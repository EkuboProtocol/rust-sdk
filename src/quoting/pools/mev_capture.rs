use derive_more::{Add, AddAssign, Sub, SubAssign};
use num_traits::Zero;
use ruint::aliases::U256;
use thiserror::Error;

use crate::{
    chain::Chain,
    quoting::types::{BlockTimestamp, Pool, PoolConfig, PoolKey, Quote, QuoteParams},
};
use crate::{
    chain::evm::{EVM_FULL_RANGE_TICK_SPACING, Evm},
    math::swap::{amount_before_fee, compute_fee},
    private,
    quoting::pools::concentrated::{
        ConcentratedPool, ConcentratedPoolQuoteError, ConcentratedPoolResources,
        ConcentratedPoolState, ConcentratedPoolTypeConfig, TickSpacing,
    },
};
use crate::{
    math::tick::{sqrt_ratio_to_tick, to_sqrt_ratio},
    quoting::types::PoolState,
};

/// MEV-capture pool that wraps a concentrated liquidity pool with time-aware fees.
#[derive(Clone, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct MevCapturePool {
    /// Underlying concentrated liquidity pool.
    concentrated_pool: ConcentratedPool<Evm>,
    /// Last update timestamp.
    last_update_time: u32,
    /// Current tick used for fixed-point fee calculation.
    tick: i32,
}

/// Unique identifier for a [`MevCapturePool`].
pub type MevCapturePoolKey =
    PoolKey<<Evm as Chain>::Address, <Evm as Chain>::Fee, MevCapturePoolTypeConfig>;
/// Pool configuration for a [`MevCapturePool`].
pub type MevCapturePoolConfig =
    PoolConfig<<Evm as Chain>::Address, <Evm as Chain>::Fee, MevCapturePoolTypeConfig>;

/// Type config for a [`MevCapturePool`].
pub type MevCapturePoolTypeConfig = ConcentratedPoolTypeConfig;

/// State snapshot for a [`MevCapturePool`].
#[derive(Clone, Debug, PartialEq, Eq, Copy, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct MevCapturePoolState {
    /// Last update timestamp.
    pub last_update_time: u32,
    /// State of the underlying concentrated pool.
    pub concentrated_pool_state: ConcentratedPoolState,
}

/// Resources consumed during MEV-capture quote execution.
#[derive(Clone, Copy, Default, Debug, PartialEq, Eq, Hash, Add, AddAssign, Sub, SubAssign)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct MevCaptureStandalonePoolResources {
    /// Count of state updates (time syncs).
    pub state_update_count: u32,
}

/// Resources consumed during MEV-capture quote execution.
#[derive(Clone, Copy, Default, Debug, PartialEq, Eq, Hash, Add, AddAssign, Sub, SubAssign)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct MevCapturePoolResources {
    /// Resources consumed by the underlying concentrated pool.
    pub concentrated: ConcentratedPoolResources,
    /// Resources added by the MEV-capture wrapper.
    pub mev_capture: MevCaptureStandalonePoolResources,
}

/// Errors that can occur when constructing a [`MevCapturePool`].
#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, Error)]
pub enum MevCapturePoolConstructionError {
    #[error("fee must be non-zero")]
    FeeMustBeGreaterThanZero,
    #[error("underlying pool must not be full range")]
    CannotBeFullRange,
    #[error("extension must be non-zero")]
    MissingExtension,
    #[error("current tick is invalid")]
    InvalidCurrentTick,
}

impl MevCapturePool {
    // An MEV resist pool just wraps a concentrated pool with some additional logic
    pub fn new(
        concentrated_pool: ConcentratedPool<Evm>,
        last_update_time: u32,
        tick: i32,
    ) -> Result<Self, MevCapturePoolConstructionError> {
        let PoolConfig {
            fee,
            pool_type_config: TickSpacing(tick_spacing),
            extension,
        } = concentrated_pool.key().config;

        if fee.is_zero() {
            return Err(MevCapturePoolConstructionError::FeeMustBeGreaterThanZero);
        }
        if tick_spacing == EVM_FULL_RANGE_TICK_SPACING {
            return Err(MevCapturePoolConstructionError::CannotBeFullRange);
        }
        if extension.is_zero() {
            return Err(MevCapturePoolConstructionError::MissingExtension);
        }

        // validates that the current tick is between the active tick and the active tick index + 1
        if let Some(i) = concentrated_pool.state().active_tick_index {
            let sorted_ticks = concentrated_pool.ticks();
            if let Some(t) = sorted_ticks.get(i)
                && t.index > tick
            {
                return Err(MevCapturePoolConstructionError::InvalidCurrentTick);
            }
            if let Some(t) = sorted_ticks.get(i + 1)
                && t.index <= tick
            {
                return Err(MevCapturePoolConstructionError::InvalidCurrentTick);
            }
        } else if let Some(t) = concentrated_pool.ticks().first()
            && t.index <= tick
        {
            return Err(MevCapturePoolConstructionError::InvalidCurrentTick);
        }

        Ok(Self {
            concentrated_pool,
            last_update_time,
            tick,
        })
    }

    pub fn concentrated_pool(&self) -> &ConcentratedPool<Evm> {
        &self.concentrated_pool
    }

    /// Returns the tick Core stores for a swap ending at `sqrt_ratio`.
    ///
    /// Core stores the floor tick of the price, except that a decreasing swap which stops on the
    /// tick it was swapping towards leaves the pool at that tick minus one. For concentrated
    /// pools that happens at initialized ticks and at the minimum tick. Core also stops on
    /// uninitialized ticks at the edge of each searched tick bitmap word, which depends on the
    /// swap's `skipAhead`; a swap only ends exactly on one of those if its sqrt ratio limit is
    /// that tick's price, which this does not model.
    fn tick_after_swap(&self, sqrt_ratio: U256, is_price_increasing: bool) -> i32 {
        let tick = sqrt_ratio_to_tick::<Evm>(sqrt_ratio);

        let stopped_on_crossed_tick = !is_price_increasing
            && to_sqrt_ratio::<Evm>(tick) == Some(sqrt_ratio)
            && (tick == Evm::min_tick()
                || self
                    .concentrated_pool
                    .ticks()
                    .binary_search_by_key(&tick, |t| t.index)
                    .is_ok());

        tick - i32::from(stopped_on_crossed_tick)
    }
}

/// Core's additional fee for a swap that moved the pool by `tick_delta` ticks.
fn additional_fee(tick_delta: u32, tick_spacing: u32, fee: u64) -> u64 {
    let fee_multiplier_x64 = (U256::from(tick_delta) << 64) / U256::from(tick_spacing);

    let fee: U256 = (fee_multiplier_x64 * U256::from(fee)) >> 64;

    fee.min(U256::from(u64::MAX)).to()
}

impl AsRef<ConcentratedPool<Evm>> for MevCapturePool {
    fn as_ref(&self) -> &ConcentratedPool<Evm> {
        self.concentrated_pool()
    }
}

impl AsRef<Self> for MevCapturePool {
    fn as_ref(&self) -> &Self {
        self
    }
}

impl Pool for MevCapturePool {
    type Address = <Evm as Chain>::Address;
    type Fee = <Evm as Chain>::Fee;
    type Resources = MevCapturePoolResources;
    type State = MevCapturePoolState;
    type QuoteError = ConcentratedPoolQuoteError;
    type Meta = BlockTimestamp;
    type PoolTypeConfig = MevCapturePoolTypeConfig;

    fn key(&self) -> MevCapturePoolKey {
        self.concentrated_pool.key()
    }

    fn state(&self) -> Self::State {
        MevCapturePoolState {
            concentrated_pool_state: self.concentrated_pool.state(),
            last_update_time: self.last_update_time,
        }
    }

    fn quote(
        &self,
        params: QuoteParams<Self::Address, Self::State, Self::Meta>,
    ) -> Result<Quote<Self::Resources, Self::State>, Self::QuoteError> {
        match self.concentrated_pool.quote(QuoteParams {
            token_amount: params.token_amount,
            sqrt_ratio_limit: params.sqrt_ratio_limit,
            override_state: params.override_state.map(|o| o.concentrated_pool_state),
            meta: (),
        }) {
            Ok(quote) => {
                let current_time = (params.meta & 0xFFFFFFFF) as u32;

                let tick_after_swap =
                    self.tick_after_swap(quote.state_after.sqrt_ratio, quote.is_price_increasing);

                let pool_config = self.concentrated_pool.key().config;
                let fixed_point_additional_fee = additional_fee(
                    tick_after_swap.abs_diff(self.tick),
                    pool_config.pool_type_config.0,
                    pool_config.fee,
                );

                let pool_time = params
                    .override_state
                    .map_or(self.last_update_time, |mrps| mrps.last_update_time);

                // if the time is updated, fees are accumulated to the current liquidity providers
                // this causes up to 3 additional SSTOREs (~15k gas)
                let state_update_count = u32::from(pool_time != current_time);

                let mut calculated_amount = quote.calculated_amount;

                if params.token_amount.amount >= 0 {
                    // exact input, remove the additional fee from the output
                    calculated_amount -=
                        compute_fee::<Evm>(calculated_amount, fixed_point_additional_fee);
                } else {
                    let input_amount_fee: u128 =
                        compute_fee::<Evm>(calculated_amount, pool_config.fee);
                    let input_amount = calculated_amount - input_amount_fee;

                    if let Some(bf) =
                        amount_before_fee::<Evm>(input_amount, fixed_point_additional_fee)
                    {
                        let fee = bf - input_amount;
                        // exact output, compute the additional fee for the output
                        calculated_amount += fee;
                    } else {
                        return Err(ConcentratedPoolQuoteError::FailedComputeSwapStep(
                            crate::math::swap::ComputeStepError::AmountBeforeFeeOverflow,
                        ));
                    }
                }

                Ok(Quote {
                    calculated_amount,
                    consumed_amount: quote.consumed_amount,
                    execution_resources: MevCapturePoolResources {
                        concentrated: quote.execution_resources,
                        mev_capture: MevCaptureStandalonePoolResources { state_update_count },
                    },
                    fees_paid: quote.fees_paid,
                    is_price_increasing: quote.is_price_increasing,
                    state_after: MevCapturePoolState {
                        last_update_time: current_time,
                        concentrated_pool_state: quote.state_after,
                    },
                })
            }
            Err(err) => Err(err),
        }
    }

    fn has_liquidity(&self) -> bool {
        self.concentrated_pool.has_liquidity()
    }

    fn max_tick_with_liquidity(&self) -> Option<i32> {
        self.concentrated_pool.max_tick_with_liquidity()
    }

    fn min_tick_with_liquidity(&self) -> Option<i32> {
        self.concentrated_pool.min_tick_with_liquidity()
    }

    fn is_path_dependent(&self) -> bool {
        true
    }
}

impl PoolState for MevCapturePoolState {
    fn sqrt_ratio(&self) -> U256 {
        self.concentrated_pool_state.sqrt_ratio()
    }

    fn liquidity(&self) -> u128 {
        self.concentrated_pool_state.liquidity()
    }
}

impl private::Sealed for MevCapturePoolState {}
impl private::Sealed for MevCapturePool {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::alloy_primitives::Address;
    use crate::{
        chain::tests::ChainTest,
        math::tick::to_sqrt_ratio,
        quoting::types::{Pool, PoolConfig, PoolKey, QuoteParams, Tick, TokenAmount},
    };
    use alloc::vec::Vec;
    use ruint::uint;

    const DEFAULT_FEE: u64 = ((1u128 << 64) / 100) as u64;
    const DEFAULT_TICK_SPACING: u32 = 20_000;

    fn ticks(entries: &[(i32, i128)]) -> Vec<Tick> {
        entries
            .iter()
            .map(|(index, delta)| Tick {
                index: *index,
                liquidity_delta: *delta,
            })
            .collect()
    }

    fn build_pool(
        token0: Address,
        token1: Address,
        fee: u64,
        tick_spacing: u32,
        sqrt_ratio: U256,
        liquidity: i128,
        last_update_time: u32,
        tick: i32,
        tick_entries: &[(i32, i128)],
    ) -> MevCapturePool {
        MevCapturePool::new(
            ConcentratedPool::new(
                PoolKey {
                    token0,
                    token1,
                    config: PoolConfig {
                        fee,
                        pool_type_config: TickSpacing(tick_spacing),
                        extension: Evm::one_address(),
                    },
                },
                ConcentratedPoolState {
                    active_tick_index: Some(0),
                    liquidity: liquidity as u128,
                    sqrt_ratio,
                },
                ticks(tick_entries),
            )
            .unwrap(),
            last_update_time,
            tick,
        )
        .unwrap()
    }

    fn default_pool(liquidity: i128, sqrt_ratio: U256, tick: i32) -> MevCapturePool {
        build_pool(
            Evm::zero_address(),
            Evm::one_address(),
            DEFAULT_FEE,
            DEFAULT_TICK_SPACING,
            sqrt_ratio,
            liquidity,
            1,
            tick,
            &[(600_000, liquidity), (800_000, -liquidity)],
        )
    }

    #[test]
    fn swap_input_amount_token0() {
        let liquidity = 28_898_102;
        let pool = default_pool(liquidity, to_sqrt_ratio::<Evm>(700_000).unwrap(), 700_000);

        let quote = pool
            .quote(QuoteParams {
                meta: 1,
                override_state: None,
                sqrt_ratio_limit: None,
                token_amount: TokenAmount {
                    amount: 100_000,
                    token: Evm::zero_address(),
                },
            })
            .unwrap();

        assert_eq!(
            (
                quote.consumed_amount,
                quote.calculated_amount,
                quote.state_after.last_update_time
            ),
            (100_000, 197_432, 1)
        );

        let first = pool
            .quote(QuoteParams {
                meta: 1,
                override_state: None,
                sqrt_ratio_limit: None,
                token_amount: TokenAmount {
                    amount: 300_000,
                    token: Evm::zero_address(),
                },
            })
            .unwrap();
        let second = pool
            .quote(QuoteParams {
                meta: 1,
                override_state: Some(first.state_after),
                sqrt_ratio_limit: None,
                token_amount: TokenAmount {
                    amount: 300_000,
                    token: Evm::zero_address(),
                },
            })
            .unwrap();

        assert_eq!(
            (second.consumed_amount, second.calculated_amount),
            (300_000, 556_308)
        );
    }

    #[test]
    fn swap_output_amount_token0() {
        let liquidity = 28_898_102;
        let pool = default_pool(liquidity, to_sqrt_ratio::<Evm>(700_000).unwrap(), 700_000);

        let quote = pool
            .quote(QuoteParams {
                meta: 1,
                override_state: None,
                sqrt_ratio_limit: None,
                token_amount: TokenAmount {
                    amount: -100_000,
                    token: Evm::zero_address(),
                },
            })
            .unwrap();

        assert_eq!(
            (
                quote.consumed_amount,
                quote.calculated_amount,
                quote.state_after.last_update_time
            ),
            (-100_000, 205_416, 1)
        );
    }

    #[test]
    fn swap_example_mainnet() {
        let liquidity = 187_957_823_162_863_064_741;
        let fee = 9_223_372_036_854_775;
        let tick_spacing = 1_000;
        let tick = 8_015_514;

        let pool = build_pool(
            Evm::zero_address(),
            Evm::one_address(),
            fee,
            tick_spacing,
            uint!(18723430188006331344089883003460461264896_U256),
            liquidity,
            1,
            tick,
            &[(7_755_000, liquidity), (8_267_000, -liquidity)],
        );

        for (amount, expected) in [
            (1_000_000_000_000_000, 3_024_270_519_421_888_604),
            (5_000_000_000_000_000, 15_086_011_739_862_955_627),
        ] {
            let quote = pool
                .quote(QuoteParams {
                    meta: 2,
                    override_state: None,
                    sqrt_ratio_limit: None,
                    token_amount: TokenAmount {
                        amount,
                        token: Evm::zero_address(),
                    },
                })
                .unwrap();

            assert_eq!(
                (quote.consumed_amount, quote.calculated_amount),
                (amount, expected)
            );
        }
    }

    // The first swap crosses the empty tick bitmap word starting at tick 8,065,000. `Core` gives
    // these amounts with `skipAhead` 2; with `skipAhead` 0 it takes an extra swap step at that
    // word boundary and rounds differently by a few thousand wei.
    #[test]
    fn swap_example_mainnet_split_trade() {
        let liquidity = 187_957_823_162_863_064_741;
        let fee = 9_223_372_036_854_775;
        let tick_spacing = 1_000;
        let tick = 8_092_285;

        let pool = build_pool(
            Evm::zero_address(),
            Evm::one_address(),
            fee,
            tick_spacing,
            uint!(19456111242847136401729567804224169836544_U256),
            liquidity,
            1,
            tick,
            &[(7_755_000, liquidity), (8_267_000, -liquidity)],
        );

        let sqrt_ratio_limit = Some(uint!(18447191164202170524_U256));

        let result0 = pool
            .quote(QuoteParams {
                meta: 2,
                override_state: None,
                sqrt_ratio_limit,
                token_amount: TokenAmount {
                    amount: 125_000_000_000_000_000,
                    token: Evm::zero_address(),
                },
            })
            .unwrap();

        assert_eq!(
            (result0.consumed_amount, result0.calculated_amount),
            (125_000_000_000_000_000, 378_805_738_986_174_443_017)
        );

        let result1 = pool
            .quote(QuoteParams {
                meta: 2,
                override_state: Some(result0.state_after),
                sqrt_ratio_limit,
                token_amount: TokenAmount {
                    amount: 50_000_000_000_000_000,
                    token: Evm::zero_address(),
                },
            })
            .unwrap();

        assert_eq!(
            (result1.consumed_amount, result1.calculated_amount),
            (50_000_000_000_000_000, 141_694_588_268_248_472_002)
        );

        let result2 = pool
            .quote(QuoteParams {
                meta: 2,
                override_state: Some(result1.state_after),
                sqrt_ratio_limit,
                token_amount: TokenAmount {
                    amount: 12_500_000_000_000_000,
                    token: Evm::zero_address(),
                },
            })
            .unwrap();

        assert_eq!(
            (result2.consumed_amount, result2.calculated_amount),
            (12_500_000_000_000_000, 34_654_649_033_984_065_649)
        );

        let result3 = pool
            .quote(QuoteParams {
                meta: 2,
                override_state: Some(result2.state_after),
                sqrt_ratio_limit,
                token_amount: TokenAmount {
                    amount: 12_500_000_000_000_000,
                    token: Evm::zero_address(),
                },
            })
            .unwrap();

        assert_eq!(
            (result3.consumed_amount, result3.calculated_amount),
            (12_500_000_000_000_000, 34_275_601_333_991_479_698)
        );
    }

    /// A pool with the positions the Foundry parity scenarios create on `Core`.
    fn core_parity_pool(
        fee: u64,
        tick_spacing: u32,
        liquidity: u128,
        positions: [(i32, i128); 2],
    ) -> MevCapturePool {
        let [(outer, outer_liquidity), (inner, inner_liquidity)] = positions;

        MevCapturePool::new(
            ConcentratedPool::new(
                PoolKey {
                    token0: Evm::zero_address(),
                    token1: Evm::one_address(),
                    config: PoolConfig {
                        fee,
                        pool_type_config: TickSpacing(tick_spacing),
                        extension: Evm::one_address(),
                    },
                },
                ConcentratedPoolState {
                    active_tick_index: Some(1),
                    liquidity,
                    sqrt_ratio: to_sqrt_ratio::<Evm>(0).unwrap(),
                },
                ticks(&[
                    (-outer, outer_liquidity),
                    (-inner, inner_liquidity),
                    (inner, -inner_liquidity),
                    (outer, -outer_liquidity),
                ]),
            )
            .unwrap(),
            0,
            0,
        )
        .unwrap()
    }

    /// Quotes each swap in sequence, as `Core` would execute them within one block, and checks the
    /// consumed and calculated amounts.
    fn assert_quotes(pool: &MevCapturePool, swaps: &[(bool, i128, Option<i32>, i128, u128)]) {
        let mut state = None;

        for &(is_token1, amount, limit_tick, consumed, calculated) in swaps {
            let quote = pool
                .quote(QuoteParams {
                    meta: 1,
                    override_state: state,
                    sqrt_ratio_limit: limit_tick.map(|tick| to_sqrt_ratio::<Evm>(tick).unwrap()),
                    token_amount: TokenAmount {
                        amount,
                        token: if is_token1 {
                            Evm::one_address()
                        } else {
                            Evm::zero_address()
                        },
                    },
                })
                .unwrap();

            assert_eq!(
                (quote.consumed_amount, quote.calculated_amount),
                (consumed, calculated)
            );

            state = Some(quote.state_after);
        }
    }

    // Expected amounts are the results of the same swaps through `MEVCapture` on `Core` in Foundry
    mod matches_core {
        use super::*;

        fn wide_spacing_pool() -> MevCapturePool {
            core_parity_pool(
                DEFAULT_FEE,
                DEFAULT_TICK_SPACING,
                121_005_059,
                [(100_000, 20_504_176), (20_000, 100_500_883)],
            )
        }

        fn low_fee_pool() -> MevCapturePool {
            core_parity_pool(
                ((1u128 << 64) / 10_000) as u64,
                100,
                2_201_001_558_332_747_049_219_572_744,
                [
                    (10_000, 200_500_516_666_268_056_066_533_655),
                    (1_000, 2_000_501_041_666_478_993_153_039_089),
                ],
            )
        }

        #[test]
        fn exact_input() {
            assert_quotes(
                &wide_spacing_pool(),
                &[(false, 500_000, None, 500_000, 490_970)],
            );
            assert_quotes(
                &wide_spacing_pool(),
                &[(true, 500_000, None, 500_000, 490_970)],
            );
            assert_quotes(
                &low_fee_pool(),
                &[(
                    false,
                    400_000_000_000_000_000_000_000,
                    None,
                    400_000_000_000_000_000_000_000,
                    399_741_774_575_010_561_642_568,
                )],
            );
            assert_quotes(
                &low_fee_pool(),
                &[(
                    true,
                    400_000_000_000_000_000_000_000,
                    None,
                    400_000_000_000_000_000_000_000,
                    399_742_174_462_343_990_786_130,
                )],
            );
        }

        #[test]
        fn exact_output() {
            assert_quotes(
                &wide_spacing_pool(),
                &[(false, -300_000, None, -300_000, 304_533)],
            );
            assert_quotes(
                &wide_spacing_pool(),
                &[(true, -300_000, None, -300_000, 304_533)],
            );
            assert_quotes(
                &low_fee_pool(),
                &[(
                    false,
                    -300_000_000_000_000_000_000_000,
                    None,
                    -300_000_000_000_000_000_000_000,
                    300_152_536_467_866_436_260_590,
                )],
            );
            assert_quotes(
                &low_fee_pool(),
                &[(
                    true,
                    -300_000_000_000_000_000_000_000,
                    None,
                    -300_000_000_000_000_000_000_000,
                    300_152_836_672_351_544_524_094,
                )],
            );
        }

        #[test]
        fn crossing_initialized_ticks() {
            assert_quotes(
                &low_fee_pool(),
                &[(
                    false,
                    2_000_000_000_000_000_000_000_000,
                    None,
                    2_000_000_000_000_000_000_000_000,
                    1_974_512_281_141_026_964_903_651,
                )],
            );
            assert_quotes(
                &low_fee_pool(),
                &[(
                    true,
                    -1_500_000_000_000_000_000_000_000,
                    None,
                    -1_500_000_000_000_000_000_000_000,
                    1_509_437_693_364_358_517_459_459,
                )],
            );
        }

        // `Core` leaves the pool one tick below an initialized tick that a decreasing swap stops
        // on, which moves the pool one tick further for the additional fee
        #[test]
        fn stopping_on_initialized_tick() {
            assert_quotes(
                &wide_spacing_pool(),
                &[(false, 10_000_000, Some(-20_000), 1_228_406, 1_191_978)],
            );
            assert_quotes(
                &wide_spacing_pool(),
                &[(true, 10_000_000, Some(20_000), 1_228_406, 1_191_978)],
            );
            assert_quotes(
                &low_fee_pool(),
                &[(
                    false,
                    5_000_000_000_000_000_000_000_000,
                    Some(-1_000),
                    1_100_885_488_244_704_583_342_630,
                    1_099_123_824_470_088_356_129_274,
                )],
            );
        }

        #[test]
        fn swaps_in_same_block() {
            assert_quotes(
                &wide_spacing_pool(),
                &[
                    (false, 200_000, None, 200_000, 197_352),
                    (false, 200_000, None, 200_000, 196_386),
                ],
            );
            assert_quotes(
                &wide_spacing_pool(),
                &[
                    (false, 300_000, None, 300_000, 295_545),
                    (true, 400_000, None, 400_000, 396_318),
                ],
            );
        }
    }
}
