use derive_more::{Add, AddAssign, Sub, SubAssign};
use num_traits::Zero;
use ruint::aliases::U256;
use thiserror::Error;

use crate::{
    chain::evm::{Evm, EVM_FULL_RANGE_TICK_SPACING},
    math::{
        facade::round_f64,
        swap::{amount_before_fee, compute_fee},
    },
    private,
    quoting::pools::base::{
        BasePool, BasePoolQuoteError, BasePoolResources, BasePoolState, BasePoolTypeConfig,
        TickSpacing,
    },
};
use crate::{
    chain::Chain,
    quoting::types::{BlockTimestamp, Pool, PoolConfig, PoolKey, Quote, QuoteParams},
};
use crate::{math::tick::approximate_sqrt_ratio_to_tick, quoting::types::PoolState};

/// MEV-capture pool that wraps a concentrated liquidity pool with time-aware fees.
#[derive(Clone, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct MevCapturePool {
    /// Underlying concentrated liquidity pool.
    base_pool: BasePool<Evm>,
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
pub type MevCapturePoolTypeConfig = BasePoolTypeConfig;

/// State snapshot for a [`MevCapturePool`].
#[derive(Clone, Debug, PartialEq, Eq, Copy, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct MevCapturePoolState {
    /// Last update timestamp.
    pub last_update_time: u32,
    /// State of the underlying base pool.
    pub base_pool_state: BasePoolState,
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
    /// Resources consumed by the underlying base pool.
    pub base: BasePoolResources,
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
    // An MEV resist pool just wraps a base pool with some additional logic
    pub fn new(
        base_pool: BasePool<Evm>,
        last_update_time: u32,
        tick: i32,
    ) -> Result<Self, MevCapturePoolConstructionError> {
        let PoolConfig {
            fee,
            pool_type_config: TickSpacing(tick_spacing),
            extension,
        } = base_pool.key().config;

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
        if let Some(i) = base_pool.state().active_tick_index {
            let sorted_ticks = base_pool.ticks();
            if let Some(t) = sorted_ticks.get(i) {
                if t.index > tick {
                    return Err(MevCapturePoolConstructionError::InvalidCurrentTick);
                }
            }
            if let Some(t) = sorted_ticks.get(i + 1) {
                if t.index <= tick {
                    return Err(MevCapturePoolConstructionError::InvalidCurrentTick);
                }
            }
        } else if let Some(t) = base_pool.ticks().first() {
            if t.index <= tick {
                return Err(MevCapturePoolConstructionError::InvalidCurrentTick);
            }
        }

        Ok(Self {
            base_pool,
            last_update_time,
            tick,
        })
    }
}

impl Pool for MevCapturePool {
    type Address = <Evm as Chain>::Address;
    type Fee = <Evm as Chain>::Fee;
    type Resources = MevCapturePoolResources;
    type State = MevCapturePoolState;
    type QuoteError = BasePoolQuoteError;
    type Meta = BlockTimestamp;
    type PoolTypeConfig = MevCapturePoolTypeConfig;

    fn key(&self) -> MevCapturePoolKey {
        self.base_pool.key()
    }

    fn state(&self) -> Self::State {
        MevCapturePoolState {
            base_pool_state: self.base_pool.state(),
            last_update_time: self.last_update_time,
        }
    }

    fn quote(
        &self,
        params: QuoteParams<Self::Address, Self::State, Self::Meta>,
    ) -> Result<Quote<Self::Resources, Self::State>, Self::QuoteError> {
        match self.base_pool.quote(QuoteParams {
            token_amount: params.token_amount,
            sqrt_ratio_limit: params.sqrt_ratio_limit,
            override_state: params.override_state.map(|o| o.base_pool_state),
            meta: (),
        }) {
            Ok(quote) => {
                let current_time = (params.meta & 0xFFFFFFFF) as u32;

                let tick_after_swap = approximate_sqrt_ratio_to_tick(quote.state_after.sqrt_ratio);

                let pool_config = self.base_pool.key().config;
                let approximate_fee_multiplier = f64::from((tick_after_swap - self.tick).abs() + 1)
                    / f64::from(pool_config.pool_type_config.0);

                let fixed_point_additional_fee: u64 =
                    (round_f64(approximate_fee_multiplier * pool_config.fee as f64) as u128)
                        .min(u128::from(u64::MAX)) as u64;

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
                        return Err(BasePoolQuoteError::FailedComputeSwapStep(
                            crate::math::swap::ComputeStepError::AmountBeforeFeeOverflow,
                        ));
                    }
                }

                Ok(Quote {
                    calculated_amount,
                    consumed_amount: quote.consumed_amount,
                    execution_resources: MevCapturePoolResources {
                        base: quote.execution_resources,
                        mev_capture: MevCaptureStandalonePoolResources { state_update_count },
                    },
                    fees_paid: quote.fees_paid,
                    is_price_increasing: quote.is_price_increasing,
                    state_after: MevCapturePoolState {
                        last_update_time: current_time,
                        base_pool_state: quote.state_after,
                    },
                })
            }
            Err(err) => Err(err),
        }
    }

    fn has_liquidity(&self) -> bool {
        self.base_pool.has_liquidity()
    }

    fn max_tick_with_liquidity(&self) -> Option<i32> {
        self.base_pool.max_tick_with_liquidity()
    }

    fn min_tick_with_liquidity(&self) -> Option<i32> {
        self.base_pool.min_tick_with_liquidity()
    }

    fn is_path_dependent(&self) -> bool {
        true
    }
}

impl PoolState for MevCapturePoolState {
    fn sqrt_ratio(&self) -> U256 {
        self.base_pool_state.sqrt_ratio()
    }

    fn liquidity(&self) -> u128 {
        self.base_pool_state.liquidity()
    }
}

impl private::Sealed for MevCapturePoolState {}
impl private::Sealed for MevCapturePool {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        chain::tests::ChainTest,
        math::tick::to_sqrt_ratio,
        quoting::types::{Pool, PoolConfig, PoolKey, QuoteParams, Tick, TokenAmount},
    };
    use alloc::vec::Vec;
    use crate::alloy_primitives::Address;
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
            BasePool::new(
                PoolKey {
                    token0,
                    token1,
                    config: PoolConfig {
                        fee,
                        pool_type_config: TickSpacing(tick_spacing),
                        extension: Evm::one_address(),
                    },
                },
                BasePoolState {
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
            (1_000_000_000_000_000, 3_024_269_006_844_199_936),
            (5_000_000_000_000_000, 15_086_011_739_862_955_657),
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
            (125_000_000_000_000_000, 378_805_738_986_174_441_222)
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
            (50_000_000_000_000_000, 141_694_588_268_248_470_538)
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
            (12_500_000_000_000_000, 34_654_649_033_984_065_500)
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
            (12_500_000_000_000_000, 34_275_601_333_991_479_466)
        );
    }
}
