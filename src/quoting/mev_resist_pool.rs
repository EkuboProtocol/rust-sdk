use crate::math::swap::{amount_before_fee, compute_fee};
use crate::math::tick::{approximate_sqrt_ratio_to_tick, FULL_RANGE_TICK_SPACING};
use crate::quoting::base_pool::{BasePool, BasePoolQuoteError, BasePoolResources, BasePoolState};
use crate::quoting::types::{BlockTimestamp, NodeKey, Pool, Quote, QuoteParams};
use core::ops::{Add, AddAssign, Sub, SubAssign};

// Resources consumed during any swap execution in a full range pool.
#[derive(Clone, Copy, Default, Debug, PartialEq, Eq)]
pub struct MEVResistPoolResources {
    pub state_update_count: u32,
    pub base_pool_resources: BasePoolResources,
}

impl AddAssign for MEVResistPoolResources {
    fn add_assign(&mut self, rhs: Self) {
        self.state_update_count += rhs.state_update_count;
        self.base_pool_resources += rhs.base_pool_resources;
    }
}

impl Add for MEVResistPoolResources {
    type Output = Self;

    fn add(mut self, rhs: Self) -> Self::Output {
        self += rhs;
        self
    }
}

impl SubAssign for MEVResistPoolResources {
    fn sub_assign(&mut self, rhs: Self) {
        self.state_update_count -= rhs.state_update_count;
        self.base_pool_resources -= rhs.base_pool_resources;
    }
}

impl Sub for MEVResistPoolResources {
    type Output = Self;

    fn sub(mut self, rhs: Self) -> Self::Output {
        self -= rhs;
        self
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct MEVResistPool {
    base_pool: BasePool,
    last_update_time: u32,
    tick: i32,
}

#[derive(Clone, Debug, PartialEq, Eq, Copy)]
pub struct MEVResistPoolState {
    pub last_update_time: u32,
    pub base_pool_state: BasePoolState,
}

/// Errors that can occur when constructing a MEVResistPool.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum MEVResistPoolError {
    FeeMustBeGreaterThanZero,
    CannotBeFullRange,
    MissingExtension,
    InvalidCurrentTick,
}

impl MEVResistPool {
    // An MEV resist pool just wraps a base pool with some additional logic
    pub fn new(
        base_pool: BasePool,
        last_update_time: u32,
        tick: i32,
    ) -> Result<Self, MEVResistPoolError> {
        let key = base_pool.get_key();
        if key.config.fee == 0 {
            return Err(MEVResistPoolError::FeeMustBeGreaterThanZero);
        }
        if key.config.tick_spacing == FULL_RANGE_TICK_SPACING {
            return Err(MEVResistPoolError::CannotBeFullRange);
        }
        if key.config.extension.is_zero() {
            return Err(MEVResistPoolError::MissingExtension);
        }

        // validates that the current tick is between the active tick and the active tick index + 1
        if let Some(i) = base_pool.get_state().active_tick_index {
            let sorted_ticks = base_pool.get_sorted_ticks();
            if let Some(t) = sorted_ticks.get(i) {
                if t.index > tick {
                    return Err(MEVResistPoolError::InvalidCurrentTick);
                }
            }
            if let Some(t) = sorted_ticks.get(i + 1) {
                if t.index <= tick {
                    return Err(MEVResistPoolError::InvalidCurrentTick);
                }
            }
        } else {
            if let Some(t) = base_pool.get_sorted_ticks().first() {
                if t.index <= tick {
                    return Err(MEVResistPoolError::InvalidCurrentTick);
                }
            }
        }

        Ok(Self {
            base_pool: base_pool,
            last_update_time,
            tick,
        })
    }
}

impl Pool for MEVResistPool {
    type Resources = MEVResistPoolResources;
    type State = MEVResistPoolState;
    type QuoteError = BasePoolQuoteError;
    type Meta = BlockTimestamp;

    fn get_key(&self) -> &NodeKey {
        self.base_pool.get_key()
    }

    fn get_state(&self) -> Self::State {
        MEVResistPoolState {
            base_pool_state: self.base_pool.get_state(),
            last_update_time: self.last_update_time,
        }
    }

    fn quote(
        &self,
        params: QuoteParams<Self::State, Self::Meta>,
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

                let pool_config = self.base_pool.get_key().config;
                let approximate_fee_multiplier = (((tick_after_swap - self.tick).abs() + 1) as f64)
                    / (pool_config.tick_spacing as f64);

                let fixed_point_additional_fee: u64 =
                    ((approximate_fee_multiplier * pool_config.fee as f64).round() as u128)
                        .min(u64::MAX as u128) as u64;

                let pool_time = params
                    .override_state
                    .map_or(self.last_update_time, |mrps| mrps.last_update_time);

                // if the time is updated, fees are accumulated to the current liquidity providers
                // this causes up to 3 additional SSTOREs (~15k gas)
                let state_update_count = if pool_time != current_time { 1 } else { 0 };

                let mut calculated_amount = quote.calculated_amount;

                if params.token_amount.amount >= 0 {
                    // exact input, remove the additional fee from the output
                    calculated_amount -= compute_fee(calculated_amount, fixed_point_additional_fee);
                } else {
                    let input_amount_fee: u128 = compute_fee(calculated_amount, pool_config.fee);
                    let input_amount = calculated_amount - input_amount_fee;

                    if let Some(bf) = amount_before_fee(input_amount, fixed_point_additional_fee) {
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
                    calculated_amount: calculated_amount,
                    consumed_amount: quote.consumed_amount,
                    execution_resources: MEVResistPoolResources {
                        state_update_count: state_update_count,
                        base_pool_resources: quote.execution_resources,
                    },
                    fees_paid: quote.fees_paid,
                    is_price_increasing: quote.is_price_increasing,
                    state_after: MEVResistPoolState {
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

#[cfg(test)]
mod tests {
    use alloc::vec;

    use crate::{
        math::{tick::to_sqrt_ratio, uint::U256},
        quoting::{
            base_pool::{BasePool, BasePoolState},
            mev_resist_pool::MEVResistPool,
            types::{Config, NodeKey, Pool, QuoteParams, Tick, TokenAmount},
        },
    };

    #[test]
    fn test_swap_input_amount_token0() {
        let liquidity: i128 = 28_898_102;
        let pool = MEVResistPool::new(
            BasePool::new(
                NodeKey {
                    token0: U256::one(),
                    token1: U256::one() + U256::one(),
                    config: Config {
                        fee: ((1_u128 << 64) / 100) as u64,
                        tick_spacing: 20_000,
                        extension: U256::one(),
                    },
                },
                BasePoolState {
                    active_tick_index: Some(0),
                    liquidity: liquidity as u128,
                    sqrt_ratio: to_sqrt_ratio(700_000).unwrap(),
                },
                vec![
                    Tick {
                        index: 600_000,
                        liquidity_delta: liquidity,
                    },
                    Tick {
                        index: 800_000,
                        liquidity_delta: -liquidity,
                    },
                ],
            )
            .unwrap(),
            1,
            700_000,
        )
        .unwrap();

        let result = pool
            .quote(QuoteParams {
                meta: 1,
                override_state: None,
                sqrt_ratio_limit: None,
                token_amount: TokenAmount {
                    amount: 100_000,
                    token: U256::one(),
                },
            })
            .unwrap();

        assert_eq!(
            (result.consumed_amount, result.calculated_amount),
            (100_000, 197_432)
        );
        assert_eq!(result.state_after.last_update_time, 1);

        // two swaps
        let mut result = pool
            .quote(QuoteParams {
                meta: 1,
                override_state: None,
                sqrt_ratio_limit: None,
                token_amount: TokenAmount {
                    amount: 300_000,
                    token: U256::one(),
                },
            })
            .unwrap();
        result = pool
            .quote(QuoteParams {
                meta: 1,
                override_state: Some(result.state_after),
                sqrt_ratio_limit: None,
                token_amount: TokenAmount {
                    amount: 300_000,
                    token: U256::one(),
                },
            })
            .unwrap();
        assert_eq!(
            (result.consumed_amount, result.calculated_amount),
            (300_000, 556_308)
        );
    }

    #[test]
    fn test_swap_output_amount_token0() {
        let liquidity: i128 = 28_898_102;
        let pool = MEVResistPool::new(
            BasePool::new(
                NodeKey {
                    token0: U256::one(),
                    token1: U256::one() + U256::one(),
                    config: Config {
                        fee: ((1_u128 << 64) / 100) as u64,
                        tick_spacing: 20_000,
                        extension: U256::one(),
                    },
                },
                BasePoolState {
                    active_tick_index: Some(0),
                    liquidity: liquidity as u128,
                    sqrt_ratio: to_sqrt_ratio(700_000).unwrap(),
                },
                vec![
                    Tick {
                        index: 600_000,
                        liquidity_delta: liquidity,
                    },
                    Tick {
                        index: 800_000,
                        liquidity_delta: -liquidity,
                    },
                ],
            )
            .unwrap(),
            1,
            700_000,
        )
        .unwrap();

        let result = pool
            .quote(QuoteParams {
                meta: 1,
                override_state: None,
                sqrt_ratio_limit: None,
                token_amount: TokenAmount {
                    amount: -100_000,
                    token: U256::one(),
                },
            })
            .unwrap();

        assert_eq!(
            (result.consumed_amount, result.calculated_amount),
            (-100_000, 205_416)
        );
        assert_eq!(result.state_after.last_update_time, 1);
    }

    #[test]
    fn test_swap_example_mainnet() {
        let liquidity: i128 = 187957823162863064741;
        let tick: i32 = 8015514;
        let fee: u64 = 9223372036854775;
        let tick_spacing: u32 = 1000;

        let pool = MEVResistPool::new(
            BasePool::new(
                NodeKey {
                    token0: U256::zero(),
                    token1: U256::one(),
                    config: Config {
                        fee: fee,
                        tick_spacing: tick_spacing,
                        extension: U256::one(),
                    },
                },
                BasePoolState {
                    active_tick_index: Some(0),
                    liquidity: liquidity as u128,
                    sqrt_ratio: U256::from_dec_str("18723430188006331344089883003460461264896")
                        .unwrap(),
                },
                vec![
                    Tick {
                        index: 7755000,
                        liquidity_delta: liquidity,
                    },
                    Tick {
                        index: 8267000,
                        liquidity_delta: -liquidity,
                    },
                ],
            )
            .unwrap(),
            1,
            tick,
        )
        .unwrap();

        let specified_amount: i128 = 1000000000000000;
        let result = pool
            .quote(QuoteParams {
                meta: 2,
                override_state: None,
                sqrt_ratio_limit: None,
                token_amount: TokenAmount {
                    amount: specified_amount,
                    token: U256::zero(),
                },
            })
            .unwrap();

        assert_eq!(
            (result.consumed_amount, result.calculated_amount),
            (specified_amount, 3024269006844199936)
        );

        let specified_amount: i128 = 5000000000000000;
        let result = pool
            .quote(QuoteParams {
                meta: 2,
                override_state: None,
                sqrt_ratio_limit: None,
                token_amount: TokenAmount {
                    amount: specified_amount,
                    token: U256::zero(),
                },
            })
            .unwrap();

        assert_eq!(
            (result.consumed_amount, result.calculated_amount),
            (specified_amount, 15086011739862955657)
        );
    }
}
