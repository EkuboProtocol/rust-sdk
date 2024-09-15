use crate::math::swap::{compute_step, is_price_increasing, ComputeStepError};
use crate::math::tick::{to_sqrt_ratio, MAX_SQRT_RATIO, MIN_SQRT_RATIO};
use crate::math::uint::U256;
use crate::quoting::types::{NodeKey, Pool, Quote, QuoteParams, Tick};
use crate::quoting::util::approximate_number_of_tick_spacings_crossed;
use alloc::vec::Vec;
use core::ops::Add;
use num_traits::Zero;

// Resources consumed during any swap execution.
#[derive(Clone, Copy, Default)]
pub struct BasePoolResources {
    pub initialized_ticks_crossed: u32,
    pub tick_spacings_crossed: u32,
}

impl Add for BasePoolResources {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        BasePoolResources {
            initialized_ticks_crossed: self.initialized_ticks_crossed
                + rhs.initialized_ticks_crossed,
            tick_spacings_crossed: self.tick_spacings_crossed + rhs.tick_spacings_crossed,
        }
    }
}

pub const MAX_TICK_SPACING: u32 = 354892;
pub const MIN_TICK_AT_MAX_TICK_SPACING: i32 = -88368108;
pub const MAX_TICK_AT_MAX_TICK_SPACING: i32 = 88368108;
pub const MIN_SQRT_RATIO_AT_MAX_TICK_SPACING: U256 = U256([3580400339970425059, 1, 0, 0]);
pub const MAX_SQRT_RATIO_AT_MAX_TICK_SPACING: U256 = U256([
    6538062197914670769,
    14200015713685041661,
    15448319606494512814,
    0,
]);

#[derive(Debug, PartialEq)]
pub enum BasePoolQuoteError {
    InvalidToken,
    InvalidSqrtRatioLimit,
    InvalidTick(i32),
    FailedComputeSwapStep(ComputeStepError),
}

#[derive(Clone, Copy)]
pub struct BasePoolState {
    pub sqrt_ratio: U256,
    pub liquidity: u128,
    pub active_tick_index: Option<usize>,
}

pub struct BasePool {
    key: NodeKey,
    state: BasePoolState,
    sorted_ticks: Vec<Tick>,
}

impl BasePool {
    pub fn new(key: NodeKey, state: BasePoolState, sorted_ticks: Vec<Tick>) -> Self {
        assert!(key.token0 < key.token1, "token0 must be less than token1");
        assert!(!key.token0.is_zero(), "token0 must be non-zero");
        assert!(
            key.tick_spacing <= MAX_TICK_SPACING,
            "tick spacing must be less than max tick spacing"
        );
        assert!(
            key.tick_spacing > 0,
            "tick spacing must be greater than zero"
        );
        if let Some(active) = state.active_tick_index {
            let tick = sorted_ticks
                .get(active)
                .expect("active tick index is out of bounds");

            assert!(
                to_sqrt_ratio(tick.index).expect("invalid active tick") <= state.sqrt_ratio,
                "sqrt_ratio of active tick is not less than or equal to current sqrt_ratio"
            );
        } else {
            if let Some(first) = sorted_ticks.first() {
                assert!(
                    state.sqrt_ratio
                        <= to_sqrt_ratio(first.index).expect("first tick has invalid index"),
                    "sqrt ratio must be less than or equal to first tick"
                );
            }
        }

        // check ticks are sorted in linear time
        let mut last_tick: Option<i32> = None;
        for tick in sorted_ticks.iter() {
            if let Some(last) = last_tick {
                assert!(tick.index > last, "ticks must be sorted");
            };
            last_tick = Some(tick.index);
        }

        Self {
            key,
            state,
            sorted_ticks,
        }
    }
}

impl Pool for BasePool {
    type Resources = BasePoolResources;
    type State = BasePoolState;
    type QuoteError = BasePoolQuoteError;

    fn get_key(&self) -> NodeKey {
        self.key
    }

    fn get_state(&self) -> Self::State {
        self.state
    }

    fn quote(
        &self,
        params: QuoteParams<Self::State>,
    ) -> Result<Quote<Self::Resources, Self::State>, Self::QuoteError> {
        let amount = params.token_amount.amount;
        let token = params.token_amount.token;
        let is_token1 = token == self.key.token1;

        if !is_token1 && token != self.key.token0 {
            return Err(BasePoolQuoteError::InvalidToken);
        }

        let state = if let Some(override_state) = params.override_state {
            override_state
        } else {
            self.state.clone()
        };

        if amount == 0 {
            return Ok(Quote {
                is_price_increasing: is_token1,
                consumed_amount: 0,
                calculated_amount: 0,
                execution_resources: Default::default(),
                state_after: state,
                fees_paid: 0,
            });
        }

        let is_increasing = is_price_increasing(amount, is_token1);

        let mut sqrt_ratio = state.sqrt_ratio;
        let mut liquidity = state.liquidity;
        let mut active_tick_index = state.active_tick_index;

        let sqrt_ratio_limit = if let Some(limit) = params.sqrt_ratio_limit {
            if is_increasing && limit < sqrt_ratio {
                return Err(BasePoolQuoteError::InvalidSqrtRatioLimit);
            }
            if !is_increasing && limit > sqrt_ratio {
                return Err(BasePoolQuoteError::InvalidSqrtRatioLimit);
            }
            if limit < MIN_SQRT_RATIO {
                return Err(BasePoolQuoteError::InvalidSqrtRatioLimit);
            }
            if limit > MAX_SQRT_RATIO {
                return Err(BasePoolQuoteError::InvalidSqrtRatioLimit);
            }
            limit
        } else {
            if is_increasing {
                MAX_SQRT_RATIO
            } else {
                MIN_SQRT_RATIO
            }
        };

        let mut calculated_amount: i128 = 0;
        let mut fees_paid: u128 = 0;
        let mut initialized_ticks_crossed: u32 = 0;
        let mut amount_remaining = amount;

        let starting_sqrt_ratio = sqrt_ratio;

        while amount_remaining != 0 && sqrt_ratio != sqrt_ratio_limit {
            let next_initialized_tick: Option<(usize, &Tick, U256)> = if is_increasing {
                if let Some(index) = active_tick_index {
                    if let Some(next) = self.sorted_ticks.get(index + 1) {
                        Some((
                            index + 1,
                            next,
                            to_sqrt_ratio(next.index)
                                .ok_or(BasePoolQuoteError::InvalidTick(next.index))?,
                        ))
                    } else {
                        None
                    }
                } else {
                    if let Some(next) = self.sorted_ticks.first() {
                        Some((
                            0,
                            next,
                            to_sqrt_ratio(next.index)
                                .ok_or(BasePoolQuoteError::InvalidTick(next.index))?,
                        ))
                    } else {
                        None
                    }
                }
            } else {
                if let Some(index) = active_tick_index {
                    if let Some(tick) = self.sorted_ticks.get(index) {
                        Some((
                            index,
                            tick,
                            to_sqrt_ratio(tick.index)
                                .ok_or(BasePoolQuoteError::InvalidTick(tick.index))?,
                        ))
                    } else {
                        None
                    }
                } else {
                    None
                }
            };

            let step_sqrt_ratio_limit =
                next_initialized_tick.map_or(sqrt_ratio_limit, |(_, _, next_ratio)| {
                    if (next_ratio < sqrt_ratio_limit) == is_increasing {
                        next_ratio
                    } else {
                        sqrt_ratio_limit
                    }
                });

            let step = compute_step(
                sqrt_ratio,
                liquidity,
                step_sqrt_ratio_limit,
                amount,
                is_token1,
                self.key.fee,
            )
            .map_err(BasePoolQuoteError::FailedComputeSwapStep)?;

            amount_remaining -= step.consumed_amount;
            calculated_amount += step.calculated_amount;
            fees_paid += step.fee_amount;
            sqrt_ratio = step.sqrt_ratio_next;

            if let Some((index, next_tick, tick_sqrt_ratio)) = next_initialized_tick {
                if sqrt_ratio == tick_sqrt_ratio {
                    active_tick_index = if is_increasing {
                        Some(index)
                    } else if !index.is_zero() {
                        Some(index - 1)
                    } else {
                        None
                    };

                    initialized_ticks_crossed += 1;

                    if (next_tick.liquidity_delta.signum() == 1) == is_increasing {
                        liquidity = liquidity + next_tick.liquidity_delta.unsigned_abs();
                    } else {
                        liquidity = liquidity - next_tick.liquidity_delta.unsigned_abs();
                    };
                }
            } else {
                active_tick_index = None
            }
        }

        let resources = BasePoolResources {
            initialized_ticks_crossed,
            tick_spacings_crossed: approximate_number_of_tick_spacings_crossed(
                starting_sqrt_ratio,
                sqrt_ratio,
                self.key.tick_spacing,
            ),
        };

        let state_after = BasePoolState {
            sqrt_ratio,
            liquidity,
            active_tick_index,
        };

        Ok(Quote {
            is_price_increasing: is_increasing,
            consumed_amount: amount - amount_remaining,
            calculated_amount,
            execution_resources: resources,
            state_after,
            fees_paid,
        })
    }

    // Checks if the pool has any liquidity.
    fn has_liquidity(&self) -> bool {
        self.state.liquidity > 0 || !self.sorted_ticks.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::quoting::types::{Block, QuoteMeta, TokenAmount};
    use alloc::vec;

    const TOKEN0: U256 = U256([1, 0, 0, 0]);
    const TOKEN1: U256 = U256([2, 0, 0, 0]);

    fn node_key(tick_spacing: u32, fee: u128) -> NodeKey {
        NodeKey {
            token0: TOKEN0,
            token1: TOKEN1,
            tick_spacing,
            fee,
            extension: U256::zero(),
        }
    }

    #[test]
    fn test_quote_zero_liquidity_token1_input() {
        let pool = BasePool::new(
            node_key(1, 0),
            BasePoolState {
                sqrt_ratio: U256([0, 0, 1, 0]),
                liquidity: 0u128,
                active_tick_index: None,
            },
            vec![],
        );

        let params = QuoteParams {
            token_amount: TokenAmount {
                amount: 1,
                token: TOKEN1,
            },
            sqrt_ratio_limit: None,
            override_state: None,
            meta: QuoteMeta {
                block: Block { number: 1, time: 2 },
            },
        };

        let quote = pool.quote(params).expect("Failed to get quote");

        assert_eq!(quote.calculated_amount, 0);
        assert_eq!(quote.execution_resources.initialized_ticks_crossed, 0);
    }

    #[test]
    fn test_quote_zero_liquidity_token0_input() {
        let pool = BasePool::new(
            node_key(1, 0),
            BasePoolState {
                sqrt_ratio: U256([0, 0, 1, 0]),
                liquidity: 0u128,
                active_tick_index: None,
            },
            vec![],
        );

        let params = QuoteParams {
            token_amount: TokenAmount {
                amount: 1,
                token: TOKEN0,
            },
            sqrt_ratio_limit: None,
            override_state: None,
            meta: QuoteMeta {
                block: Block { number: 1, time: 2 },
            },
        };

        let quote = pool.quote(params).expect("Failed to get quote");

        assert_eq!(quote.calculated_amount, 0);
        assert_eq!(quote.execution_resources.initialized_ticks_crossed, 0);
    }

    #[test]
    fn test_quote_liquidity_token1_input() {
        let sorted_ticks = vec![
            Tick {
                index: 0,
                liquidity_delta: 1_000_000_000,
            },
            Tick {
                index: 1,
                liquidity_delta: -1_000_000_000,
            },
        ];

        let pool = BasePool::new(
            node_key(1, 0),
            BasePoolState {
                sqrt_ratio: U256([0, 0, 1, 0]),
                liquidity: 1_000_000_000u128,
                active_tick_index: Some(0),
            },
            sorted_ticks,
        );

        let params = QuoteParams {
            token_amount: TokenAmount {
                amount: 1000,
                token: TOKEN1,
            },
            sqrt_ratio_limit: None,
            override_state: None,
            meta: QuoteMeta {
                block: Block { number: 1, time: 2 },
            },
        };

        let quote = pool.quote(params).expect("Failed to get quote");

        assert_eq!(quote.calculated_amount, 499);
        assert_eq!(quote.execution_resources.initialized_ticks_crossed, 1);
    }

    #[test]
    fn test_quote_liquidity_token0_input() {
        let sorted_ticks = vec![
            Tick {
                index: 0,
                liquidity_delta: 1_000_000_000,
            },
            Tick {
                index: 1,
                liquidity_delta: -1_000_000_000,
            },
        ];

        let pool = BasePool::new(
            node_key(1, 0),
            BasePoolState {
                sqrt_ratio: to_sqrt_ratio(1).expect("Invalid tick"),
                liquidity: 0,
                active_tick_index: Some(1),
            },
            sorted_ticks,
        );

        let params = QuoteParams {
            token_amount: TokenAmount {
                amount: 1000,
                token: TOKEN0,
            },
            sqrt_ratio_limit: None,
            override_state: None,
            meta: QuoteMeta {
                block: Block { number: 1, time: 2 },
            },
        };

        let quote = pool.quote(params).expect("Failed to get quote");

        assert_eq!(quote.calculated_amount, 499);
        assert_eq!(quote.execution_resources.initialized_ticks_crossed, 2);
    }
}