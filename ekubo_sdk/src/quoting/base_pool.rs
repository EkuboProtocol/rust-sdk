use crate::math::swap::{compute_step, is_price_increasing, ComputeStepError};
use crate::math::tick::{to_sqrt_ratio, MAX_SQRT_RATIO, MIN_SQRT_RATIO};
use crate::math::uint::U256;
use crate::quoting::types::{BasePoolResources, BasePoolState, NodeKey, Quote, QuoteParams, Tick};
use crate::quoting::util::approximate_number_of_tick_spacings_crossed;
use alloc::vec::Vec;
use num_traits::Zero;

#[derive(Debug)]
pub enum QuoteError {
    InvalidToken,
    InvalidSqrtRatioLimit,
    InvalidTick(i32),
    FailedComputeSwapStep(ComputeStepError),
}

// Main struct representing the pool.
pub struct BasePool {
    key: NodeKey,
    state: BasePoolState,
    sorted_ticks: Vec<Tick>,
}

impl BasePool {
    pub fn new(key: NodeKey, state: BasePoolState, sorted_ticks: Vec<Tick>) -> Self {
        // todo: apply some validation to the arguments
        Self {
            key,
            state,
            sorted_ticks,
        }
    }

    // Combines two resource usages.
    pub fn combine_resources(
        &self,
        resource: BasePoolResources,
        additional_resources: BasePoolResources,
    ) -> BasePoolResources {
        BasePoolResources {
            initialized_ticks_crossed: resource.initialized_ticks_crossed
                + additional_resources.initialized_ticks_crossed,
            tick_spacings_crossed: resource.tick_spacings_crossed
                + additional_resources.tick_spacings_crossed,
        }
    }

    // Initializes resource usage.
    fn initial_resources(&self) -> BasePoolResources {
        BasePoolResources {
            initialized_ticks_crossed: 0,
            tick_spacings_crossed: 0,
        }
    }

    // Quotes a swap given the parameters.
    pub fn quote(&self, params: QuoteParams) -> Result<Quote, QuoteError> {
        let amount = params.token_amount.amount;
        let token = params.token_amount.token;
        let is_token1 = token == self.key.token1;

        if !is_token1 && token != self.key.token0 {
            return Err(QuoteError::InvalidToken);
        }

        let state = if let Some(ref override_state) = params.override_state {
            override_state.clone()
        } else {
            self.state.clone()
        };

        if amount == 0 {
            return Ok(Quote {
                is_price_increasing: is_token1,
                consumed_amount: 0,
                calculated_amount: 0,
                execution_resources: self.initial_resources(),
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
                return Err(QuoteError::InvalidSqrtRatioLimit);
            }
            if !is_increasing && limit > sqrt_ratio {
                return Err(QuoteError::InvalidSqrtRatioLimit);
            }
            if limit < MIN_SQRT_RATIO {
                return Err(QuoteError::InvalidSqrtRatioLimit);
            }
            if limit > MAX_SQRT_RATIO {
                return Err(QuoteError::InvalidSqrtRatioLimit);
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
                            to_sqrt_ratio(next.index).ok_or(QuoteError::InvalidTick(next.index))?,
                        ))
                    } else {
                        None
                    }
                } else {
                    if let Some(next) = self.sorted_ticks.first() {
                        Some((
                            0,
                            next,
                            to_sqrt_ratio(next.index).ok_or(QuoteError::InvalidTick(next.index))?,
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
                            to_sqrt_ratio(tick.index).ok_or(QuoteError::InvalidTick(tick.index))?,
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
            .map_err(QuoteError::FailedComputeSwapStep)?;

            amount_remaining -= step.consumed_amount;
            calculated_amount += step.calculated_amount;
            fees_paid += step.fee_amount;
            sqrt_ratio = step.sqrt_ratio_next;

            if let Some((index, next_tick, _)) = next_initialized_tick {
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
    pub fn has_liquidity(&self) -> bool {
        self.state.liquidity > 0 || !self.sorted_ticks.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::quoting::types::{Block, QuoteMeta, TokenAmount};
    use alloc::vec;

    fn node_key(tick_spacing: u32, fee: u128) -> NodeKey {
        NodeKey {
            token0: U256::zero(),
            token1: U256::one(),
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
            vec![], // sorted_ticks
        );

        let params = QuoteParams {
            token_amount: TokenAmount {
                amount: 1,
                token: U256::from(1u64),
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
            vec![], // sorted_ticks
        );

        let params = QuoteParams {
            token_amount: TokenAmount {
                amount: 1,
                token: U256::from(0u64),
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
                token: U256::from(1u64),
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
                token: U256::from(0u64),
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
