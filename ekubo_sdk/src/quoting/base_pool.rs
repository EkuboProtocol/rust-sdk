use crate::math::swap::{compute_step, is_price_increasing, ComputeStepError};
use crate::math::tick::{to_sqrt_ratio, MAX_SQRT_RATIO, MIN_SQRT_RATIO};
use crate::math::uint::U256;
use crate::quoting::types::{BasePoolResources, BasePoolState, NodeKey, Quote, QuoteParams, Tick};
use alloc::vec::Vec;

enum QuoteError {
    InvalidToken,
    InvalidSqrtRatioLimit,
    FailedComputeSwapStep(ComputeStepError),
}

// Function to find the nearest initialized tick index.
fn find_nearest_initialized_tick_index(sorted_ticks: &[Tick], tick: i32) -> Option<usize> {
    let mut l = 0usize;
    let mut r = sorted_ticks.len();

    while l < r {
        let mid = (l + r) / 2;
        let mid_tick = sorted_ticks[mid].tick;
        if mid_tick <= tick {
            if mid == sorted_ticks.len() - 1 || sorted_ticks[mid + 1].tick > tick {
                return Some(mid);
            } else {
                l = mid;
            }
        } else {
            r = mid;
        }
    }

    None
}

// Main struct representing the pool.
struct BasePool {
    key: NodeKey,
    state: BasePoolState,
    sorted_ticks: Vec<Tick>,
}

impl BasePool {
    // Constructor for BasePool.
    pub fn new(
        token0: U256,
        token1: U256,
        tick_spacing: u32,
        fee: u128,
        sqrt_ratio: U256,
        liquidity: u128,
        tick: i32,
        sorted_ticks: Vec<Tick>,
    ) -> Self {
        let key = NodeKey {
            token0,
            token1,
            fee,
            tick_spacing,
            extension: U256::zero(),
        };

        let active_tick_index = find_nearest_initialized_tick_index(&sorted_ticks, tick);

        let state = BasePoolState {
            sqrt_ratio,
            liquidity,
            active_tick_index,
        };

        Self {
            key,
            state,
            sorted_ticks,
        }
    }

    // Combines two resource usages.
    fn combine_resources(
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

        let mut resources = self.initial_resources();

        if amount == 0 {
            return Ok(Quote {
                is_price_increasing: is_token1,
                consumed_amount: 0,
                calculated_amount: 0,
                execution_resources: resources,
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
        let mut initialized_ticks_crossed = resources.initialized_ticks_crossed;
        let mut amount_remaining = amount;

        let starting_sqrt_ratio = sqrt_ratio;

        while amount_remaining != 0 && sqrt_ratio != sqrt_ratio_limit {
            let next_initialized_tick: Option<&Tick> = if is_increasing {
                if let Some(index) = active_tick_index {
                    if index + 1 < self.sorted_ticks.len() {
                        self.sorted_ticks.get(index + 1)
                    } else {
                        None
                    }
                } else {
                    if self.sorted_ticks.is_empty() {
                        None
                    } else {
                        self.sorted_ticks.get(0)
                    }
                }
            } else {
                if let Some(index) = active_tick_index {
                    self.sorted_ticks.get(index)
                } else {
                    None
                }
            };

            let next_initialized_tick_sqrt_ratio = if let Some(tick) = next_initialized_tick {
                to_sqrt_ratio(tick.tick).expect("Invalid tick in sorted ticks")
            } else {
                if is_increasing {
                    MAX_SQRT_RATIO
                } else {
                    MIN_SQRT_RATIO
                }
            };

            let step_sqrt_ratio_limit =
                if (next_initialized_tick_sqrt_ratio < sqrt_ratio_limit) == is_increasing {
                    next_initialized_tick_sqrt_ratio
                } else {
                    sqrt_ratio_limit
                };

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

            if let Some(next_tick) = next_initialized_tick {
                if sqrt_ratio == next_initialized_tick_sqrt_ratio {
                    active_tick_index = if is_increasing {
                        active_tick_index.map(|i| i + 1usize)
                    } else {
                        active_tick_index.map(|i| i - 1usize)
                    };
                    initialized_ticks_crossed += 1;
                    if is_increasing {
                        liquidity = liquidity + next_tick.liquidity_delta.unsigned_abs();
                    } else {
                        liquidity = liquidity - next_tick.liquidity_delta.unsigned_abs();
                    };
                }
            }
        }

        resources.initialized_ticks_crossed = initialized_ticks_crossed;
        resources.tick_spacings_crossed += 1;

        //     approximate_number_of_tick_spacings_crossed(
        //     starting_sqrt_ratio,
        //     sqrt_ratio,
        //     self.key.tick_spacing,
        // );

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
