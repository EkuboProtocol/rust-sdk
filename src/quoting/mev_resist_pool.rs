use crate::math::tick::{approximate_sqrt_ratio_to_tick, FULL_RANGE_TICK_SPACING};
use crate::quoting::base_pool::{BasePool, BasePoolQuoteError, BasePoolResources, BasePoolState};
use crate::quoting::types::{BlockTimestamp, NodeKey, Pool, Quote, QuoteParams};
use core::ops::{Add, AddAssign};

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

#[derive(Clone, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct MEVResistPool {
    base_pool: BasePool,
    last_update_time: u32,
    tick: i32,
}

#[derive(Clone, Debug, PartialEq, Eq, Copy)]
pub struct MEVResistPoolState {
    last_update_time: u32,
    base_pool_state: BasePoolState,
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

                let approximate_fee_multiplier = ((tick_after_swap - self.tick).abs() as u32)
                    / self.base_pool.get_key().config.tick_spacing;

                let pool_time = params
                    .override_state
                    .map_or(self.last_update_time, |mrps| mrps.last_update_time);

                // if the time is updated, fees are accumulated to the current liquidity providers
                // this is at least 2 additional SSTOREs
                let state_update_count = if pool_time != current_time { 1 } else { 0 };

                if approximate_fee_multiplier == 0 {
                    // nothing to do here
                    return Ok(Quote {
                        calculated_amount: quote.calculated_amount,
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
                    });
                }

                return Ok(Quote {
                    // todo: discount the calculated amount
                    calculated_amount: quote.calculated_amount,
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
                });
            }
            Err(err) => return Err(err),
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
