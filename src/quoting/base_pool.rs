use crate::math::swap::{compute_step, is_price_increasing, ComputeStepError};
use crate::math::tick::{to_sqrt_ratio, MAX_SQRT_RATIO, MIN_SQRT_RATIO};
use crate::math::uint::U256;
use crate::quoting::types::{NodeKey, Pool, Quote, QuoteParams, Tick};
use crate::quoting::util::{
    approximate_number_of_tick_spacings_crossed, construct_sorted_ticks, ConstructSortedTicksError,
};
use alloc::vec::Vec;
use core::ops::{Add, AddAssign, Sub, SubAssign};
use num_traits::Zero;

// Resources consumed during any swap execution.
#[derive(Clone, Copy, Default, Debug, PartialEq, Eq)]
pub struct BasePoolResources {
    pub no_override_price_change: u32,
    pub initialized_ticks_crossed: u32,
    pub tick_spacings_crossed: u32,
}

impl AddAssign for BasePoolResources {
    fn add_assign(&mut self, rhs: Self) {
        self.no_override_price_change += rhs.no_override_price_change;
        self.initialized_ticks_crossed += rhs.initialized_ticks_crossed;
        self.tick_spacings_crossed += rhs.tick_spacings_crossed;
    }
}

impl Add for BasePoolResources {
    type Output = Self;

    fn add(mut self, rhs: Self) -> Self::Output {
        self += rhs;
        self
    }
}

impl SubAssign for BasePoolResources {
    fn sub_assign(&mut self, rhs: Self) {
        self.no_override_price_change -= rhs.no_override_price_change;
        self.initialized_ticks_crossed -= rhs.initialized_ticks_crossed;
        self.tick_spacings_crossed -= rhs.tick_spacings_crossed;
    }
}

impl Sub for BasePoolResources {
    type Output = Self;

    fn sub(mut self, rhs: Self) -> Self::Output {
        self -= rhs;
        self
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

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum BasePoolQuoteError {
    InvalidToken,
    InvalidSqrtRatioLimit,
    InvalidTick(i32),
    FailedComputeSwapStep(ComputeStepError),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct BasePoolState {
    #[cfg_attr(feature = "serde", serde(with = "crate::quoting::types::serde_u256"))]
    pub sqrt_ratio: U256,
    pub liquidity: u128,
    pub active_tick_index: Option<usize>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct BasePool {
    key: NodeKey,
    state: BasePoolState,
    sorted_ticks: Vec<Tick>,
}

/// Errors that can occur when constructing a BasePool.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum BasePoolError {
    ConstructSortedTicksFromPartialDataError(ConstructSortedTicksError),
    /// Token0 must be less than token1.
    TokenOrderInvalid,
    /// Tick spacing must be less than or equal to max tick spacing.
    TickSpacingTooLarge,
    /// Tick spacing must be greater than zero. Use the `FullRangePool` instead if you encounter this error.
    TickSpacingCannotBeZero,
    /// Ticks must be sorted in ascending order.
    TicksNotSorted,
    /// All ticks must be a multiple of tick_spacing.
    TickNotMultipleOfSpacing,
    /// The total liquidity across all ticks must sum to zero.
    TotalLiquidityNotZero,
    /// Active liquidity doesn't match the sum of liquidity deltas before the active tick.
    ActiveLiquidityMismatch,
    /// The sqrt_ratio of active tick is not less than or equal to current sqrt_ratio.
    ActiveTickSqrtRatioInvalid,
    /// current sqrt_ratio must be lower than the first tick's sqrt_ratio when active_tick_index is none.
    SqrtRatioTooHighWithNoActiveTick,
    /// The active tick index is out of bounds.
    ActiveTickIndexOutOfBounds,
    /// Invalid tick index.
    InvalidTickIndex(i32),
    /// The application of all tick liquidity deltas must result in a valid intermediate active liqudity.
    ActiveLiquidityOverflow,
}

impl BasePool {
    /// Creates a BasePool from partial tick data retrieved from a quote data fetcher lens contract.
    ///
    /// This helper constructor takes partial tick data along with min/max tick boundaries and constructs
    /// a valid BasePool instance with properly balanced liquidity deltas.
    ///
    /// # Arguments
    ///
    /// * `key` - The NodeKey containing token information and configuration
    /// * `sqrt_ratio` - The square root price ratio of the pool
    /// * `partial_ticks` - A vector of ticks retrieved from the lens contract
    /// * `min_tick_searched` - The minimum tick that was searched (not necessarily a multiple of tick spacing)
    /// * `max_tick_searched` - The maximum tick that was searched (not necessarily a multiple of tick spacing)
    /// * `liquidity` - The current liquidity of the pool
    /// * `current_tick` - The current tick of the pool
    ///
    /// # Returns
    ///
    /// * `Result<Self, BasePoolError>` - A new BasePool instance or an error
    pub fn from_partial_data(
        key: NodeKey,
        sqrt_ratio: U256,
        partial_ticks: Vec<Tick>,
        min_tick_searched: i32,
        max_tick_searched: i32,
        liquidity: u128,
        current_tick: i32,
    ) -> Result<Self, BasePoolError> {
        // Use the construct_sorted_ticks function to get valid sorted ticks
        let tick_spacing = key.tick_spacing;
        let spacing_i32 = tick_spacing as i32;

        // Get sorted ticks using the utility function
        let sorted_ticks = construct_sorted_ticks(
            partial_ticks,
            min_tick_searched,
            max_tick_searched,
            tick_spacing,
            liquidity,
            current_tick,
        )
        .map_err(BasePoolError::ConstructSortedTicksFromPartialDataError)?;

        // Ensure all ticks are multiples of tick spacing
        for tick in &sorted_ticks {
            if tick.index % spacing_i32 != 0 {
                return Err(BasePoolError::TickNotMultipleOfSpacing);
            }
        }

        // Find the active tick index (closest initialized tick at or below current_tick)
        let mut active_tick_index = None;
        for (i, tick) in sorted_ticks.iter().enumerate() {
            if tick.index <= current_tick {
                active_tick_index = Some(i);
            } else {
                break;
            }
        }

        // Create the BasePoolState with the provided sqrt_ratio, liquidity, and computed active_tick_index
        let state = BasePoolState {
            sqrt_ratio,
            liquidity,
            active_tick_index,
        };

        // Call the existing constructor with the prepared parameters
        Self::new(key, state, sorted_ticks)
    }

    pub fn new(
        key: NodeKey,
        state: BasePoolState,
        sorted_ticks: Vec<Tick>,
    ) -> Result<Self, BasePoolError> {
        // Validate token ordering
        if !(key.token0 < key.token1) {
            return Err(BasePoolError::TokenOrderInvalid);
        }

        // Validate tick spacing
        if key.tick_spacing > MAX_TICK_SPACING {
            return Err(BasePoolError::TickSpacingTooLarge);
        }

        if key.tick_spacing.is_zero() {
            return Err(BasePoolError::TickSpacingCannotBeZero);
        }

        // Check ticks are sorted in linear time
        let mut last_tick: Option<i32> = None;
        let mut total_liquidity: u128 = 0;
        let mut active_liquidity: u128 = 0;
        let spacing_i32 = key.tick_spacing as i32;

        for (i, tick) in sorted_ticks.iter().enumerate() {
            // Verify ticks are sorted
            if let Some(last) = last_tick {
                if !(tick.index > last) {
                    return Err(BasePoolError::TicksNotSorted);
                }
            };

            // Verify ticks are multiples of tick_spacing
            if !(tick.index % spacing_i32).is_zero() {
                return Err(BasePoolError::TickNotMultipleOfSpacing);
            }

            last_tick = Some(tick.index);

            // Calculate total liquidity
            total_liquidity = if tick.liquidity_delta < 0 {
                total_liquidity.checked_sub(tick.liquidity_delta.unsigned_abs())
            } else {
                total_liquidity.checked_add(tick.liquidity_delta.unsigned_abs())
            }
            .ok_or(BasePoolError::ActiveLiquidityOverflow)?;

            // Calculate active liquidity
            if let Some(active_index) = state.active_tick_index {
                if i <= active_index {
                    active_liquidity = if tick.liquidity_delta > 0 {
                        active_liquidity.checked_add(tick.liquidity_delta.unsigned_abs())
                    } else {
                        active_liquidity.checked_sub(tick.liquidity_delta.unsigned_abs())
                    }
                    .ok_or(BasePoolError::ActiveLiquidityOverflow)?;
                }
            }
        }

        // Verify total liquidity is zero
        if !total_liquidity.is_zero() {
            return Err(BasePoolError::TotalLiquidityNotZero);
        }

        // Verify active liquidity matches state liquidity
        if active_liquidity != state.liquidity {
            return Err(BasePoolError::ActiveLiquidityMismatch);
        }

        // Validate sqrt ratio against active or first tick
        if let Some(active) = state.active_tick_index {
            let tick = sorted_ticks
                .get(active)
                .ok_or(BasePoolError::ActiveTickIndexOutOfBounds)?;

            let active_tick_sqrt_ratio =
                to_sqrt_ratio(tick.index).ok_or(BasePoolError::InvalidTickIndex(tick.index))?;

            if !(active_tick_sqrt_ratio <= state.sqrt_ratio) {
                return Err(BasePoolError::ActiveTickSqrtRatioInvalid);
            }
        } else {
            if let Some(first) = sorted_ticks.first() {
                let first_tick_sqrt_ratio = to_sqrt_ratio(first.index)
                    .ok_or(BasePoolError::InvalidTickIndex(first.index))?;

                if !(state.sqrt_ratio <= first_tick_sqrt_ratio) {
                    return Err(BasePoolError::SqrtRatioTooHighWithNoActiveTick);
                }
            }
        }

        Ok(Self {
            key,
            state,
            sorted_ticks,
        })
    }

    pub fn get_sorted_ticks(&self) -> &Vec<Tick> {
        &self.sorted_ticks
    }
}

// Tests for the from_partial_data constructor
#[cfg(test)]
mod from_partial_data_tests {
    use super::*;
    use crate::math::tick::{MAX_TICK, MIN_TICK};
    use alloc::vec;

    // Constants for testing
    const TOKEN0: U256 = U256([1, 0, 0, 0]);
    const TOKEN1: U256 = U256([2, 0, 0, 0]);

    #[test]
    fn test_from_partial_data_empty_ticks() {
        // Test creating a pool with empty tick data
        let key = NodeKey {
            token0: TOKEN0,
            token1: TOKEN1,
            tick_spacing: 10,
            extension: U256::zero(),
            fee: 0,
        };

        let sqrt_ratio = to_sqrt_ratio(0).unwrap();
        let partial_ticks = Vec::new();
        let min_tick_searched = -5005;
        let max_tick_searched = 5005;
        let liquidity = 1000;
        let current_tick = 0;

        let result = BasePool::from_partial_data(
            key,
            sqrt_ratio,
            partial_ticks,
            min_tick_searched,
            max_tick_searched,
            liquidity,
            current_tick,
        );

        assert!(result.is_ok());
        let pool = result.unwrap();

        // Verify the pool has MIN_TICK and MAX_TICK ticks
        let ticks = pool.get_sorted_ticks();
        assert_eq!(ticks.len(), 2);
        assert_eq!(ticks[0].index, -5010);
        assert_eq!(ticks[0].liquidity_delta, liquidity as i128);
        assert_eq!(ticks[1].index, 5010);
        assert_eq!(ticks[1].liquidity_delta, -(liquidity as i128));
    }

    #[test]
    fn test_from_partial_data_with_partial_ticks() {
        // Test creating a pool with partial ticks
        let key = NodeKey {
            token0: TOKEN0,
            token1: TOKEN1,
            tick_spacing: 10,
            extension: U256::zero(),
            fee: 0,
        };

        let sqrt_ratio = to_sqrt_ratio(50).unwrap();
        let partial_ticks = vec![
            Tick {
                index: 0,
                liquidity_delta: 500,
            },
            Tick {
                index: 100,
                liquidity_delta: -200,
            },
        ];

        let min_tick_searched = -45;
        let max_tick_searched = 145;
        let liquidity = 750;
        let current_tick = 52;

        let result = BasePool::from_partial_data(
            key,
            sqrt_ratio,
            partial_ticks,
            min_tick_searched,
            max_tick_searched,
            liquidity,
            current_tick,
        );

        assert!(result.is_ok());
        let pool = result.unwrap();

        // Verify the constructed pool has the correct properties
        let ticks = pool.get_sorted_ticks();

        // Check that we have ticks at the min and max boundaries
        assert_eq!(
            pool.sorted_ticks.first().unwrap(),
            &Tick {
                index: -50,
                liquidity_delta: 250
            }
        );
        assert_eq!(
            pool.sorted_ticks.last().unwrap(),
            &Tick {
                index: 150,
                liquidity_delta: -550
            }
        );

        // Verify active_tick_index points to tick at or before current_tick
        let active_index = pool.state.active_tick_index;
        assert_eq!(active_index.unwrap(), 1);

        // Verify all liquidity deltas sum to zero
        let sum: i128 = ticks.iter().map(|t| t.liquidity_delta).sum();
        assert_eq!(sum, 0);

        // Verify active liquidity matches
        assert_eq!(pool.state.liquidity, liquidity);
    }

    #[test]
    fn test_from_partial_data_tick_spacing_validation() {
        // Test that the tick spacing validation works
        let key = NodeKey {
            token0: TOKEN0,
            token1: TOKEN1,
            tick_spacing: 0,
            extension: U256::zero(),
            fee: 0,
        };

        let sqrt_ratio = to_sqrt_ratio(0).unwrap();
        let partial_ticks = Vec::new();
        let min_tick_searched = MIN_TICK;
        let max_tick_searched = MAX_TICK;
        let liquidity = 1000;
        let current_tick = 0;

        let result = BasePool::from_partial_data(
            key,
            sqrt_ratio,
            partial_ticks,
            min_tick_searched,
            max_tick_searched,
            liquidity,
            current_tick,
        );

        // Should fail with TickSpacingCannotBeZero
        assert_eq!(
            result.unwrap_err(),
            BasePoolError::ConstructSortedTicksFromPartialDataError(
                ConstructSortedTicksError::InvalidTickSpacing
            )
        );
    }
}

impl Pool for BasePool {
    type Resources = BasePoolResources;
    type State = BasePoolState;
    type QuoteError = BasePoolQuoteError;
    type Meta = ();

    fn get_key(&self) -> &NodeKey {
        &self.key
    }

    fn get_state(&self) -> Self::State {
        self.state
    }

    fn quote(
        &self,
        params: QuoteParams<Self::State, Self::Meta>,
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

        let mut calculated_amount: u128 = 0;
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
                amount_remaining,
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
                active_tick_index = if is_increasing {
                    self.sorted_ticks.len().checked_sub(1)
                } else {
                    None
                };
            }
        }

        let resources = BasePoolResources {
            // we ignore changes from the override price because we assume the price has already changed
            no_override_price_change: if starting_sqrt_ratio == self.state.sqrt_ratio
                && starting_sqrt_ratio != sqrt_ratio
            {
                1
            } else {
                0
            },
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

    fn max_tick_with_liquidity(&self) -> Option<i32> {
        self.sorted_ticks.last().map(|t| t.index)
    }

    fn min_tick_with_liquidity(&self) -> Option<i32> {
        self.sorted_ticks.first().map(|t| t.index)
    }

    fn is_path_dependent(&self) -> bool {
        false
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::quoting::types::TokenAmount;
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

    mod constructor_validation {
        use super::BasePoolError;
        use super::{to_sqrt_ratio, vec, BasePool, BasePoolState, NodeKey, MAX_TICK_SPACING, U256};
        use crate::math::tick::MAX_TICK;
        use crate::quoting::base_pool::BasePoolError::TickSpacingCannotBeZero;
        use crate::quoting::base_pool::MAX_TICK_AT_MAX_TICK_SPACING;
        use crate::quoting::types::Tick;

        #[test]
        fn test_token0_lt_token1() {
            let result = BasePool::new(
                NodeKey {
                    token0: U256::zero(),
                    token1: U256::zero(),
                    extension: U256::zero(),
                    fee: 0,
                    tick_spacing: 0,
                },
                BasePoolState {
                    sqrt_ratio: to_sqrt_ratio(0).unwrap(),
                    active_tick_index: None,
                    liquidity: 0,
                },
                vec![],
            );
            assert_eq!(result.unwrap_err(), BasePoolError::TokenOrderInvalid);
        }

        #[test]
        fn test_token0_zero() {
            let result = BasePool::new(
                NodeKey {
                    token0: U256::zero(),
                    token1: U256::one(),
                    extension: U256::zero(),
                    fee: 0,
                    tick_spacing: 1,
                },
                BasePoolState {
                    sqrt_ratio: to_sqrt_ratio(0).unwrap(),
                    active_tick_index: None,
                    liquidity: 0,
                },
                vec![],
            );
            assert!(result.is_ok());
        }

        #[test]
        fn test_tick_spacing_zero_reverts() {
            let result = BasePool::new(
                NodeKey {
                    token0: U256::one(),
                    token1: U256::one() + 1,
                    extension: U256::zero(),
                    fee: 0,
                    tick_spacing: 0,
                },
                BasePoolState {
                    sqrt_ratio: to_sqrt_ratio(0).unwrap(),
                    active_tick_index: None,
                    liquidity: 0,
                },
                vec![],
            );
            assert_eq!(result.unwrap_err(), TickSpacingCannotBeZero);
        }

        #[test]
        fn test_tick_spacing_lte_max() {
            let result = BasePool::new(
                NodeKey {
                    token0: U256::one(),
                    token1: U256::one() + 1,
                    extension: U256::zero(),
                    fee: 0,
                    tick_spacing: MAX_TICK_SPACING + 1,
                },
                BasePoolState {
                    sqrt_ratio: to_sqrt_ratio(0).unwrap(),
                    active_tick_index: None,
                    liquidity: 0,
                },
                vec![],
            );
            assert_eq!(result.unwrap_err(), BasePoolError::TickSpacingTooLarge);
        }

        #[test]
        fn test_active_tick_index_within_range() {
            let result = BasePool::new(
                NodeKey {
                    token0: U256::one(),
                    token1: U256::one() + 1,
                    extension: U256::zero(),
                    fee: 0,
                    tick_spacing: MAX_TICK_SPACING,
                },
                BasePoolState {
                    sqrt_ratio: to_sqrt_ratio(0).unwrap(),
                    active_tick_index: Some(0),
                    liquidity: 0,
                },
                vec![],
            );
            assert_eq!(
                result.unwrap_err(),
                BasePoolError::ActiveTickIndexOutOfBounds
            );
        }

        #[test]
        fn test_ticks_must_be_sorted() {
            let result = BasePool::new(
                NodeKey {
                    token0: U256::one(),
                    token1: U256::one() + 1,
                    extension: U256::zero(),
                    fee: 0,
                    tick_spacing: MAX_TICK_SPACING,
                },
                BasePoolState {
                    sqrt_ratio: to_sqrt_ratio(0).unwrap(),
                    active_tick_index: Some(0),
                    liquidity: 1,
                },
                vec![
                    Tick {
                        index: MAX_TICK_AT_MAX_TICK_SPACING,
                        liquidity_delta: 0,
                    },
                    Tick {
                        index: 0,
                        liquidity_delta: 0,
                    },
                ],
            );
            assert_eq!(result.unwrap_err(), BasePoolError::TicksNotSorted);
        }

        #[test]
        fn test_ticks_must_be_multiple_of_tick_spacing() {
            let result = BasePool::new(
                NodeKey {
                    token0: U256::one(),
                    token1: U256::one() + 1,
                    extension: U256::zero(),
                    fee: 0,
                    tick_spacing: MAX_TICK_SPACING,
                },
                BasePoolState {
                    sqrt_ratio: to_sqrt_ratio(0).unwrap(),
                    active_tick_index: Some(0),
                    liquidity: 1,
                },
                vec![
                    Tick {
                        index: -1,
                        liquidity_delta: 1,
                    },
                    Tick {
                        index: MAX_TICK - 1,
                        liquidity_delta: -1,
                    },
                ],
            );
            assert_eq!(result.unwrap_err(), BasePoolError::TickNotMultipleOfSpacing);
        }

        #[test]
        fn test_ticks_must_total_to_zero_liquidity() {
            let result = BasePool::new(
                NodeKey {
                    token0: U256::one(),
                    token1: U256::one() + 1,
                    extension: U256::zero(),
                    fee: 0,
                    tick_spacing: MAX_TICK_SPACING,
                },
                BasePoolState {
                    sqrt_ratio: to_sqrt_ratio(0).unwrap(),
                    active_tick_index: Some(0),
                    liquidity: 2,
                },
                vec![
                    Tick {
                        index: 0,
                        liquidity_delta: 2,
                    },
                    Tick {
                        index: MAX_TICK_AT_MAX_TICK_SPACING,
                        liquidity_delta: -1,
                    },
                ],
            );
            assert_eq!(result.unwrap_err(), BasePoolError::TotalLiquidityNotZero);
        }

        #[test]
        fn test_active_tick_index_must_be_within_bounds() {
            let result = BasePool::new(
                NodeKey {
                    token0: U256::one(),
                    token1: U256::one() + 1,
                    extension: U256::zero(),
                    fee: 0,
                    tick_spacing: MAX_TICK_SPACING,
                },
                BasePoolState {
                    sqrt_ratio: to_sqrt_ratio(0).unwrap(),
                    active_tick_index: Some(2),
                    liquidity: 0,
                },
                vec![
                    Tick {
                        index: 0,
                        liquidity_delta: 2,
                    },
                    Tick {
                        index: MAX_TICK_AT_MAX_TICK_SPACING,
                        liquidity_delta: -2,
                    },
                ],
            );
            assert_eq!(
                result.unwrap_err(),
                BasePoolError::ActiveTickIndexOutOfBounds
            );
        }

        #[test]
        fn test_liquidity_equal_sum_of_deltas_active_ticks() {
            let result = BasePool::new(
                NodeKey {
                    token0: U256::one(),
                    token1: U256::one() + 1,
                    extension: U256::zero(),
                    fee: 0,
                    tick_spacing: MAX_TICK_SPACING,
                },
                BasePoolState {
                    sqrt_ratio: to_sqrt_ratio(0).unwrap(),
                    active_tick_index: Some(0),
                    liquidity: 0,
                },
                vec![
                    Tick {
                        index: 0,
                        liquidity_delta: 2,
                    },
                    Tick {
                        index: MAX_TICK_AT_MAX_TICK_SPACING,
                        liquidity_delta: -2,
                    },
                ],
            );
            assert_eq!(result.unwrap_err(), BasePoolError::ActiveLiquidityMismatch);
        }

        #[test]
        fn test_active_tick_sqrt_ratio_is_lte_current_sqrt_ratio() {
            let result = BasePool::new(
                NodeKey {
                    token0: U256::one(),
                    token1: U256::one() + 1,
                    extension: U256::zero(),
                    fee: 0,
                    tick_spacing: MAX_TICK_SPACING,
                },
                BasePoolState {
                    sqrt_ratio: to_sqrt_ratio(0).unwrap() - 1,
                    active_tick_index: Some(0),
                    liquidity: 2,
                },
                vec![
                    Tick {
                        index: 0,
                        liquidity_delta: 2,
                    },
                    Tick {
                        index: MAX_TICK_AT_MAX_TICK_SPACING,
                        liquidity_delta: -2,
                    },
                ],
            );
            assert_eq!(
                result.unwrap_err(),
                BasePoolError::ActiveTickSqrtRatioInvalid
            );
        }

        #[test]
        fn test_if_no_active_tick_sqrt_ratio_lte_first() {
            let result = BasePool::new(
                NodeKey {
                    token0: U256::one(),
                    token1: U256::one() + 1,
                    extension: U256::zero(),
                    fee: 0,
                    tick_spacing: MAX_TICK_SPACING,
                },
                BasePoolState {
                    sqrt_ratio: to_sqrt_ratio(0).unwrap() + 1,
                    active_tick_index: None,
                    liquidity: 0,
                },
                vec![
                    Tick {
                        index: 0,
                        liquidity_delta: 2,
                    },
                    Tick {
                        index: MAX_TICK_AT_MAX_TICK_SPACING,
                        liquidity_delta: -2,
                    },
                ],
            );
            assert_eq!(
                result.unwrap_err(),
                BasePoolError::SqrtRatioTooHighWithNoActiveTick
            );
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
        )
        .expect("Pool creation should succeed");

        let params = QuoteParams {
            token_amount: TokenAmount {
                amount: 1,
                token: TOKEN1,
            },
            sqrt_ratio_limit: None,
            override_state: None,
            meta: (),
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
        )
        .expect("Pool creation should succeed");

        let params = QuoteParams {
            token_amount: TokenAmount {
                amount: 1,
                token: TOKEN0,
            },
            sqrt_ratio_limit: None,
            override_state: None,
            meta: (),
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
            meta: (),
        };

        let quote = pool
            .expect("Pool creation should succeed")
            .quote(params)
            .expect("Failed to get quote");

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
            meta: (),
        };

        let quote = pool
            .expect("Pool creation should succeed")
            .quote(params)
            .expect("Failed to get quote");

        assert_eq!(quote.calculated_amount, 499);
        assert_eq!(quote.execution_resources.initialized_ticks_crossed, 2);
    }

    #[test]
    fn test_example_failing_quote() {
        let pool = BasePool::new(
            node_key(100, 17014118346046923988514818429550592),
            BasePoolState {
                sqrt_ratio: U256([16035209758820767612, 757181812420893, 0, 0]),
                liquidity: 99999,
                active_tick_index: Some(16),
            },
            vec![
                Tick {
                    index: -88722000,
                    liquidity_delta: 99999,
                },
                Tick {
                    index: -24124600,
                    liquidity_delta: 103926982998885,
                },
                Tick {
                    index: -24124500,
                    liquidity_delta: -103926982998885,
                },
                Tick {
                    index: -20236100,
                    liquidity_delta: 20192651866847,
                },
                Tick {
                    index: -20235900,
                    liquidity_delta: 676843433645,
                },
                Tick {
                    index: -20235400,
                    liquidity_delta: 620315686813,
                },
                Tick {
                    index: -20235000,
                    liquidity_delta: 3899271022058,
                },
                Tick {
                    index: -20234900,
                    liquidity_delta: 1985516133391,
                },
                Tick {
                    index: -20233000,
                    liquidity_delta: 2459469409600,
                },
                Tick {
                    index: -20232100,
                    liquidity_delta: -20192651866847,
                },
                Tick {
                    index: -20231900,
                    liquidity_delta: -663892969024,
                },
                Tick {
                    index: -20231400,
                    liquidity_delta: -620315686813,
                },
                Tick {
                    index: -20231000,
                    liquidity_delta: -3516445235227,
                },
                Tick {
                    index: -20230900,
                    liquidity_delta: -1985516133391,
                },
                Tick {
                    index: -20229000,
                    liquidity_delta: -2459469409600,
                },
                Tick {
                    index: -20227900,
                    liquidity_delta: -12950464621,
                },
                Tick {
                    index: -20227000,
                    liquidity_delta: -382825786831,
                },
                Tick {
                    index: -2000,
                    liquidity_delta: 140308196,
                },
                Tick {
                    index: 2000,
                    liquidity_delta: -140308196,
                },
                Tick {
                    index: 88722000,
                    liquidity_delta: -99999,
                },
            ],
        );

        // Unwrap the pool once and store it
        let unwrapped_pool = pool.expect("Pool creation should succeed");

        let quote = unwrapped_pool
            .quote(QuoteParams {
                token_amount: TokenAmount {
                    amount: 1000000,
                    token: TOKEN0,
                },
                sqrt_ratio_limit: None,
                override_state: None,
                meta: (),
            })
            .expect("Failed to get quote of token0");

        assert_eq!(quote.calculated_amount, 0);
        assert_eq!(quote.execution_resources.initialized_ticks_crossed, 0);

        let quote = unwrapped_pool
            .quote(QuoteParams {
                token_amount: TokenAmount {
                    amount: 1000000,
                    token: TOKEN1,
                },
                sqrt_ratio_limit: None,
                override_state: None,
                meta: (),
            })
            .expect("Failed to get quote of token1");

        assert_eq!(quote.consumed_amount, 1_000_000);
        assert_eq!(quote.calculated_amount, 2436479431);
        assert_eq!(quote.execution_resources.initialized_ticks_crossed, 2);
    }
}
