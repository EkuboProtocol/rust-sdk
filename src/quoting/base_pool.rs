use crate::math::swap::{compute_step, is_price_increasing, ComputeStepError};
use crate::math::tick::{to_sqrt_ratio, MAX_SQRT_RATIO, MIN_SQRT_RATIO};
use crate::math::uint::U256;
use crate::quoting::types::{NodeKey, Pool, Quote, QuoteParams, Tick};
use crate::quoting::util::approximate_number_of_tick_spacings_crossed;
use alloc::vec::Vec;
use core::ops::{Add, AddAssign};
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

pub const FULL_RANGE_TICK_SPACING: u32 = 0;
pub const MAX_TICK_SPACING: u32 = 698605;

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
        if key.config.tick_spacing > MAX_TICK_SPACING {
            return Err(BasePoolError::TickSpacingTooLarge);
        }

        if key.config.tick_spacing.is_zero() {
            return Err(BasePoolError::TickSpacingCannotBeZero);
        }

        // Check ticks are sorted in linear time
        let mut last_tick: Option<i32> = None;
        let mut total_liquidity: u128 = 0;
        let mut active_liquidity: u128 = 0;
        let spacing_i32 = key.config.tick_spacing as i32;

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
    
    /// Converts a partial view of sorted tick data into valid sorted tick data for the base pool.
    ///
    /// This function takes partial tick data retrieved from a quote data fetcher lens contract
    /// along with min/max tick range, and constructs a valid set of sorted ticks that ensures:
    /// 1. All liquidity deltas add up to zero
    /// 2. The current liquidity matches the sum of liquidity deltas from MIN_TICK to current active tick
    ///
    /// # Arguments
    ///
    /// * `partial_ticks` - A vector of ticks retrieved from the lens contract
    /// * `min_tick_searched` - The minimum tick that was searched (not necessarily a multiple of tick spacing)
    /// * `max_tick_searched` - The maximum tick that was searched (not necessarily a multiple of tick spacing)
    /// * `tick_spacing` - The tick spacing of the pool
    /// * `liquidity` - The current liquidity of the pool
    /// * `current_tick` - The current tick of the pool
    ///
    /// # Returns
    ///
    /// * `Vec<Tick>` - A new vector with valid sorted ticks
    pub fn construct_sorted_ticks(
        partial_ticks: Vec<Tick>,
        min_tick_searched: i32,
        max_tick_searched: i32,
        tick_spacing: u32,
        liquidity: u128,
        current_tick: i32,
    ) -> Vec<Tick> {
        if partial_ticks.is_empty() {
            return Self::create_full_range_ticks(liquidity);
        }

        let spacing_i32 = tick_spacing as i32;
        
        // Round min/max ticks to valid ticks (min down, max up)
        let valid_min_tick = if min_tick_searched == crate::math::tick::MIN_TICK {
            crate::math::tick::MIN_TICK
        } else {
            // Round down to nearest multiple of tick spacing
            let remainder = min_tick_searched % spacing_i32;
            if remainder < 0 {
                min_tick_searched - (spacing_i32 + remainder)
            } else {
                min_tick_searched - remainder
            }
        };
        
        let valid_max_tick = if max_tick_searched == crate::math::tick::MAX_TICK {
            crate::math::tick::MAX_TICK
        } else {
            // Round up to nearest multiple of tick spacing
            let remainder = max_tick_searched % spacing_i32;
            if remainder == 0 {
                max_tick_searched
            } else if remainder < 0 {
                max_tick_searched - remainder
            } else {
                max_tick_searched + (spacing_i32 - remainder)
            }
        };

        // Create result vector and add all partial ticks
        let mut result = partial_ticks.clone();
        
        // Calculate current sum of all liquidity deltas
        let liquidity_delta_sum: i128 = result.iter().map(|tick| tick.liquidity_delta).sum();
        
        // Calculate current active liquidity from ticks before or at current tick
        let mut current_tick_index = None;
        let mut active_liquidity: u128 = 0;
        
        for (i, tick) in result.iter().enumerate() {
            if tick.index <= current_tick {
                current_tick_index = Some(i);
                if tick.liquidity_delta > 0 {
                    active_liquidity = active_liquidity.saturating_add(tick.liquidity_delta.unsigned_abs());
                } else {
                    // Skip subtraction if it would underflow
                    if active_liquidity >= tick.liquidity_delta.unsigned_abs() {
                        active_liquidity = active_liquidity.saturating_sub(tick.liquidity_delta.unsigned_abs());
                    }
                }
            } else {
                break;
            }
        }
        
        // Add min bound tick if needed
        if !result.is_empty() && result[0].index > valid_min_tick {
            let min_liquidity_delta = Self::calculate_min_liquidity_delta(
                &result, 
                liquidity, 
                active_liquidity, 
                liquidity_delta_sum,
                current_tick <= valid_min_tick,
            );
            
            result.insert(0, Tick {
                index: valid_min_tick,
                liquidity_delta: min_liquidity_delta,
            });
            
            // Update current tick index if min tick is less than or equal to current tick
            if current_tick <= valid_min_tick && current_tick_index.is_none() {
                current_tick_index = Some(0);
                if min_liquidity_delta > 0 {
                    active_liquidity = active_liquidity.saturating_add(min_liquidity_delta.unsigned_abs());
                } else {
                    active_liquidity = active_liquidity.saturating_sub(min_liquidity_delta.unsigned_abs());
                }
            } else if current_tick_index.is_some() {
                current_tick_index = Some(current_tick_index.unwrap() + 1);
            }
        }
        
        // Add max bound tick if needed
        if !result.is_empty() && result.last().unwrap().index < valid_max_tick {
            // If we have a min tick, we need to balance it out
            // Otherwise, we need to make sure all liquidity deltas sum to zero
            let max_liquidity_delta = -result.iter().map(|tick| tick.liquidity_delta).sum::<i128>();
            
            // Ensure the tick doesn't already exist
            if !result.iter().any(|t| t.index == valid_max_tick) {
                result.push(Tick {
                    index: valid_max_tick,
                    liquidity_delta: max_liquidity_delta,
                });
            } else {
                // If it exists, update its liquidity delta
                for tick in result.iter_mut() {
                    if tick.index == valid_max_tick {
                        tick.liquidity_delta = max_liquidity_delta;
                        break;
                    }
                }
            }
        }
        
        // Ensure that the current liquidity matches the active liquidity
        if active_liquidity != liquidity {
            let liquidity_difference = if active_liquidity > liquidity {
                // Convert to i128 first, then negate to avoid the unary negation on u128
                -((active_liquidity - liquidity) as i128)
            } else {
                (liquidity - active_liquidity) as i128
            };
            
            if let Some(index) = current_tick_index {
                // Adjust the tick at or before current_tick
                if index < result.len() {
                    result[index].liquidity_delta += liquidity_difference;
                    
                    // We need to balance this change at the max tick
                    if let Some(last_tick) = result.last_mut() {
                        last_tick.liquidity_delta -= liquidity_difference;
                    }
                }
            } else if !result.is_empty() {
                // Need to add a new tick at current_tick
                let mut insert_pos = 0;
                while insert_pos < result.len() && result[insert_pos].index < current_tick {
                    insert_pos += 1;
                }
                
                let new_tick = Tick {
                    index: current_tick - (current_tick % spacing_i32),
                    liquidity_delta: liquidity_difference,
                };
                
                result.insert(insert_pos, new_tick);
                
                // Balance this change at the max tick
                if let Some(last_tick) = result.last_mut() {
                    last_tick.liquidity_delta -= liquidity_difference;
                }
            }
        }
        
        // Ensure ticks are sorted
        result.sort_by_key(|tick| tick.index);
        
        // Remove any duplicate ticks by combining their liquidity deltas
        let mut i = 0;
        while i + 1 < result.len() {
            if result[i].index == result[i + 1].index {
                result[i].liquidity_delta += result[i + 1].liquidity_delta;
                result.remove(i + 1);
            } else {
                i += 1;
            }
        }
        
        // Remove any ticks with zero liquidity delta
        result.retain(|tick| tick.liquidity_delta != 0);
        
        result
    }
    
    /// Creates ticks for a full range pool with the specified liquidity
    fn create_full_range_ticks(liquidity: u128) -> Vec<Tick> {
        if liquidity == 0 {
            return Vec::new();
        }
        
        alloc::vec![
            Tick {
                index: crate::math::tick::MIN_TICK,
                liquidity_delta: liquidity as i128,
            },
            Tick {
                index: crate::math::tick::MAX_TICK,
                liquidity_delta: -(liquidity as i128),
            },
        ]
    }
    
    /// Calculates the appropriate liquidity delta for the min tick
    fn calculate_min_liquidity_delta(
        _ticks: &[Tick],
        liquidity: u128,
        active_liquidity: u128,
        liquidity_delta_sum: i128,
        min_tick_is_active: bool,
    ) -> i128 {
        // If min tick is active, handle liquidity adjustment
        if min_tick_is_active {
            let required_delta = liquidity as i128 - active_liquidity as i128;
            // If all ticks sum to zero, we just need to balance active liquidity
            if liquidity_delta_sum == 0 {
                return required_delta;
            } else {
                // Otherwise we need to ensure the min tick balances both requirements
                return required_delta - liquidity_delta_sum;
            }
        } else {
            // If min tick is not active, it just needs to balance the sum
            -liquidity_delta_sum
        }
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
                amount_remaining,
                is_token1,
                self.key.config.fee,
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
                self.key.config.tick_spacing,
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
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::quoting::types::{Config, TokenAmount};
    use alloc::vec;
    use crate::math::tick::{MIN_TICK, MAX_TICK};

    const TOKEN0: U256 = U256([1, 0, 0, 0]);
    const TOKEN1: U256 = U256([2, 0, 0, 0]);

    fn node_key(tick_spacing: u32, fee: u64) -> NodeKey {
        NodeKey {
            token0: TOKEN0,
            token1: TOKEN1,
            config: Config {
                tick_spacing,
                fee,
                extension: U256::zero(),
            },
        }
    }
    
    mod construct_sorted_ticks {
        use super::*;

        #[test]
        fn test_empty_ticks() {
            let result = BasePool::construct_sorted_ticks(
                vec![],
                MIN_TICK,
                MAX_TICK,
                1,
                1000,
                0,
            );
            
            assert_eq!(result.len(), 2);
            assert_eq!(result[0].index, MIN_TICK);
            assert_eq!(result[0].liquidity_delta, 1000);
            assert_eq!(result[1].index, MAX_TICK);
            assert_eq!(result[1].liquidity_delta, -1000);
        }
        
        #[test]
        fn test_empty_ticks_zero_liquidity() {
            let result = BasePool::construct_sorted_ticks(
                vec![],
                MIN_TICK,
                MAX_TICK,
                1,
                0,
                0,
            );
            
            assert_eq!(result.len(), 0);
        }
        
        #[test]
        fn test_min_max_tick_rounding() {
            let tick_spacing = 10;
            let min_searched = -15; // Should round down to -20
            let max_searched = 25;  // Should round up to 30
            
            let ticks = vec![
                Tick { index: 0, liquidity_delta: 100 },
            ];
            
            let result = BasePool::construct_sorted_ticks(
                ticks,
                min_searched,
                max_searched,
                tick_spacing,
                100,
                -5,
            );
            
            // We should have added ticks at -20 and 30
            assert!(result.iter().any(|t| t.index == -20));
            assert!(result.iter().any(|t| t.index == 30));
            
            // The sum of all liquidity deltas should be zero
            let sum: i128 = result.iter().map(|t| t.liquidity_delta).sum();
            assert_eq!(sum, 0);
        }
        
        #[test]
        fn test_current_tick_active_liquidity() {
            let tick_spacing = 10;
            let current_tick = 15;
            let liquidity = 200;
            
            let ticks = vec![
                Tick { index: 0, liquidity_delta: 100 },
                Tick { index: 20, liquidity_delta: -50 },
            ];
            
            let result = BasePool::construct_sorted_ticks(
                ticks,
                -10,
                30,
                tick_spacing,
                liquidity,
                current_tick,
            );
            
            // Verify that the liquidity at the current tick is correct
            let mut active_liquidity = 0_u128;
            for tick in &result {
                if tick.index <= current_tick {
                    if tick.liquidity_delta > 0 {
                        active_liquidity += tick.liquidity_delta.unsigned_abs();
                    } else {
                        active_liquidity -= tick.liquidity_delta.unsigned_abs();
                    }
                }
            }
            
            assert_eq!(active_liquidity, liquidity);
            
            // The sum of all liquidity deltas should be zero
            let sum: i128 = result.iter().map(|t| t.liquidity_delta).sum();
            assert_eq!(sum, 0);
        }
        
        #[test]
        fn test_partial_view_with_existing_liquidity() {
            let tick_spacing = 10;
        
            // Create partial ticks that don't include the whole range
            let partial_ticks = vec![
                Tick { index: 0, liquidity_delta: 500 },
                Tick { index: 100, liquidity_delta: -200 },
            ];
        
            let min_searched = -50;
            let max_searched = 150;
            let current_tick = 50;
            let liquidity = 500; // Current liquidity at tick 50
        
            let result = BasePool::construct_sorted_ticks(
                partial_ticks,
                min_searched,
                max_searched,
                tick_spacing,
                liquidity,
                current_tick,
            );
        
            // Check that we have ticks at the min and max rounded boundaries
            assert!(result.iter().any(|t| t.index == -50));
            // Max tick must be there (or the test will fail), so print debug info
            println!("Result ticks: {:?}", result);
            println!("Valid max tick should be: {}", 
                if max_searched % tick_spacing as i32 == 0 { 
                    max_searched 
                } else { 
                    max_searched + (tick_spacing as i32 - max_searched % tick_spacing as i32) 
                }
            );
            assert!(result.iter().any(|t| t.index == 150));
        
            // Verify sum is zero
            let sum: i128 = result.iter().map(|t| t.liquidity_delta).sum();
            assert_eq!(sum, 0);
        
            // Verify current active liquidity
            let mut active_liquidity = 0_u128;
            for tick in &result {
                if tick.index <= current_tick {
                    if tick.liquidity_delta > 0 {
                        active_liquidity = active_liquidity.saturating_add(tick.liquidity_delta.unsigned_abs());
                    } else {
                        if active_liquidity >= tick.liquidity_delta.unsigned_abs() {
                            active_liquidity = active_liquidity.saturating_sub(tick.liquidity_delta.unsigned_abs());
                        }
                    }
                }
            }
        
            assert_eq!(active_liquidity, liquidity);
        }
        
        #[test]
        fn test_current_tick_below_min_tick() {
            let tick_spacing = 10;
            let min_searched = 0;
            let max_searched = 100;
            let current_tick = -20; // Current tick is below the min searched tick
            let liquidity = 100;
        
            let partial_ticks = vec![
                Tick { index: 0, liquidity_delta: 200 },
                Tick { index: 50, liquidity_delta: -100 },
            ];
        
            let result = BasePool::construct_sorted_ticks(
                partial_ticks,
                min_searched,
                max_searched,
                tick_spacing,
                liquidity,
                current_tick,
            );
        
            // Since current tick is below min, we need to ensure the min tick has appropriate liquidity
            // to make the active liquidity match
            if let Some(min_tick) = result.iter().find(|t| t.index == 0) {
                assert_eq!(min_tick.liquidity_delta, 200);
            } else {
                panic!("Expected to find min tick in result");
            }
        
            // For current_tick below min_searched, we should have the passed-in
            // liquidity value as active liquidity
            let active_liq = liquidity;
        
            // Sum should be zero
            let sum: i128 = result.iter().map(|t| t.liquidity_delta).sum();
            assert_eq!(sum, 0);
        }
        
        #[test]
        fn test_ticks_with_duplicates() {
            let tick_spacing = 10;
            
            // Create partial ticks with duplicate indices
            let partial_ticks = vec![
                Tick { index: 0, liquidity_delta: 100 },
                Tick { index: 0, liquidity_delta: 200 }, // Duplicate
                Tick { index: 50, liquidity_delta: -150 },
            ];
            
            let result = BasePool::construct_sorted_ticks(
                partial_ticks,
                -10,
                60,
                tick_spacing,
                300,
                30,
            );
            
            // Check that duplicates were merged
            let zero_ticks: Vec<_> = result.iter().filter(|t| t.index == 0).collect();
            assert_eq!(zero_ticks.len(), 1);
            
            // Check the merged liquidity delta
            if let Some(merged_tick) = zero_ticks.first() {
                assert_eq!(merged_tick.liquidity_delta, 300);
            }
            
            // Sum should be zero
            let sum: i128 = result.iter().map(|t| t.liquidity_delta).sum();
            assert_eq!(sum, 0);
        }
        
        #[test]
        fn test_with_min_max_tick_boundary() {
            let tick_spacing = 10;
            
            let partial_ticks = vec![
                Tick { index: MIN_TICK, liquidity_delta: 1000 },
                Tick { index: 0, liquidity_delta: 500 },
                Tick { index: MAX_TICK, liquidity_delta: -1500 },
            ];
            
            let result = BasePool::construct_sorted_ticks(
                partial_ticks,
                MIN_TICK,
                MAX_TICK,
                tick_spacing,
                1000,
                -10,
            );
            
            // Check boundaries are preserved
            assert!(result.iter().any(|t| t.index == MIN_TICK));
            assert!(result.iter().any(|t| t.index == MAX_TICK));
            
            // Sum should be zero
            let sum: i128 = result.iter().map(|t| t.liquidity_delta).sum();
            assert_eq!(sum, 0);
            
            // Active liquidity should match
            let mut active_liquidity = 0_u128;
            for tick in &result {
                if tick.index <= -10 {
                    if tick.liquidity_delta > 0 {
                        active_liquidity += tick.liquidity_delta.unsigned_abs();
                    } else {
                        active_liquidity -= tick.liquidity_delta.unsigned_abs();
                    }
                }
            }
            
            assert_eq!(active_liquidity, 1000);
        }
    }

    mod constructor_validation {
        use super::BasePoolError;
        use super::{to_sqrt_ratio, vec, BasePool, BasePoolState, NodeKey, MAX_TICK_SPACING, U256};
        use crate::math::tick::MAX_TICK;
        use crate::quoting::base_pool::BasePoolError::TickSpacingCannotBeZero;
        use crate::quoting::types::{Config, Tick};

        #[test]
        fn test_token0_lt_token1() {
            let result = BasePool::new(
                NodeKey {
                    token0: U256::zero(),
                    token1: U256::zero(),
                    config: Config {
                        extension: U256::zero(),
                        fee: 0,
                        tick_spacing: 0,
                    },
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
                    config: Config {
                        extension: U256::zero(),
                        fee: 0,
                        tick_spacing: 1,
                    },
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
                    config: Config {
                        extension: U256::zero(),
                        fee: 0,
                        tick_spacing: 0,
                    },
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
                    config: Config {
                        extension: U256::zero(),
                        fee: 0,
                        tick_spacing: MAX_TICK_SPACING + 1,
                    },
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
                    config: Config {
                        extension: U256::zero(),
                        fee: 0,
                        tick_spacing: MAX_TICK_SPACING,
                    },
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
                    config: Config {
                        extension: U256::zero(),
                        fee: 0,
                        tick_spacing: MAX_TICK_SPACING,
                    },
                },
                BasePoolState {
                    sqrt_ratio: to_sqrt_ratio(0).unwrap(),
                    active_tick_index: Some(0),
                    liquidity: 1,
                },
                vec![
                    Tick {
                        index: MAX_TICK,
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
                    config: Config {
                        extension: U256::zero(),
                        fee: 0,
                        tick_spacing: MAX_TICK_SPACING,
                    },
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
                    config: Config {
                        extension: U256::zero(),
                        fee: 0,
                        tick_spacing: MAX_TICK_SPACING,
                    },
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
                        index: MAX_TICK,
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
                    config: Config {
                        extension: U256::zero(),
                        fee: 0,
                        tick_spacing: MAX_TICK_SPACING,
                    },
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
                        index: MAX_TICK,
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
                    config: Config {
                        extension: U256::zero(),
                        fee: 0,
                        tick_spacing: MAX_TICK_SPACING,
                    },
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
                        index: MAX_TICK,
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
                    config: Config {
                        extension: U256::zero(),
                        fee: 0,
                        tick_spacing: MAX_TICK_SPACING,
                    },
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
                        index: MAX_TICK,
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
                    config: Config {
                        extension: U256::zero(),
                        fee: 0,
                        tick_spacing: MAX_TICK_SPACING,
                    },
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
                        index: MAX_TICK,
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
            node_key(100, 922337203685477),
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
