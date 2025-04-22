use crate::math::uint::U256;
use crate::quoting::types::Tick;
use crate::math::tick::{MIN_TICK, MAX_TICK};
use alloc::vec::Vec;

// Function to find the nearest initialized tick index.
pub fn find_nearest_initialized_tick_index(sorted_ticks: &[Tick], tick: i32) -> Option<usize> {
    let mut l = 0usize;
    let mut r = sorted_ticks.len();

    while l < r {
        let mid = (l + r) / 2;
        let mid_tick = sorted_ticks[mid].index;
        if mid_tick <= tick {
            if mid == sorted_ticks.len() - 1 || sorted_ticks[mid + 1].index > tick {
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

const LOG_BASE_SQRT_TICK_SIZE: f64 = 4.9999975000016666654166676666658333340476184226196031741031750577196410537756684185262518589393595459766211405607685305832e-7;

pub fn u256_to_float_base_x128(x128: U256) -> f64 {
    x128.0[0] as f64 / 340282366920938463463374607431768211456f64
        + (x128.0[1] as f64 / 18446744073709551616f64)
        + x128.0[2] as f64
        + (x128.0[3] as f64 * 18446744073709551616f64)
}

pub fn approximate_number_of_tick_spacings_crossed(
    starting_sqrt_ratio: U256,
    ending_sqrt_ratio: U256,
    tick_spacing: u32,
) -> u32 {
    if tick_spacing == 0 {
        return 0;
    }

    let start: f64 = u256_to_float_base_x128(starting_sqrt_ratio);
    let end: f64 = u256_to_float_base_x128(ending_sqrt_ratio);
    let ticks_crossed = ((start.ln() - end.ln()).abs() / LOG_BASE_SQRT_TICK_SIZE) as u32;
    ticks_crossed / tick_spacing
}

/// Converts a partial view of sorted tick data into valid sorted tick data for a pool.
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
        // For empty input, create a full range of ticks if there's liquidity
        if liquidity > 0 {
            return alloc::vec![
                Tick {
                    index: MIN_TICK,
                    liquidity_delta: liquidity as i128,
                },
                Tick {
                    index: MAX_TICK,
                    liquidity_delta: -(liquidity as i128),
                },
            ];
        }
        return Vec::new();
    }

    let spacing_i32 = tick_spacing as i32;
    
    // Round min/max ticks to valid ticks (min down, max up)
    let valid_min_tick = if min_tick_searched == MIN_TICK {
        MIN_TICK
    } else {
        // Round down to nearest multiple of tick spacing
        let remainder = min_tick_searched % spacing_i32;
        if remainder < 0 {
            min_tick_searched - (spacing_i32 + remainder)
        } else {
            min_tick_searched - remainder
        }
    };
    
    let valid_max_tick = if max_tick_searched == MAX_TICK {
        MAX_TICK
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
    let mut liquidity_delta_sum: i128 = 0;
    for tick in &result {
        liquidity_delta_sum = liquidity_delta_sum.saturating_add(tick.liquidity_delta);
    }
    
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
        let min_liquidity_delta = calculate_min_liquidity_delta(
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
    
    // Special case: preserve MIN_TICK/MAX_TICK if they exist in the input
    let has_min_tick = result.iter().any(|t| t.index == MIN_TICK);
    let has_max_tick = result.iter().any(|t| t.index == MAX_TICK);
    
    // First check if min tick needs to be added (but don't override MIN_TICK if it exists)
    if !has_min_tick && !result.iter().any(|t| t.index == valid_min_tick) {
        let min_liquidity_delta = calculate_min_liquidity_delta(
            liquidity, 
            active_liquidity, 
            liquidity_delta_sum,
            current_tick <= valid_min_tick,
        );
        
        result.push(Tick {
            index: valid_min_tick,
            liquidity_delta: min_liquidity_delta,
        });
    }
    
    // Recalculate the liquidity sum for max tick calculation
    liquidity_delta_sum = 0;
    for tick in &result {
        liquidity_delta_sum += tick.liquidity_delta; // No saturating_add to preserve negative values
    }
    
    // Then ensure max tick is added (but don't override MAX_TICK if it exists)
    if !has_max_tick {
        let max_liquidity_delta = -liquidity_delta_sum;
        
        // Check if valid max tick exists, update it or add it
        let valid_max_tick_exists = result.iter().any(|t| t.index == valid_max_tick);
        
        if valid_max_tick_exists {
            for tick in result.iter_mut() {
                if tick.index == valid_max_tick {
                    tick.liquidity_delta = max_liquidity_delta;
                    break;
                }
            }
        } else {
            result.push(Tick {
                index: valid_max_tick,
                liquidity_delta: max_liquidity_delta,
            });
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

/// Calculates the appropriate liquidity delta for the min tick
fn calculate_min_liquidity_delta(
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

#[cfg(test)]
mod tests {
    use crate::math::tick::{MAX_SQRT_RATIO, MIN_SQRT_RATIO};
    use crate::math::uint::U256;
    use crate::quoting::types::Tick;
    use crate::quoting::util::find_nearest_initialized_tick_index;
    use crate::quoting::util::{
        approximate_number_of_tick_spacings_crossed, u256_to_float_base_x128,
    };
    use alloc::vec;

    #[test]
    fn test_find_nearest_initialized_tick_index_no_ticks() {
        assert_eq!(find_nearest_initialized_tick_index(&vec![], 0), None);
    }

    #[test]
    fn test_find_nearest_initialized_tick_index_one_tick_less_than() {
        assert_eq!(
            find_nearest_initialized_tick_index(
                &vec![Tick {
                    index: -1,
                    liquidity_delta: 1,
                }],
                0
            ),
            Some(0)
        );
    }

    #[test]
    fn test_find_nearest_initialized_tick_index_one_tick_equal_to() {
        assert_eq!(
            find_nearest_initialized_tick_index(
                &vec![Tick {
                    index: 0,
                    liquidity_delta: 1,
                }],
                0
            ),
            Some(0)
        );
    }

    #[test]
    fn test_find_nearest_initialized_tick_index_one_tick_greater_than() {
        assert_eq!(
            find_nearest_initialized_tick_index(
                &vec![Tick {
                    index: 1,
                    liquidity_delta: 1,
                }],
                0
            ),
            None
        );
    }

    #[test]
    fn test_find_nearest_initialized_tick_index_many_ticks() {
        let sorted_ticks = vec![
            Tick {
                index: -100,
                liquidity_delta: 0,
            },
            Tick {
                index: -5,
                liquidity_delta: 0,
            },
            Tick {
                index: -4,
                liquidity_delta: 0,
            },
            Tick {
                index: 18,
                liquidity_delta: 0,
            },
            Tick {
                index: 23,
                liquidity_delta: 0,
            },
            Tick {
                index: 50,
                liquidity_delta: 0,
            },
        ];

        assert_eq!(
            find_nearest_initialized_tick_index(&sorted_ticks, -101),
            None
        );
        assert_eq!(
            find_nearest_initialized_tick_index(&sorted_ticks, -100),
            Some(0)
        );
        assert_eq!(
            find_nearest_initialized_tick_index(&sorted_ticks, -99),
            Some(0)
        );
        assert_eq!(
            find_nearest_initialized_tick_index(&sorted_ticks, -6),
            Some(0)
        );
        assert_eq!(
            find_nearest_initialized_tick_index(&sorted_ticks, -5),
            Some(1)
        );
        assert_eq!(
            find_nearest_initialized_tick_index(&sorted_ticks, -4),
            Some(2)
        );
        assert_eq!(
            find_nearest_initialized_tick_index(&sorted_ticks, -3),
            Some(2)
        );
        assert_eq!(
            find_nearest_initialized_tick_index(&sorted_ticks, 0),
            Some(2)
        );
        assert_eq!(
            find_nearest_initialized_tick_index(&sorted_ticks, 17),
            Some(2)
        );
        assert_eq!(
            find_nearest_initialized_tick_index(&sorted_ticks, 18),
            Some(3)
        );
        assert_eq!(
            find_nearest_initialized_tick_index(&sorted_ticks, 19),
            Some(3)
        );
        assert_eq!(
            find_nearest_initialized_tick_index(&sorted_ticks, 22),
            Some(3)
        );
        assert_eq!(
            find_nearest_initialized_tick_index(&sorted_ticks, 23),
            Some(4)
        );
        assert_eq!(
            find_nearest_initialized_tick_index(&sorted_ticks, 24),
            Some(4)
        );
        assert_eq!(
            find_nearest_initialized_tick_index(&sorted_ticks, 49),
            Some(4)
        );
        assert_eq!(
            find_nearest_initialized_tick_index(&sorted_ticks, 50),
            Some(5)
        );
        assert_eq!(
            find_nearest_initialized_tick_index(&sorted_ticks, 51),
            Some(5)
        );
    }

    #[test]
    fn test_approximate_number_of_tick_spacings_crossed_for_doubling() {
        assert_eq!(
            approximate_number_of_tick_spacings_crossed(MIN_SQRT_RATIO, MIN_SQRT_RATIO * 2, 0),
            0
        );
        // 2x sqrt ratio increase ~= 4x price increase
        assert_eq!(
            approximate_number_of_tick_spacings_crossed(U256([0, 0, 1, 0]), U256([0, 0, 2, 0]), 1),
            1386295
        );
        assert_eq!(
            approximate_number_of_tick_spacings_crossed(MIN_SQRT_RATIO, MIN_SQRT_RATIO * 2, 1),
            1386295
        );
        assert_eq!(
            approximate_number_of_tick_spacings_crossed(MAX_SQRT_RATIO, MAX_SQRT_RATIO / 2, 1),
            1386295
        );
    }

    #[test]
    fn test_approximate_number_of_tick_spacings_crossed_for_doubling_big_tick_spacing() {
        // 2x sqrt ratio increase ~= 4x price increase
        assert_eq!(
            approximate_number_of_tick_spacings_crossed(U256([0, 0, 1, 0]), U256([0, 0, 2, 0]), 5),
            277259
        );
        assert_eq!(
            approximate_number_of_tick_spacings_crossed(MIN_SQRT_RATIO, MIN_SQRT_RATIO * 2, 3),
            462098
        );
        assert_eq!(
            approximate_number_of_tick_spacings_crossed(MAX_SQRT_RATIO, MAX_SQRT_RATIO / 2, 200),
            6931
        );
    }

    #[test]
    fn test_u256_to_fraction() {
        assert_eq!(
            u256_to_float_base_x128(U256([16403144882676588163, 1525053501570699700, 35, 0])),
            35.08267331597798
        );
        assert_eq!(
            u256_to_float_base_x128(U256([123456, 0, 0, 0])),
            3.628045764377908e-34
        );
        assert_eq!(
            u256_to_float_base_x128(U256([0, 123456, 0, 0])),
            6.692563170318522e-15
        );
        assert_eq!(u256_to_float_base_x128(U256([0, 0, 123456, 0])), 123456.0);
        assert_eq!(
            u256_to_float_base_x128(U256([0, 0, 0, 123456])),
            2.2773612363638864e24
        );
    }
}
