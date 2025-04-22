use crate::math::uint::U256;
use crate::quoting::types::Tick;
use crate::math::tick::{MIN_TICK, MAX_TICK};
use alloc::vec::Vec;
use num_traits::Zero;

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
    // Handle empty ticks case
    if partial_ticks.is_empty() {
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

    // Create result vector with the input ticks
    let mut result = partial_ticks.clone();
    
    // Ensure ticks are sorted
    result.sort_by_key(|tick| tick.index);
    
    // Following the TypeScript implementation reference:
    let mut active_tick_index = None;
    let mut current_liquidity: i128 = 0;

    // This will be the liquidity we add to the min tick (liquidity_delta_min)
    let mut min_tick_liquidity_delta = 0i128;
    
    // Find the active tick and compute liquidity delta for min tick
    for (i, tick) in result.iter().enumerate() {
        // If we haven't found the active tick yet and this tick is greater than current tick
        if active_tick_index.is_none() && tick.index > current_tick {
            // The active tick is the previous tick (if there was one)
            active_tick_index = if i == 0 { None } else { Some(i - 1) };
            
            // The difference between the expected liquidity and the current sum is what 
            // needs to be added at the min tick
            min_tick_liquidity_delta = (liquidity as i128) - current_liquidity;
            
            // Reset to the actual liquidity to track what needs to be added at max tick
            current_liquidity = liquidity as i128;
        }
        
        // Add this tick's delta to our running total
        current_liquidity += tick.liquidity_delta;
    }
    
    // If we didn't find an active tick (all ticks were <= current_tick)
    if active_tick_index.is_none() {
        active_tick_index = if !result.is_empty() { Some(result.len() - 1) } else { None };
        min_tick_liquidity_delta = (liquidity as i128) - current_liquidity;
        current_liquidity = liquidity as i128;
    }
    
    // Add the min tick if it's not already in the result
    let min_tick = min_tick_searched;
    if !result.iter().any(|t| t.index == min_tick) {
        result.push(Tick {
            index: min_tick,
            liquidity_delta: min_tick_liquidity_delta,
        });
    } else {
        // Update the existing min tick
        for tick in result.iter_mut() {
            if tick.index == min_tick {
                tick.liquidity_delta = min_tick_liquidity_delta;
                break;
            }
        }
    }
    
    // Add the max tick if it's not already in the result
    let max_tick = max_tick_searched;
    
    // Max tick gets the negative of the current liquidity to balance everything
    let max_tick_liquidity_delta = -current_liquidity;
    
    if !result.iter().any(|t| t.index == max_tick) {
        result.push(Tick {
            index: max_tick,
            liquidity_delta: max_tick_liquidity_delta,
        });
    } else {
        // Update the existing max tick
        for tick in result.iter_mut() {
            if tick.index == max_tick {
                tick.liquidity_delta = max_tick_liquidity_delta;
                break;
            }
        }
    }
    
    // Sort again after adding/updating min and max ticks
    result.sort_by_key(|tick| tick.index);
    
    // Merge duplicate ticks
    let mut i = 0;
    while i + 1 < result.len() {
        if result[i].index == result[i + 1].index {
            result[i].liquidity_delta += result[i + 1].liquidity_delta;
            result.remove(i + 1);
        } else {
            i += 1;
        }
    }
    
    // Remove ticks with zero liquidity delta
    result.retain(|tick| tick.liquidity_delta != 0);
    
    result
}


#[cfg(test)]
mod tests {
    use crate::math::tick::{MAX_SQRT_RATIO, MIN_SQRT_RATIO, MIN_TICK, MAX_TICK};
    use crate::math::uint::U256;
    use crate::quoting::types::Tick;
    use crate::quoting::util::find_nearest_initialized_tick_index;
    use crate::quoting::util::{
        approximate_number_of_tick_spacings_crossed, u256_to_float_base_x128, construct_sorted_ticks,
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
    
    mod construct_sorted_ticks_tests {
        use super::*;

        #[test]
        fn test_empty_ticks() {
            let result = construct_sorted_ticks(
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
            let result = construct_sorted_ticks(
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
            
            let result = construct_sorted_ticks(
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
            
            let result = construct_sorted_ticks(
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
                        active_liquidity = active_liquidity.saturating_add(tick.liquidity_delta.unsigned_abs());
                    } else if active_liquidity >= tick.liquidity_delta.unsigned_abs() {
                        active_liquidity = active_liquidity.saturating_sub(tick.liquidity_delta.unsigned_abs());
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
        
            let result = construct_sorted_ticks(
                partial_ticks,
                min_searched,
                max_searched,
                tick_spacing,
                liquidity,
                current_tick,
            );
        
            // Check that we have ticks at the min and max rounded boundaries
            assert!(result.iter().any(|t| t.index == -50));
            assert!(result.iter().any(|t| t.index == 150));
        
            // Verify sum is zero
            let sum: i128 = result.iter().map(|t| t.liquidity_delta).sum();
            assert_eq!(sum, 0);
            
            // Specifically check the value of the tick at 150
            for tick in &result {
                if tick.index == 150 {
                    assert_eq!(tick.liquidity_delta, 0, "Tick at 150 should have liquidity_delta of 0");
                }
            }
        
            // Verify current active liquidity
            let mut active_liquidity = 0_u128;
            for tick in &result {
                if tick.index <= current_tick {
                    if tick.liquidity_delta > 0 {
                        active_liquidity = active_liquidity.saturating_add(tick.liquidity_delta.unsigned_abs());
                    } else if active_liquidity >= tick.liquidity_delta.unsigned_abs() {
                        active_liquidity = active_liquidity.saturating_sub(tick.liquidity_delta.unsigned_abs());
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
        
            let result = construct_sorted_ticks(
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
            
            let result = construct_sorted_ticks(
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
            
            let result = construct_sorted_ticks(
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
                        active_liquidity = active_liquidity.saturating_add(tick.liquidity_delta.unsigned_abs());
                    } else if active_liquidity >= tick.liquidity_delta.unsigned_abs() {
                        active_liquidity = active_liquidity.saturating_sub(tick.liquidity_delta.unsigned_abs());
                    }
                }
            }
            
            assert_eq!(active_liquidity, 1000);
        }
    }
}
