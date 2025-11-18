use crate::quoting::types::Tick;
use crate::{
    chain::Chain,
    math::uint::{u256_to_float_base_x128, U256},
};
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

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum ConstructSortedTicksError {
    CurrentTickOutsideSearchedRange,
    MinTickLessThanMaxTick,
    InvalidTickSpacing,
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
/// * `current_tick` - The current tick of the pool, must be between min and max tick searched
pub fn construct_sorted_ticks<C: Chain>(
    partial_ticks: Vec<Tick>,
    min_tick_searched: i32,
    max_tick_searched: i32,
    tick_spacing: u32,
    liquidity: u128,
    current_tick: i32,
) -> Result<Vec<Tick>, ConstructSortedTicksError> {
    if current_tick < min_tick_searched || current_tick > max_tick_searched {
        return Err(ConstructSortedTicksError::CurrentTickOutsideSearchedRange);
    }
    if min_tick_searched > max_tick_searched {
        return Err(ConstructSortedTicksError::MinTickLessThanMaxTick);
    }
    if tick_spacing.is_zero() || tick_spacing > C::max_tick_spacing() {
        return Err(ConstructSortedTicksError::InvalidTickSpacing);
    }

    let spacing_i32 = tick_spacing as i32;

    let valid_min_tick = (((min_tick_searched - (spacing_i32 - 1)) / spacing_i32) * spacing_i32)
        .max((C::min_tick() / spacing_i32) * spacing_i32);

    let valid_max_tick = (((max_tick_searched + (spacing_i32 - 1)) / spacing_i32) * spacing_i32)
        .min((C::max_tick() / spacing_i32) * spacing_i32);

    // Sort and deduplicate ticks
    let mut result = partial_ticks.clone();
    result.sort_by_key(|tick| tick.index);

    // Calculate sum of liquidity for ticks at or below current_tick
    let mut liquidity_sum = 0_i128;

    // First pass: find active tick index and calculate running sum
    for tick in result.iter() {
        if tick.index <= current_tick {
            liquidity_sum += tick.liquidity_delta;
        } else {
            break;
        }
    }

    // Calculate min tick delta (difference between expected and actual liquidity)
    let min_tick_liquidity_delta = (liquidity as i128) - liquidity_sum;

    // Calculate max tick delta (ensure all deltas sum to zero)
    // For this, we need to sum all tick deltas and negate the result plus min_delta
    let all_delta_sum: i128 = result.iter().map(|t| t.liquidity_delta).sum();
    let max_tick_liquidity_delta = -(min_tick_liquidity_delta + all_delta_sum);

    if min_tick_liquidity_delta != 0 {
        // Check if we already have min/max boundary ticks
        let has_min_tick = result.first().map_or(false, |t| t.index == valid_min_tick);

        // Add or update min boundary tick
        if has_min_tick {
            result.first_mut().unwrap().liquidity_delta += min_tick_liquidity_delta;
        } else {
            result.insert(
                0,
                Tick {
                    index: valid_min_tick,
                    liquidity_delta: min_tick_liquidity_delta,
                },
            );
        }
    }

    if max_tick_liquidity_delta != 0 {
        let has_max_tick = result.last().map_or(false, |t| t.index == valid_max_tick);

        // Add or update max boundary tick
        if has_max_tick {
            // Update existing tick
            result.last_mut().unwrap().liquidity_delta += max_tick_liquidity_delta;
        } else {
            // Add new max boundary tick
            result.push(Tick {
                index: valid_max_tick,
                liquidity_delta: max_tick_liquidity_delta,
            });
        }
    }

    Ok(result)
}

#[cfg(test)]
mod tests {
    use crate::math::tick::{MAX_SQRT_RATIO, MAX_TICK, MIN_SQRT_RATIO, MIN_TICK};
    use crate::math::uint::U256;
    use crate::quoting::types::Tick;
    use crate::quoting::util::find_nearest_initialized_tick_index;
    use crate::quoting::util::{
        approximate_number_of_tick_spacings_crossed, construct_sorted_ticks,
        u256_to_float_base_x128,
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
        use crate::quoting::util::ConstructSortedTicksError;

        #[test]
        fn test_empty_ticks() {
            let result = construct_sorted_ticks(vec![], MIN_TICK, MAX_TICK, 1, 1000, 0).unwrap();

            assert_eq!(result.len(), 2);
            assert_eq!(result[0].index, MIN_TICK);
            assert_eq!(result[0].liquidity_delta, 1000);
            assert_eq!(result[1].index, MAX_TICK);
            assert_eq!(result[1].liquidity_delta, -1000);
        }

        #[test]
        fn test_empty_ticks_rounded_tick_spacing() {
            let result = construct_sorted_ticks(vec![], MIN_TICK, MAX_TICK, 10, 1000, 0).unwrap();

            assert_eq!(result.len(), 2);
            assert_eq!(result[0].index, -88722830);
            assert_eq!(result[0].liquidity_delta, 1000);
            assert_eq!(result[1].index, 88722830);
            assert_eq!(result[1].liquidity_delta, -1000);
        }

        #[test]
        fn test_empty_ticks_zero_liquidity() {
            let result = construct_sorted_ticks(vec![], MIN_TICK, MAX_TICK, 1, 0, 0).unwrap();

            assert_eq!(result.len(), 0);
        }

        #[test]
        fn test_min_max_tick_rounding() {
            let tick_spacing = 10;
            let min_searched = -15; // Should round down to -20
            let max_searched = 25; // Should round up to 30

            let ticks = vec![Tick {
                index: 0,
                liquidity_delta: 100,
            }];

            let result =
                construct_sorted_ticks(ticks, min_searched, max_searched, tick_spacing, 100, -5)
                    .unwrap();

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
                Tick {
                    index: 0,
                    liquidity_delta: 100,
                },
                Tick {
                    index: 20,
                    liquidity_delta: -50,
                },
            ];

            let result =
                construct_sorted_ticks(ticks, -10, 30, tick_spacing, liquidity, current_tick)
                    .unwrap();

            // Verify that the liquidity at the current tick is correct
            let mut active_liquidity = 0_u128;
            for tick in &result {
                if tick.index <= current_tick {
                    if tick.liquidity_delta > 0 {
                        active_liquidity =
                            active_liquidity.saturating_add(tick.liquidity_delta.unsigned_abs());
                    } else if active_liquidity >= tick.liquidity_delta.unsigned_abs() {
                        active_liquidity =
                            active_liquidity.saturating_sub(tick.liquidity_delta.unsigned_abs());
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
                Tick {
                    index: 0,
                    liquidity_delta: 500,
                },
                Tick {
                    index: 100,
                    liquidity_delta: -200,
                },
            ];

            let min_searched = -45;
            let max_searched = 145;
            let current_tick = 52;
            let liquidity = 750; // Current liquidity at tick 50

            let result = construct_sorted_ticks(
                partial_ticks,
                min_searched,
                max_searched,
                tick_spacing,
                liquidity,
                current_tick,
            )
            .unwrap();

            // Check that we have ticks at the min and max boundaries
            assert_eq!(
                result.first().unwrap(),
                &Tick {
                    index: -50,
                    liquidity_delta: 250
                }
            );
            assert_eq!(
                result.last().unwrap(),
                &Tick {
                    index: 150,
                    liquidity_delta: -550
                }
            );

            // Verify sum is zero
            let sum: i128 = result.iter().map(|t| t.liquidity_delta).sum();
            assert_eq!(sum, 0);
        }

        #[test]
        fn test_current_tick_below_min_tick() {
            let tick_spacing = 10;
            let min_searched = 0;
            let max_searched = 100;
            let current_tick = -20; // Current tick is below the min searched tick
            let liquidity = 100;

            let partial_ticks = vec![
                Tick {
                    index: 0,
                    liquidity_delta: 200,
                },
                Tick {
                    index: 50,
                    liquidity_delta: -100,
                },
            ];

            assert_eq!(
                construct_sorted_ticks(
                    partial_ticks,
                    min_searched,
                    max_searched,
                    tick_spacing,
                    liquidity,
                    current_tick,
                )
                .unwrap_err(),
                ConstructSortedTicksError::CurrentTickOutsideSearchedRange
            );
        }

        #[test]
        fn test_with_min_max_tick_boundary() {
            let tick_spacing = 10;

            let partial_ticks = vec![
                Tick {
                    index: MIN_TICK,
                    liquidity_delta: 1000,
                },
                Tick {
                    index: 0,
                    liquidity_delta: 500,
                },
                Tick {
                    index: MAX_TICK,
                    liquidity_delta: -1500,
                },
            ];

            let result =
                construct_sorted_ticks(partial_ticks, MIN_TICK, MAX_TICK, tick_spacing, 1000, -10)
                    .unwrap();

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
                        active_liquidity =
                            active_liquidity.saturating_add(tick.liquidity_delta.unsigned_abs());
                    } else if active_liquidity >= tick.liquidity_delta.unsigned_abs() {
                        active_liquidity =
                            active_liquidity.saturating_sub(tick.liquidity_delta.unsigned_abs());
                    }
                }
            }

            assert_eq!(active_liquidity, 1000);
        }
    }
}
