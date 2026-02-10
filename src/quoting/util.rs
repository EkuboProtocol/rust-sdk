use crate::chain::Chain;
use crate::math::tick::approximate_sqrt_ratio_to_tick;
use crate::quoting::types::Tick;
use alloc::vec::Vec;
use num_traits::Zero;
use ruint::aliases::U256;
use thiserror::Error;

// Function to find the nearest initialized tick index.
#[must_use]
pub fn find_nearest_initialized_tick_index(sorted_ticks: &[Tick], tick: i32) -> Option<usize> {
    let mut l = 0usize;
    let mut r = sorted_ticks.len();

    while l < r {
        let mid = usize::midpoint(l, r);
        let mid_tick = sorted_ticks[mid].index;
        if mid_tick <= tick {
            if mid == sorted_ticks.len() - 1 || sorted_ticks[mid + 1].index > tick {
                return Some(mid);
            }
            l = mid;
        } else {
            r = mid;
        }
    }

    None
}

const TICK_BITMAP_STORAGE_OFFSET: i32 = 89421695;

#[must_use]
pub fn approximate_extra_distinct_tick_bitmap_lookups(
    starting_sqrt_ratio: U256,
    ending_sqrt_ratio: U256,
    tick_spacing: u32,
) -> u32 {
    if tick_spacing.is_zero() {
        return 0;
    }

    let tick_spacing = tick_spacing
        .try_into()
        .expect("tick spacing to fit into i32");

    let (start_word, end_word) = (
        bitmap_word_from_sqrt_ratio(starting_sqrt_ratio, tick_spacing),
        bitmap_word_from_sqrt_ratio(ending_sqrt_ratio, tick_spacing),
    );

    start_word.abs_diff(end_word)
}

#[must_use]
pub fn approximate_extra_distinct_time_bitmap_lookups(start_time: u64, end_time: u64) -> u32 {
    u32::try_from(
        bitmap_word_from_time(end_time)
            .checked_sub(bitmap_word_from_time(start_time))
            .expect("start_time to be lte end_time"),
    )
    .expect("time bitmap word diff to fit into u32")
}

fn bitmap_word_from_sqrt_ratio(sqrt_ratio: U256, tick_spacing: i32) -> u32 {
    let tick = approximate_sqrt_ratio_to_tick(sqrt_ratio);
    ((tick / tick_spacing) - i32::from((tick % tick_spacing).is_negative())
        + TICK_BITMAP_STORAGE_OFFSET)
        .cast_unsigned()
        >> 8
}

fn bitmap_word_from_time(time: u64) -> u64 {
    time >> 16
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, Error)]
pub enum ConstructSortedTicksError {
    #[error("current tick is outside of the searched range")]
    CurrentTickOutsideSearchedRange,
    #[error("minimum tick must be less than the max tick")]
    MinTickLessThanMaxTick,
    #[error("tick spacing is invalid")]
    InvalidTickSpacing,
}

/// Converts a partial view of sorted tick data into valid sorted tick data for a pool.
///
/// This function takes partial tick data retrieved from a quote data fetcher lens contract
/// along with min/max tick range, and constructs a valid set of sorted ticks that ensures:
/// 1. All liquidity deltas add up to zero
/// 2. The current liquidity matches the sum of liquidity deltas from `MIN_TICK` to current active tick
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
    if tick_spacing.is_zero() || tick_spacing > C::max_tick_spacing().0 {
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
    for tick in &result {
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
        let has_min_tick = result.first().is_some_and(|t| t.index == valid_min_tick);

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
        let has_max_tick = result.last().is_some_and(|t| t.index == valid_max_tick);

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

pub fn real_last_time(current: u64, stored: u32) -> u64 {
    current - (current.wrapping_sub(stored.into()) & u64::from(u32::MAX))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        chain::{tests::run_for_all_chains, Chain},
        math::tick::to_sqrt_ratio,
        quoting::types::Tick,
    };
    use alloc::vec;

    macro_rules! chain_test {
        ($name:ident, $body:block) => {
            #[test]
            fn $name() {
                run_for_all_chains!(ChainTy, _chain => $body);
            }
        };
    }

    fn make_ticks(entries: &[(i32, i128)]) -> Vec<Tick> {
        entries
            .iter()
            .map(|(index, delta)| Tick {
                index: *index,
                liquidity_delta: *delta,
            })
            .collect()
    }

    #[test]
    fn find_nearest_initialized_tick_index_no_ticks() {
        assert_eq!(find_nearest_initialized_tick_index(&[], 0), None);
    }

    #[test]
    fn find_nearest_initialized_tick_index_single_tick() {
        let ticks = make_ticks(&[(-1, 1)]);
        assert_eq!(find_nearest_initialized_tick_index(&ticks, 0), Some(0));

        let ticks = make_ticks(&[(0, 1)]);
        assert_eq!(find_nearest_initialized_tick_index(&ticks, 0), Some(0));

        let ticks = make_ticks(&[(1, 1)]);
        assert_eq!(find_nearest_initialized_tick_index(&ticks, 0), None);
    }

    #[test]
    fn find_nearest_initialized_tick_index_many_ticks() {
        let sorted_ticks = make_ticks(&[(-100, 0), (-5, 0), (-4, 0), (18, 0), (23, 0), (50, 0)]);

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

    chain_test!(approximate_extra_distinct_bitmap_lookups_word_boundaries, {
        let spacing = 1u32;
        let base = to_sqrt_ratio::<ChainTy>(0).unwrap();
        let same_word = to_sqrt_ratio::<ChainTy>(128).unwrap();
        let next_word = to_sqrt_ratio::<ChainTy>(129).unwrap();

        assert_eq!(
            approximate_extra_distinct_tick_bitmap_lookups(base, same_word, spacing),
            0
        );
        assert_eq!(
            approximate_extra_distinct_tick_bitmap_lookups(base, next_word, spacing),
            1
        );
    });

    chain_test!(approximate_extra_distinct_bitmap_lookups_negative_ticks, {
        let spacing = 1u32;
        let base = to_sqrt_ratio::<ChainTy>(0).unwrap();
        let negative_same_word = to_sqrt_ratio::<ChainTy>(-1).unwrap();
        let negative_prev_word = to_sqrt_ratio::<ChainTy>(-128).unwrap();

        assert_eq!(
            approximate_extra_distinct_tick_bitmap_lookups(base, negative_same_word, spacing),
            0
        );
        assert_eq!(
            approximate_extra_distinct_tick_bitmap_lookups(base, negative_prev_word, spacing),
            1
        );
    });

    #[test]
    fn approximate_extra_distinct_time_bitmap_lookups_word_boundaries() {
        let base = 0_u64;
        let same_word = (1_u64 << 16) - 1;
        let next_word = 1_u64 << 16;

        assert_eq!(
            approximate_extra_distinct_time_bitmap_lookups(base, same_word),
            0
        );
        assert_eq!(
            approximate_extra_distinct_time_bitmap_lookups(base, next_word),
            1
        );
    }

    mod construct_sorted_ticks_tests {
        use super::*;
        use crate::quoting::util::ConstructSortedTicksError;

        fn expected_min_tick<C: Chain>(min_searched: i32, spacing: u32) -> i32 {
            let spacing = spacing as i32;
            let adjusted = ((min_searched - (spacing - 1)) / spacing) * spacing;
            let chain_min = (C::min_tick() / spacing) * spacing;
            Ord::max(adjusted, chain_min)
        }

        fn expected_max_tick<C: Chain>(max_searched: i32, spacing: u32) -> i32 {
            let spacing = spacing as i32;
            let adjusted = ((max_searched + (spacing - 1)) / spacing) * spacing;
            let chain_max = (C::max_tick() / spacing) * spacing;
            Ord::min(adjusted, chain_max)
        }

        chain_test!(empty_ticks, {
            let min_tick = ChainTy::min_tick();
            let max_tick = ChainTy::max_tick();
            let result =
                construct_sorted_ticks::<ChainTy>(vec![], min_tick, max_tick, 1, 1000, 0).unwrap();

            assert_eq!(result.len(), 2);
            assert_eq!(
                (result[0].index, result[0].liquidity_delta),
                (min_tick, 1000)
            );
            assert_eq!(
                (result[1].index, result[1].liquidity_delta),
                (max_tick, -1000)
            );
        });

        chain_test!(empty_ticks_rounded_tick_spacing, {
            let result = construct_sorted_ticks::<ChainTy>(
                vec![],
                ChainTy::min_tick(),
                ChainTy::max_tick(),
                10,
                1000,
                0,
            )
            .unwrap();

            assert_eq!(result.len(), 2);
            let expected_min = expected_min_tick::<ChainTy>(ChainTy::min_tick(), 10);
            let expected_max = expected_max_tick::<ChainTy>(ChainTy::max_tick(), 10);
            assert_eq!(result[0].index, expected_min);
            assert_eq!(result[0].liquidity_delta, 1000);
            assert_eq!(result[1].index, expected_max);
            assert_eq!(result[1].liquidity_delta, -1000);
        });

        chain_test!(empty_ticks_zero_liquidity, {
            let result = construct_sorted_ticks::<ChainTy>(
                vec![],
                ChainTy::min_tick(),
                ChainTy::max_tick(),
                1,
                0,
                0,
            )
            .unwrap();

            assert_eq!(result.len(), 0);
        });

        chain_test!(min_max_tick_rounding, {
            let tick_spacing = 10;
            let min_searched = -15; // Should round down to -20
            let max_searched = 25; // Should round up to 30

            let ticks = vec![Tick {
                index: 0,
                liquidity_delta: 100,
            }];

            let result = construct_sorted_ticks::<ChainTy>(
                ticks,
                min_searched,
                max_searched,
                tick_spacing,
                100,
                -5,
            )
            .unwrap();

            let expected_min = expected_min_tick::<ChainTy>(min_searched, tick_spacing);
            let expected_max = expected_max_tick::<ChainTy>(max_searched, tick_spacing);
            assert!(result.iter().any(|t| t.index == expected_min));
            assert!(result.iter().any(|t| t.index == expected_max));

            // The sum of all liquidity deltas should be zero
            let sum: i128 = result.iter().map(|t| t.liquidity_delta).sum();
            assert_eq!(sum, 0);
        });

        chain_test!(current_tick_active_liquidity, {
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

            let result = construct_sorted_ticks::<ChainTy>(
                ticks,
                -10,
                30,
                tick_spacing,
                liquidity,
                current_tick,
            )
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
        });

        chain_test!(partial_view_with_existing_liquidity, {
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

            let result = construct_sorted_ticks::<ChainTy>(
                partial_ticks,
                min_searched,
                max_searched,
                tick_spacing,
                liquidity,
                current_tick,
            )
            .unwrap();

            let first = result.first().unwrap();
            let last = result.last().unwrap();
            assert_eq!(
                first.index,
                expected_min_tick::<ChainTy>(min_searched, tick_spacing)
            );
            assert_eq!(first.liquidity_delta, 250);
            assert_eq!(
                last.index,
                expected_max_tick::<ChainTy>(max_searched, tick_spacing)
            );
            assert_eq!(last.liquidity_delta, -550);

            // Verify sum is zero
            let sum: i128 = result.iter().map(|t| t.liquidity_delta).sum();
            assert_eq!(sum, 0);
        });

        chain_test!(current_tick_below_min_tick, {
            let tick_spacing = 10;
            let min_searched = ChainTy::min_tick();
            let max_searched = ChainTy::min_tick() + 100;
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
                construct_sorted_ticks::<ChainTy>(
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
        });

        chain_test!(with_min_max_tick_boundary, {
            let tick_spacing = 10;
            let min_tick = ChainTy::min_tick();
            let max_tick = ChainTy::max_tick();

            let partial_ticks = vec![
                Tick {
                    index: min_tick,
                    liquidity_delta: 1000,
                },
                Tick {
                    index: 0,
                    liquidity_delta: 500,
                },
                Tick {
                    index: max_tick,
                    liquidity_delta: -1500,
                },
            ];

            let result = construct_sorted_ticks::<ChainTy>(
                partial_ticks,
                min_tick,
                max_tick,
                tick_spacing,
                1000,
                -10,
            )
            .unwrap();

            // Check boundaries are preserved
            assert!(result.iter().any(|t| t.index == min_tick));
            assert!(result.iter().any(|t| t.index == max_tick));

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
        });
    }
}
