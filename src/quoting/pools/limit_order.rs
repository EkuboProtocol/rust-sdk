use crate::quoting::{
    pools::concentrated::{ConcentratedPoolConstructionError, ConcentratedPoolQuoteError},
    types::TokenAmount,
    util::{approximate_extra_distinct_tick_bitmap_lookups, find_nearest_initialized_tick_index},
};
use crate::quoting::{
    pools::concentrated::{ConcentratedPoolResources, ConcentratedPoolTypeConfig},
    types::PoolState,
};
use crate::{chain::starknet::Starknet, math::swap::is_price_increasing};
use crate::{chain::Chain, quoting::pools::concentrated::ConcentratedPoolState};
use crate::{math::tick::to_sqrt_ratio, quoting::types::PoolConfig};
use crate::{
    private,
    quoting::{
        pools::concentrated::{ConcentratedPool, TickSpacing},
        types::{Pool, PoolKey, Quote, QuoteParams, Tick},
    },
};
use alloc::vec::Vec;
use derive_more::{Add, AddAssign, Sub, SubAssign};
use num_traits::Zero;
use ruint::aliases::U256;
use starknet_types_core::felt::Felt;
use thiserror::Error;

/// Limit order pool built on top of a concentrated pool.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct LimitOrderPool {
    /// Underlying concentrated pool.
    concentrated_pool: ConcentratedPool<Starknet>,
}

/// Unique identifier for a [`LimitOrderPool`].
pub type LimitOrderPoolKey =
    PoolKey<<Starknet as Chain>::Address, <Starknet as Chain>::Fee, ConcentratedPoolTypeConfig>;
/// Pool configuration for a [`LimitOrderPool`].
pub type LimitOrderPoolConfig =
    PoolConfig<<Starknet as Chain>::Address, <Starknet as Chain>::Fee, ConcentratedPoolTypeConfig>;
/// [`ConcentratedPoolQuoteError`] re-exported with a pool-specific name.
pub type LimitOrderPoolQuoteError = ConcentratedPoolQuoteError;

/// Tick spacing required for limit order pools.
pub const LIMIT_ORDER_TICK_SPACING: i32 = 128;
/// Double tick spacing used when validating neighboring ticks.
pub const DOUBLE_LIMIT_ORDER_TICK_SPACING: i32 = 2i32 * LIMIT_ORDER_TICK_SPACING;

/// Price/liquidity state for a [`LimitOrderPool`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct LimitOrderPoolState {
    /// State of the underlying concentrated pool.
    pub concentrated_pool_state: ConcentratedPoolState,
    /// Minimum and maximum active tick indices observed since the last tick refresh.
    pub tick_indices_reached: Option<(Option<usize>, Option<usize>)>,
}

/// Resources consumed during limit order quote execution.
#[derive(Clone, Copy, Default, Debug, PartialEq, Eq, Hash, Add, AddAssign, Sub, SubAssign)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct LimitOrderStandalonePoolResources {
    /// Number of limit orders pulled (ticks crossed that were position boundaries).
    pub orders_pulled: u32,
}

/// Resources consumed during limit order quote execution.
#[derive(Clone, Copy, Default, Debug, PartialEq, Eq, Hash, Add, AddAssign, Sub, SubAssign)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct LimitOrderPoolResources {
    /// Resources consumed by the underlying concentrated pool.
    pub concentrated: ConcentratedPoolResources,
    /// Resources added by the limit order wrapper.
    pub limit_order: LimitOrderStandalonePoolResources,
}

/// Errors that can occur when constructing a [`LimitOrderPool`].
#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, Error)]
pub enum LimitOrderPoolConstructionError {
    #[error("concentrated pool error")]
    ConcentratedPoolConstructionError(#[from] ConcentratedPoolConstructionError),
    #[error("all ticks must have at least one neighbor")]
    AllTicksMustHaveNeighbor,
    #[error("last tick has no neighbor")]
    LastTickHasNoNeighbor,
}

impl LimitOrderPool {
    pub fn new(
        token0: Felt,
        token1: Felt,
        extension: Felt,
        sqrt_ratio: U256,
        tick: i32,
        liquidity: u128,
        sorted_ticks: Vec<Tick>,
    ) -> Result<Self, LimitOrderPoolConstructionError> {
        // check that each tick has at least 1 neighbor within 128 ticks
        let active_tick_index = find_nearest_initialized_tick_index(&sorted_ticks, tick);
        let mut maybe_last: Option<(&Tick, usize)> = None;
        for t in &sorted_ticks {
            if let Some((last, count)) = maybe_last {
                if t.index == last.index + LIMIT_ORDER_TICK_SPACING {
                    maybe_last = Some((t, count + 1));
                } else {
                    if count.is_zero() {
                        return Err(LimitOrderPoolConstructionError::AllTicksMustHaveNeighbor);
                    }
                    maybe_last = Some((t, 0));
                }
            } else {
                maybe_last = Some((t, 0));
            }
        }
        if maybe_last.is_some_and(|(_, count)| count.is_zero()) {
            return Err(LimitOrderPoolConstructionError::LastTickHasNoNeighbor);
        }

        Ok(LimitOrderPool {
            concentrated_pool: ConcentratedPool::new(
                PoolKey {
                    token0,
                    token1,
                    config: PoolConfig {
                        fee: 0,
                        pool_type_config: TickSpacing(LIMIT_ORDER_TICK_SPACING.unsigned_abs()),
                        extension,
                    },
                },
                ConcentratedPoolState {
                    sqrt_ratio,
                    liquidity,
                    active_tick_index,
                },
                sorted_ticks,
            )
            .map_err(LimitOrderPoolConstructionError::ConcentratedPoolConstructionError)?,
        })
    }

    pub fn concentrated_pool(&self) -> &ConcentratedPool<Starknet> {
        &self.concentrated_pool
    }
}

impl AsRef<ConcentratedPool<Starknet>> for LimitOrderPool {
    fn as_ref(&self) -> &ConcentratedPool<Starknet> {
        self.concentrated_pool()
    }
}

impl AsRef<Self> for LimitOrderPool {
    fn as_ref(&self) -> &Self {
        self
    }
}

impl Pool for LimitOrderPool {
    type Address = <Starknet as Chain>::Address;
    type Fee = <Starknet as Chain>::Fee;
    type Resources = LimitOrderPoolResources;
    type State = LimitOrderPoolState;
    type QuoteError = LimitOrderPoolQuoteError;
    type Meta = ();
    type PoolTypeConfig = ConcentratedPoolTypeConfig;

    fn key(&self) -> LimitOrderPoolKey {
        self.concentrated_pool.key()
    }

    fn state(&self) -> Self::State {
        LimitOrderPoolState {
            concentrated_pool_state: self.concentrated_pool.state(),
            tick_indices_reached: None,
        }
    }

    fn quote(
        &self,
        params: QuoteParams<Self::Address, Self::State, Self::Meta>,
    ) -> Result<Quote<Self::Resources, Self::State>, Self::QuoteError> {
        let initial_state = params.override_state.unwrap_or_else(|| self.state());
        let sorted_ticks = self.concentrated_pool.ticks();

        let is_increasing = is_price_increasing(
            params.token_amount.amount,
            params.token_amount.token == self.key().token1,
        );

        let mut calculated_amount = 0;
        let mut consumed_amount = 0;
        let mut fees_paid = 0;
        let mut concentrated_pool_resources = ConcentratedPoolResources::default();
        let mut concentrated_pool_state = initial_state.concentrated_pool_state;

        let active_tick_index = concentrated_pool_state.active_tick_index;

        // if we need to skip one or more already pulled orders, this contains the tick index of the next unpulled order
        let next_unpulled_order_tick_index_after_skip = initial_state
            .tick_indices_reached
            .and_then(|(lower, upper)| {
                if is_increasing {
                    (active_tick_index != upper).then(|| {
                        Some(upper.map_or(
                            0, // safe because active_tick_index != upper
                            |upper| {
                                if (sorted_ticks[upper].index % DOUBLE_LIMIT_ORDER_TICK_SPACING)
                                    .is_zero()
                                {
                                    upper
                                } else {
                                    // upper has been pulled as part of a decrease in price, so select the next tick index
                                    Ord::min(upper + 1, sorted_ticks.len() - 1)
                                }
                            },
                        ))
                    })
                } else {
                    (active_tick_index != lower).then(|| {
                        lower.and_then(|lower| {
                            if (sorted_ticks[lower].index % DOUBLE_LIMIT_ORDER_TICK_SPACING)
                                .is_zero()
                            {
                                // lower has been pulled as part of an increase in price, so select the previous tick index
                                lower.checked_sub(1)
                            } else {
                                Some(lower)
                            }
                        })
                    })
                }
            });

        if let Some(next_unpulled_order_tick_index) = next_unpulled_order_tick_index_after_skip {
            let active_tick_sqrt_ratio_limit = if is_increasing {
                active_tick_index
                    .map_or_else(|| sorted_ticks.first(), |idx| sorted_ticks.get(idx + 1))
                    .map_or(Ok(Starknet::max_sqrt_ratio()), |next| {
                        to_sqrt_ratio::<Starknet>(next.index)
                            .ok_or(ConcentratedPoolQuoteError::InvalidTick(next.index))
                    })
            } else {
                active_tick_index.map_or(Ok(Starknet::min_sqrt_ratio()), |idx| {
                    let tick = sorted_ticks[idx]; // is always valid
                    to_sqrt_ratio::<Starknet>(tick.index)
                        .ok_or(ConcentratedPoolQuoteError::InvalidTick(tick.index))
                })
            }?;

            let params_sqrt_ratio_limit = params.sqrt_ratio_limit.unwrap_or(if is_increasing {
                Starknet::max_sqrt_ratio()
            } else {
                Starknet::min_sqrt_ratio()
            });

            let active_tick_boundary_sqrt_ratio = if is_increasing {
                Ord::min(active_tick_sqrt_ratio_limit, params_sqrt_ratio_limit)
            } else {
                Ord::max(active_tick_sqrt_ratio_limit, params_sqrt_ratio_limit)
            };

            // swap to (at most) the boundary of the current active tick
            let quote_to_active_tick_boundary = self.concentrated_pool.quote(QuoteParams {
                sqrt_ratio_limit: Some(active_tick_boundary_sqrt_ratio),
                token_amount: params.token_amount,
                override_state: Some(concentrated_pool_state),
                meta: (),
            })?;

            calculated_amount += quote_to_active_tick_boundary.calculated_amount;
            consumed_amount += quote_to_active_tick_boundary.consumed_amount;
            fees_paid += quote_to_active_tick_boundary.fees_paid;
            concentrated_pool_resources += quote_to_active_tick_boundary.execution_resources;

            concentrated_pool_state = quote_to_active_tick_boundary.state_after;

            let amount_remaining = params.token_amount.amount - consumed_amount;

            // skip the range of pulled orders and start from the sqrt ratio of the next unpulled order if we have some amount remaining
            if !amount_remaining.is_zero() {
                let skip_starting_sqrt_ratio = if is_increasing {
                    next_unpulled_order_tick_index
                        .map_or(
                            Ok(Starknet::max_sqrt_ratio()), // note that reaching this case implies that the pool has no initialized ticks
                            |idx| {
                                let tick_index = sorted_ticks[idx].index;
                                to_sqrt_ratio::<Starknet>(tick_index)
                                    .ok_or(ConcentratedPoolQuoteError::InvalidTick(tick_index))
                            },
                        )?
                        .min(params_sqrt_ratio_limit)
                } else {
                    next_unpulled_order_tick_index
                        .map_or_else(|| sorted_ticks.first(), |idx| sorted_ticks.get(idx + 1))
                        .map_or(Ok(Starknet::min_sqrt_ratio()), |tick| {
                            to_sqrt_ratio::<Starknet>(tick.index)
                                .ok_or(ConcentratedPoolQuoteError::InvalidTick(tick.index))
                        })?
                        .max(params_sqrt_ratio_limit)
                };

                // account for the uninitialized ticks that we will skip next
                concentrated_pool_resources.extra_distinct_bitmap_lookups +=
                    approximate_extra_distinct_tick_bitmap_lookups(
                        concentrated_pool_state.sqrt_ratio,
                        skip_starting_sqrt_ratio,
                        LIMIT_ORDER_TICK_SPACING.unsigned_abs(),
                    );

                let liquidity_at_next_unpulled_order_tick_index = {
                    let mut current_liquidity = concentrated_pool_state.liquidity;
                    let mut current_active_tick_index = concentrated_pool_state.active_tick_index;

                    // apply all liquidity_deltas in between the current active tick and the next unpulled order
                    loop {
                        let (next_tick_index, liquidity_delta) = if is_increasing
                            && current_active_tick_index < next_unpulled_order_tick_index
                        {
                            let next_tick_index = current_active_tick_index.map_or(
                                0,
                                |idx| idx + 1, // valid index because next_unpulled_order_tick_index is larger than current_active_tick_index
                            );

                            (
                                Some(next_tick_index),
                                sorted_ticks[next_tick_index].liquidity_delta,
                            )
                        } else if !is_increasing
                            && current_active_tick_index > next_unpulled_order_tick_index
                        {
                            let current_tick_index = current_active_tick_index.unwrap(); // safe because current_active_tick_index is larger than next_unpulled_order_tick_index

                            (
                                current_tick_index.checked_sub(1),
                                sorted_ticks[current_tick_index].liquidity_delta,
                            )
                        } else {
                            break;
                        };

                        current_active_tick_index = next_tick_index;

                        if liquidity_delta.is_positive() == is_increasing {
                            current_liquidity += liquidity_delta.unsigned_abs();
                        } else {
                            current_liquidity -= liquidity_delta.unsigned_abs();
                        }
                    }

                    current_liquidity
                };

                let quote_from_next_unpulled_order = self.concentrated_pool.quote(QuoteParams {
                    sqrt_ratio_limit: params.sqrt_ratio_limit,
                    token_amount: TokenAmount {
                        amount: amount_remaining,
                        token: params.token_amount.token,
                    },
                    override_state: Some(ConcentratedPoolState {
                        active_tick_index: next_unpulled_order_tick_index,
                        sqrt_ratio: skip_starting_sqrt_ratio,
                        liquidity: liquidity_at_next_unpulled_order_tick_index,
                    }),
                    meta: (),
                })?;

                calculated_amount += quote_from_next_unpulled_order.calculated_amount;
                consumed_amount += quote_from_next_unpulled_order.consumed_amount;
                fees_paid += quote_from_next_unpulled_order.fees_paid;
                concentrated_pool_resources += quote_from_next_unpulled_order.execution_resources;

                concentrated_pool_state = quote_from_next_unpulled_order.state_after;
            }
        } else {
            let quote_simple = self.concentrated_pool.quote(QuoteParams {
                sqrt_ratio_limit: params.sqrt_ratio_limit,
                override_state: Some(initial_state.concentrated_pool_state),
                token_amount: params.token_amount,
                meta: (),
            })?;

            calculated_amount += quote_simple.calculated_amount;
            consumed_amount += quote_simple.consumed_amount;
            fees_paid += quote_simple.fees_paid;
            concentrated_pool_resources += quote_simple.execution_resources;

            concentrated_pool_state = quote_simple.state_after;
        }

        let (tick_index_before, tick_index_after) = (
            initial_state.concentrated_pool_state.active_tick_index,
            concentrated_pool_state.active_tick_index,
        );

        let new_tick_indices_reached = if is_increasing {
            initial_state
                .tick_indices_reached
                .map_or((tick_index_before, tick_index_after), |(lower, upper)| {
                    (lower, Ord::max(upper, tick_index_after))
                })
        } else {
            initial_state
                .tick_indices_reached
                .map_or((tick_index_after, tick_index_before), |(lower, upper)| {
                    (Ord::min(lower, tick_index_after), upper)
                })
        };

        let from_tick_index = next_unpulled_order_tick_index_after_skip
            .unwrap_or(initial_state.concentrated_pool_state.active_tick_index);
        let to_tick_index = if is_increasing {
            Ord::max(from_tick_index, tick_index_after)
        } else {
            Ord::min(from_tick_index, tick_index_after)
        };

        let orders_pulled =
            calculate_orders_pulled(from_tick_index, to_tick_index, is_increasing, sorted_ticks);

        Ok(Quote {
            calculated_amount,
            consumed_amount,
            execution_resources: LimitOrderPoolResources {
                concentrated: concentrated_pool_resources,
                limit_order: LimitOrderStandalonePoolResources { orders_pulled },
            },
            fees_paid,
            is_price_increasing: is_increasing,
            state_after: LimitOrderPoolState {
                concentrated_pool_state,
                tick_indices_reached: Some(new_tick_indices_reached),
            },
        })
    }

    fn has_liquidity(&self) -> bool {
        self.concentrated_pool.has_liquidity()
    }

    fn max_tick_with_liquidity(&self) -> Option<i32> {
        self.concentrated_pool.max_tick_with_liquidity()
    }

    fn min_tick_with_liquidity(&self) -> Option<i32> {
        self.concentrated_pool.min_tick_with_liquidity()
    }

    fn is_path_dependent(&self) -> bool {
        false
    }
}

impl PoolState for LimitOrderPoolState {
    fn sqrt_ratio(&self) -> U256 {
        self.concentrated_pool_state.sqrt_ratio()
    }

    fn liquidity(&self) -> u128 {
        self.concentrated_pool_state.liquidity()
    }
}

impl private::Sealed for LimitOrderPool {}
impl private::Sealed for LimitOrderPoolState {}

fn calculate_orders_pulled(
    from: Option<usize>,
    to: Option<usize>,
    is_increasing: bool,
    sorted_ticks: &[Tick],
) -> u32 {
    let mut current = from;
    let mut orders_pulled = 0;

    while current != to {
        let crossed_tick = if is_increasing {
            let crossed_tick = current.map_or(0, |idx| idx + 1);
            current = Some(crossed_tick);
            crossed_tick
        } else {
            let crossed_tick = current.unwrap();
            current = crossed_tick.checked_sub(1);
            crossed_tick
        };

        if !(sorted_ticks[crossed_tick].index % DOUBLE_LIMIT_ORDER_TICK_SPACING).is_zero() {
            orders_pulled += 1;
        }
    }

    orders_pulled
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        chain::starknet::Starknet,
        math::tick::to_sqrt_ratio,
        quoting::types::{Quote, QuoteParams, Tick, TokenAmount},
    };

    const TOKEN0: Felt = Felt::ZERO;
    const TOKEN1: Felt = Felt::ONE;
    const EXTENSION: Felt = Felt::TWO;
    const DEFAULT_LIQUIDITY: i128 = 10_000_000;

    fn ticks(entries: &[(i32, i128)]) -> Vec<Tick> {
        entries
            .iter()
            .map(|(index, delta)| Tick {
                index: *index,
                liquidity_delta: *delta,
            })
            .collect()
    }

    fn pool_at(
        sqrt_ratio_tick: i32,
        active_tick: i32,
        liquidity: u128,
        entries: &[(i32, i128)],
    ) -> LimitOrderPool {
        LimitOrderPool::new(
            TOKEN0,
            TOKEN1,
            EXTENSION,
            to_sqrt_ratio::<Starknet>(sqrt_ratio_tick).unwrap(),
            active_tick,
            liquidity,
            ticks(entries),
        )
        .unwrap()
    }

    fn default_pool(entries: &[(i32, i128)]) -> LimitOrderPool {
        pool_at(0, 0, DEFAULT_LIQUIDITY.unsigned_abs(), entries)
    }

    fn quote_amount(
        pool: &LimitOrderPool,
        token: Felt,
        amount: i128,
        sqrt_ratio_limit: Option<U256>,
        override_state: Option<LimitOrderPoolState>,
    ) -> Quote<LimitOrderPoolResources, LimitOrderPoolState> {
        pool.quote(QuoteParams {
            sqrt_ratio_limit,
            override_state,
            meta: (),
            token_amount: TokenAmount { token, amount },
        })
        .unwrap()
    }

    mod constructor_validation {
        use super::*;

        #[test]
        fn neighbor_ticks_validation() {
            let err = LimitOrderPool::new(
                TOKEN0,
                TOKEN1,
                EXTENSION,
                to_sqrt_ratio::<Starknet>(0).unwrap(),
                0,
                1,
                ticks(&[(0, 1), (LIMIT_ORDER_TICK_SPACING * 2, -1)]),
            )
            .unwrap_err();
            assert_eq!(
                err,
                LimitOrderPoolConstructionError::AllTicksMustHaveNeighbor
            );
        }

        #[test]
        fn neighbor_ticks_validation_skipping_netted_tick() {
            let err = LimitOrderPool::new(
                TOKEN0,
                TOKEN1,
                EXTENSION,
                to_sqrt_ratio::<Starknet>(0).unwrap(),
                0,
                1,
                ticks(&[
                    (LIMIT_ORDER_TICK_SPACING * -1, 1),
                    (LIMIT_ORDER_TICK_SPACING, -1),
                ]),
            )
            .unwrap_err();
            assert_eq!(
                err,
                LimitOrderPoolConstructionError::AllTicksMustHaveNeighbor
            );
        }

        #[test]
        fn neighbor_ticks_validation_no_neighbor_last_tick() {
            let err = LimitOrderPool::new(
                TOKEN0,
                TOKEN1,
                EXTENSION,
                to_sqrt_ratio::<Starknet>(0).unwrap(),
                0,
                2,
                ticks(&[
                    (0, 2),
                    (LIMIT_ORDER_TICK_SPACING, -1),
                    (LIMIT_ORDER_TICK_SPACING * 3, -1),
                ]),
            )
            .unwrap_err();
            assert_eq!(err, LimitOrderPoolConstructionError::LastTickHasNoNeighbor);
        }
    }

    #[test]
    fn swap_one_for_zero_partial() {
        let pool = default_pool(&[
            (0, DEFAULT_LIQUIDITY),
            (LIMIT_ORDER_TICK_SPACING, -DEFAULT_LIQUIDITY),
        ]);
        let quote = quote_amount(&pool, TOKEN1, 10_000, None, None);
        assert_eq!(
            quote.state_after.tick_indices_reached,
            Some((Some(0), Some(1)))
        );
        assert_eq!(
            (
                quote.consumed_amount,
                quote.calculated_amount,
                quote.execution_resources.limit_order.orders_pulled,
            ),
            (641, 639, 1)
        );
    }

    #[test]
    fn swap_one_for_zero_cross_multiple() {
        let pool = default_pool(&[
            (0, DEFAULT_LIQUIDITY),
            (LIMIT_ORDER_TICK_SPACING, -DEFAULT_LIQUIDITY),
            (LIMIT_ORDER_TICK_SPACING * 2, DEFAULT_LIQUIDITY),
            (LIMIT_ORDER_TICK_SPACING * 3, -DEFAULT_LIQUIDITY),
        ]);

        let quote = quote_amount(&pool, TOKEN1, 1000, None, None);
        assert_eq!(quote.fees_paid, 0);
        assert_eq!(
            quote.state_after.tick_indices_reached,
            Some((Some(0), Some(2)))
        );
        assert_eq!(
            (
                quote.consumed_amount,
                quote.calculated_amount,
                quote.execution_resources.limit_order.orders_pulled,
            ),
            (1000, 997, 1)
        );
        assert_eq!(
            (
                quote
                    .execution_resources
                    .concentrated
                    .initialized_ticks_crossed,
                quote
                    .execution_resources
                    .concentrated
                    .no_override_price_change,
                quote
                    .execution_resources
                    .concentrated
                    .extra_distinct_bitmap_lookups,
            ),
            (2, 1, 0)
        );
    }

    #[test]
    fn order_sell_token0_for_token1_can_only_be_executed_once() {
        let pool = default_pool(&[
            (0, DEFAULT_LIQUIDITY),
            (LIMIT_ORDER_TICK_SPACING, -DEFAULT_LIQUIDITY),
        ]);

        let quote0 = quote_amount(
            &pool,
            TOKEN1,
            1000,
            to_sqrt_ratio::<Starknet>(LIMIT_ORDER_TICK_SPACING),
            None,
        );
        assert_eq!(
            (
                quote0.state_after.concentrated_pool_state.active_tick_index,
                quote0.state_after.tick_indices_reached,
                quote0.execution_resources.limit_order.orders_pulled,
            ),
            (Some(1), Some((Some(0), Some(1))), 1)
        );

        let quote1 = quote_amount(
            &pool,
            TOKEN0,
            1000,
            to_sqrt_ratio::<Starknet>(0),
            Some(quote0.state_after),
        );
        let quote2 = quote_amount(
            &pool,
            TOKEN1,
            1000,
            to_sqrt_ratio::<Starknet>(LIMIT_ORDER_TICK_SPACING),
            Some(quote1.state_after),
        );
        assert_eq!((quote1.consumed_amount, quote2.consumed_amount), (0, 0));
    }

    #[test]
    fn order_sell_token1_for_token0_can_only_be_executed_once() {
        let pool = pool_at(
            LIMIT_ORDER_TICK_SPACING * 2,
            LIMIT_ORDER_TICK_SPACING * 2,
            0,
            &[
                (LIMIT_ORDER_TICK_SPACING, DEFAULT_LIQUIDITY),
                (LIMIT_ORDER_TICK_SPACING * 2, -DEFAULT_LIQUIDITY),
            ],
        );

        let quote0 = quote_amount(
            &pool,
            TOKEN0,
            1000,
            to_sqrt_ratio::<Starknet>(LIMIT_ORDER_TICK_SPACING),
            None,
        );
        assert_eq!(
            quote0.state_after.concentrated_pool_state.active_tick_index,
            None
        );
        assert_eq!(
            quote0.state_after.tick_indices_reached,
            Some((None, Some(1)))
        );

        let quote1 = quote_amount(
            &pool,
            TOKEN1,
            1000,
            to_sqrt_ratio::<Starknet>(LIMIT_ORDER_TICK_SPACING * 2),
            Some(quote0.state_after),
        );
        let quote2 = quote_amount(
            &pool,
            TOKEN0,
            1000,
            to_sqrt_ratio::<Starknet>(LIMIT_ORDER_TICK_SPACING),
            Some(quote1.state_after),
        );
        assert_eq!((quote1.consumed_amount, quote2.consumed_amount), (0, 0));
        assert_eq!(quote1.state_after.concentrated_pool_state.liquidity, 0);
    }

    fn complex_pool() -> LimitOrderPool {
        default_pool(&[
            (-3 * LIMIT_ORDER_TICK_SPACING, DEFAULT_LIQUIDITY),
            (-2 * LIMIT_ORDER_TICK_SPACING, -DEFAULT_LIQUIDITY),
            (-1 * LIMIT_ORDER_TICK_SPACING, DEFAULT_LIQUIDITY),
            (0, 0),
            (1 * LIMIT_ORDER_TICK_SPACING, -DEFAULT_LIQUIDITY),
            (4 * LIMIT_ORDER_TICK_SPACING, DEFAULT_LIQUIDITY),
            (5 * LIMIT_ORDER_TICK_SPACING, -DEFAULT_LIQUIDITY),
        ])
    }

    #[test]
    fn complex_pool_scenario() {
        let pool = complex_pool();

        let quote0 = quote_amount(
            &pool,
            TOKEN1,
            1_000_000,
            to_sqrt_ratio::<Starknet>(LIMIT_ORDER_TICK_SPACING * 9 / 2),
            None,
        );
        assert_eq!(
            quote0.state_after.concentrated_pool_state.active_tick_index,
            Some(5)
        );
        assert_eq!(
            (
                quote0.consumed_amount,
                quote0.calculated_amount,
                quote0.state_after.tick_indices_reached,
            ),
            (962, 958, Some((Some(3), Some(5))))
        );

        let quote1 = quote_amount(
            &pool,
            TOKEN0,
            1_000_000,
            to_sqrt_ratio::<Starknet>(LIMIT_ORDER_TICK_SPACING * -5 / 2),
            Some(quote0.state_after),
        );
        assert_eq!(
            (
                quote1.consumed_amount,
                quote1.calculated_amount,
                quote1.state_after.tick_indices_reached,
            ),
            (1_282, 1_278, Some((Some(0), Some(5))))
        );
        assert_eq!(
            quote1.state_after.concentrated_pool_state.sqrt_ratio,
            to_sqrt_ratio::<Starknet>(LIMIT_ORDER_TICK_SPACING * -5 / 2).unwrap()
        );

        let quote2 = quote_amount(
            &pool,
            TOKEN1,
            1_000_000,
            to_sqrt_ratio::<Starknet>(LIMIT_ORDER_TICK_SPACING * 9 / 2),
            Some(quote1.state_after),
        );
        assert_eq!(
            (
                quote2.consumed_amount,
                quote2.calculated_amount,
                quote2.state_after.tick_indices_reached,
            ),
            (641, 639, Some((Some(0), Some(5))))
        );
    }

    #[test]
    fn complex_pool_scenario_reverse_order() {
        let pool = complex_pool();

        let quote0 = quote_amount(
            &pool,
            TOKEN0,
            1_000_000,
            to_sqrt_ratio::<Starknet>(LIMIT_ORDER_TICK_SPACING * -5 / 2),
            None,
        );
        assert_eq!(
            (
                quote0.consumed_amount,
                quote0.calculated_amount,
                quote0.state_after.tick_indices_reached,
            ),
            (962, 958, Some((Some(0), Some(3))))
        );

        let quote1 = quote_amount(
            &pool,
            TOKEN1,
            1_000_000,
            to_sqrt_ratio::<Starknet>(LIMIT_ORDER_TICK_SPACING * 9 / 2),
            Some(quote0.state_after),
        );
        assert_eq!(
            (
                quote1.consumed_amount,
                quote1.calculated_amount,
                quote1.state_after.tick_indices_reached,
            ),
            (1282, 1278, Some((Some(0), Some(5))))
        );

        let quote2 = quote_amount(
            &pool,
            TOKEN0,
            1_000_000,
            to_sqrt_ratio::<Starknet>(LIMIT_ORDER_TICK_SPACING * -5 / 2),
            Some(quote1.state_after),
        );
        assert_eq!(
            (
                quote2.consumed_amount,
                quote2.calculated_amount,
                quote2.state_after.concentrated_pool_state.active_tick_index,
            ),
            (641, 639, Some(0))
        );
        assert_eq!(
            quote2.state_after.tick_indices_reached,
            Some((Some(0), Some(5)))
        );
    }
}
