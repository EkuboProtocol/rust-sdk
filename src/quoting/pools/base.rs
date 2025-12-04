use crate::private;
use crate::quoting::pools::{
    ensure_valid_token_order, is_token1, CommonPoolConstructionError, CommonPoolQuoteError,
};
use crate::quoting::types::{Pool, PoolKey, Quote, QuoteParams, Tick};
use crate::quoting::util::{
    approximate_number_of_tick_spacings_crossed, construct_sorted_ticks, ConstructSortedTicksError,
};
use crate::{
    chain::Chain,
    math::swap::{compute_step, is_price_increasing, ComputeStepError},
};
use crate::{math::tick::to_sqrt_ratio, quoting::types::PoolState};
use alloc::vec::Vec;
use derive_more::{Add, AddAssign, Sub, SubAssign};
use num_traits::Zero;
use ruint::aliases::U256;
use thiserror::Error;

/// Concentrated liquidity pool defined by sorted ticks and active liquidity state.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(
    feature = "serde",
    derive(serde::Serialize, serde::Deserialize),
    serde(bound(
        serialize = "C::Fee: serde::Serialize, C::Address: serde::Serialize",
        deserialize = "C::Fee: serde::Deserialize<'de>, C::Address: serde::Deserialize<'de>"
    ))
)]
pub struct BasePool<C: Chain> {
    /// Immutable pool key identifying tokens and fee config.
    key: BasePoolKey<C>,
    /// Current pool state (price, liquidity, active tick index).
    state: BasePoolState,
    /// Sorted ticks defining liquidity changes across price ranges.
    sorted_ticks: Vec<Tick>,
}

/// Unique identifier for a [`BasePool`].
pub type BasePoolKey<C> = PoolKey<<C as Chain>::Address, <C as Chain>::Fee, BasePoolTypeConfig>;
/// Type configuration for a [`BasePool`], representing the tick spacing.
pub type BasePoolTypeConfig = TickSpacing;

/// Tick spacing for a concentrated pool.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct TickSpacing(pub u32);

/// Price/liquidity state for a [`BasePool`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct BasePoolState {
    /// Current square root price ratio.
    pub sqrt_ratio: U256,
    /// Active liquidity at the current price.
    pub liquidity: u128,
    /// Index of the active initialized tick, if any.
    pub active_tick_index: Option<usize>,
}

/// Resources consumed during swap execution
#[derive(Clone, Copy, Default, Debug, PartialEq, Hash, Eq, Add, AddAssign, Sub, SubAssign)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct BasePoolResources {
    /// Whether price changed when no override was provided.
    pub no_override_price_change: u32,
    /// Count of initialized ticks crossed during the quote.
    pub initialized_ticks_crossed: u32,
    /// Count of tick spacings crossed during the quote.
    pub tick_spacings_crossed: u32,
}

/// Errors that can occur when constructing a `BasePool`.
#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, Error)]
pub enum BasePoolConstructionError {
    #[error(transparent)]
    Common(#[from] CommonPoolConstructionError),
    #[error("constructing ticks from partial data")]
    ConstructSortedTicksFromPartialDataError(#[from] ConstructSortedTicksError),
    #[error("tick spacing too large")]
    /// Tick spacing must be less than or equal to max tick spacing.
    TickSpacingTooLarge,
    #[error("tick spacing must be non-zero")]
    /// Tick spacing must be greater than zero. Use the `FullRangePool` instead if you encounter this error.
    TickSpacingCannotBeZero,
    #[error("ticks are not sorted in ascending order")]
    /// Ticks must be sorted in ascending order.
    TicksNotSorted,
    #[error("all ticks must be a multiple of the tick spacing")]
    /// All ticks must be a multiple of `tick_spacing`.
    TickNotMultipleOfSpacing,
    #[error("total liquidity is non-zero")]
    /// The total liquidity across all ticks must sum to zero.
    TotalLiquidityNotZero,
    #[error("active liquidity mismatch")]
    /// Active liquidity doesn't match the sum of liquidity deltas before the active tick.
    ActiveLiquidityMismatch,
    #[error("active tick price is invalid")]
    /// The `sqrt_ratio` of active tick is not less than or equal to current `sqrt_ratio`.
    ActiveTickSqrtRatioInvalid,
    #[error("active price is higher than lowest initialized tick's price")]
    /// current `sqrt_ratio` must be lower than the first tick's `sqrt_ratio` when `active_tick_index` is none.
    SqrtRatioTooHighWithNoActiveTick,
    #[error("active tick index out of bounds")]
    /// The active tick index is out of bounds.
    ActiveTickIndexOutOfBounds,
    #[error("invalid tick index {0}")]
    /// Invalid tick index.
    InvalidTickIndex(i32),
    #[error("active liquidity overflow")]
    /// The application of all tick liquidity deltas must result in a valid intermediate active liqudity.
    ActiveLiquidityOverflow,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, Error)]
pub enum BasePoolQuoteError {
    #[error(transparent)]
    Common(#[from] CommonPoolQuoteError),
    #[error("invalid price limit")]
    InvalidSqrtRatioLimit,
    #[error("invalid tick {0}")]
    InvalidTick(i32),
    #[error("failed swap step computation")]
    FailedComputeSwapStep(#[from] ComputeStepError),
}

impl<C: Chain> BasePool<C> {
    /// Creates a `BasePool` from partial tick data retrieved from a quote data fetcher lens contract.
    ///
    /// This helper constructor takes partial tick data along with min/max tick boundaries and constructs
    /// a valid `BasePool` instance with properly balanced liquidity deltas.
    ///
    /// # Arguments
    ///
    /// * `key` - The `NodeKey` containing token information and configuration
    /// * `sqrt_ratio` - The square root price ratio of the pool
    /// * `partial_ticks` - A vector of ticks retrieved from the lens contract
    /// * `min_tick_searched` - The minimum tick that was searched (not necessarily a multiple of tick spacing)
    /// * `max_tick_searched` - The maximum tick that was searched (not necessarily a multiple of tick spacing)
    /// * `liquidity` - The current liquidity of the pool
    /// * `current_tick` - The current tick of the pool
    ///
    /// # Returns
    ///
    /// * `Result<Self, BasePoolConstructionError>` - A new `BasePool` instance or an error
    pub fn from_partial_data(
        key: BasePoolKey<C>,
        sqrt_ratio: U256,
        partial_ticks: Vec<Tick>,
        min_tick_searched: i32,
        max_tick_searched: i32,
        liquidity: u128,
        current_tick: i32,
    ) -> Result<Self, BasePoolConstructionError> {
        let tick_spacing = key.config.pool_type_config;
        let spacing_i32 = tick_spacing.0 as i32;
        let tick_spacing = tick_spacing.0;

        // Get sorted ticks using the utility function
        let sorted_ticks = construct_sorted_ticks::<C>(
            partial_ticks,
            min_tick_searched,
            max_tick_searched,
            tick_spacing,
            liquidity,
            current_tick,
        )
        .map_err(BasePoolConstructionError::ConstructSortedTicksFromPartialDataError)?;

        // Ensure all ticks are multiples of tick spacing
        for tick in &sorted_ticks {
            if tick.index % spacing_i32 != 0 {
                return Err(BasePoolConstructionError::TickNotMultipleOfSpacing);
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
        key: BasePoolKey<C>,
        state: BasePoolState,
        sorted_ticks: Vec<Tick>,
    ) -> Result<Self, BasePoolConstructionError> {
        ensure_valid_token_order(&key)?;

        let tick_spacing = key.config.pool_type_config;

        if tick_spacing > C::max_tick_spacing() {
            return Err(BasePoolConstructionError::TickSpacingTooLarge);
        }

        if tick_spacing.0.is_zero() {
            return Err(BasePoolConstructionError::TickSpacingCannotBeZero);
        }

        // Check ticks are sorted in linear time
        let mut last_tick: Option<i32> = None;
        let mut total_liquidity: u128 = 0;
        let mut active_liquidity: u128 = 0;
        let spacing_i32 = tick_spacing.0 as i32;

        for (i, tick) in sorted_ticks.iter().enumerate() {
            // Verify ticks are sorted
            if let Some(last) = last_tick {
                if tick.index <= last {
                    return Err(BasePoolConstructionError::TicksNotSorted);
                }
            }

            // Verify ticks are multiples of tick_spacing
            if !(tick.index % spacing_i32).is_zero() {
                return Err(BasePoolConstructionError::TickNotMultipleOfSpacing);
            }

            last_tick = Some(tick.index);

            // Calculate total liquidity
            total_liquidity = if tick.liquidity_delta < 0 {
                total_liquidity.checked_sub(tick.liquidity_delta.unsigned_abs())
            } else {
                total_liquidity.checked_add(tick.liquidity_delta.unsigned_abs())
            }
            .ok_or(BasePoolConstructionError::ActiveLiquidityOverflow)?;

            // Calculate active liquidity
            if let Some(active_index) = state.active_tick_index {
                if i <= active_index {
                    active_liquidity = if tick.liquidity_delta > 0 {
                        active_liquidity.checked_add(tick.liquidity_delta.unsigned_abs())
                    } else {
                        active_liquidity.checked_sub(tick.liquidity_delta.unsigned_abs())
                    }
                    .ok_or(BasePoolConstructionError::ActiveLiquidityOverflow)?;
                }
            }
        }

        // Verify total liquidity is zero
        if !total_liquidity.is_zero() {
            return Err(BasePoolConstructionError::TotalLiquidityNotZero);
        }

        // Verify active liquidity matches state liquidity
        if active_liquidity != state.liquidity {
            return Err(BasePoolConstructionError::ActiveLiquidityMismatch);
        }

        // Validate sqrt ratio against active or first tick
        if let Some(active) = state.active_tick_index {
            let tick = sorted_ticks
                .get(active)
                .ok_or(BasePoolConstructionError::ActiveTickIndexOutOfBounds)?;

            let active_tick_sqrt_ratio = to_sqrt_ratio::<C>(tick.index)
                .ok_or(BasePoolConstructionError::InvalidTickIndex(tick.index))?;

            if active_tick_sqrt_ratio > state.sqrt_ratio {
                return Err(BasePoolConstructionError::ActiveTickSqrtRatioInvalid);
            }
        } else if let Some(first) = sorted_ticks.first() {
            let first_tick_sqrt_ratio = to_sqrt_ratio::<C>(first.index)
                .ok_or(BasePoolConstructionError::InvalidTickIndex(first.index))?;

            if state.sqrt_ratio > first_tick_sqrt_ratio {
                return Err(BasePoolConstructionError::SqrtRatioTooHighWithNoActiveTick);
            }
        }

        Ok(Self {
            key,
            state,
            sorted_ticks,
        })
    }

    pub fn ticks(&self) -> &[Tick] {
        &self.sorted_ticks
    }
}

impl PoolState for BasePoolState {
    fn sqrt_ratio(&self) -> U256 {
        self.sqrt_ratio
    }

    fn liquidity(&self) -> u128 {
        self.liquidity
    }
}

impl<C: Chain> Pool for BasePool<C> {
    type Address = C::Address;
    type Fee = C::Fee;
    type Resources = BasePoolResources;
    type State = BasePoolState;
    type QuoteError = BasePoolQuoteError;
    type Meta = ();
    type PoolTypeConfig = BasePoolTypeConfig;

    fn key(&self) -> PoolKey<C::Address, C::Fee, Self::PoolTypeConfig> {
        self.key
    }

    fn state(&self) -> Self::State {
        self.state
    }

    fn quote(
        &self,
        params: QuoteParams<C::Address, Self::State, Self::Meta>,
    ) -> Result<Quote<Self::Resources, Self::State>, Self::QuoteError> {
        let amount = params.token_amount.amount;
        let token = params.token_amount.token;
        let is_token1 = is_token1(&self.key, token)?;

        let state = params.override_state.unwrap_or(self.state);

        if amount == 0 {
            return Ok(Quote {
                is_price_increasing: is_token1,
                consumed_amount: 0,
                calculated_amount: 0,
                execution_resources: BasePoolResources::default(),
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
            if limit < C::min_sqrt_ratio() || limit > C::max_sqrt_ratio() {
                return Err(BasePoolQuoteError::InvalidSqrtRatioLimit);
            }
            limit
        } else if is_increasing {
            C::max_sqrt_ratio()
        } else {
            C::min_sqrt_ratio()
        };

        let mut calculated_amount: u128 = 0;
        let mut fees_paid: u128 = 0;
        let mut initialized_ticks_crossed: u32 = 0;
        let mut amount_remaining = amount;
        let starting_sqrt_ratio = sqrt_ratio;

        while amount_remaining != 0 && sqrt_ratio != sqrt_ratio_limit {
            let next_initialized_tick = if is_increasing {
                if let Some(index) = active_tick_index {
                    if let Some(tick) = self.sorted_ticks.get(index + 1) {
                        let ratio = to_sqrt_ratio::<C>(tick.index)
                            .ok_or(BasePoolQuoteError::InvalidTick(tick.index))?;
                        Some((index + 1, tick, ratio))
                    } else {
                        None
                    }
                } else if let Some(tick) = self.sorted_ticks.first() {
                    let ratio = to_sqrt_ratio::<C>(tick.index)
                        .ok_or(BasePoolQuoteError::InvalidTick(tick.index))?;
                    Some((0, tick, ratio))
                } else {
                    None
                }
            } else if let Some(index) = active_tick_index {
                if let Some(tick) = self.sorted_ticks.get(index) {
                    let ratio = to_sqrt_ratio::<C>(tick.index)
                        .ok_or(BasePoolQuoteError::InvalidTick(tick.index))?;
                    Some((index, tick, ratio))
                } else {
                    None
                }
            } else {
                None
            };

            let step_sqrt_ratio_limit =
                next_initialized_tick
                    .as_ref()
                    .map_or(sqrt_ratio_limit, |(_, _, ratio)| {
                        if (*ratio < sqrt_ratio_limit) == is_increasing {
                            *ratio
                        } else {
                            sqrt_ratio_limit
                        }
                    });

            let step = compute_step::<C>(
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
                    } else {
                        index.checked_sub(1)
                    };

                    initialized_ticks_crossed += 1;

                    if (next_tick.liquidity_delta.signum() == 1) == is_increasing {
                        liquidity += next_tick.liquidity_delta.unsigned_abs();
                    } else {
                        liquidity -= next_tick.liquidity_delta.unsigned_abs();
                    }
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
            no_override_price_change: u32::from(
                starting_sqrt_ratio == self.state.sqrt_ratio && starting_sqrt_ratio != sqrt_ratio,
            ),
            initialized_ticks_crossed,
            tick_spacings_crossed: approximate_number_of_tick_spacings_crossed(
                starting_sqrt_ratio,
                sqrt_ratio,
                self.key.config.pool_type_config.0,
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

impl<C: Chain> private::Sealed for BasePool<C> {}
impl private::Sealed for BasePoolState {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        chain::{
            starknet::Starknet,
            tests::{run_for_all_chains, ChainTest},
        },
        math::sqrt_ratio::SQRT_RATIO_ONE,
        quoting::types::{PoolConfig, TokenAmount},
    };
    use alloc::vec;
    use num_traits::Zero;

    fn pool_key<C: ChainTest>(tick_spacing: u32, fee: C::Fee) -> BasePoolKey<C> {
        PoolKey {
            token0: C::zero_address(),
            token1: C::one_address(),
            config: PoolConfig {
                fee,
                pool_type_config: TickSpacing(tick_spacing),
                extension: C::zero_address(),
            },
        }
    }

    fn ticks(indices: &[(i32, i128)]) -> Vec<Tick> {
        indices
            .iter()
            .map(|(index, delta)| Tick {
                index: *index,
                liquidity_delta: *delta,
            })
            .collect()
    }

    fn pool_state(sqrt_ratio: U256, liquidity: u128, active: Option<usize>) -> BasePoolState {
        BasePoolState {
            sqrt_ratio,
            liquidity,
            active_tick_index: active,
        }
    }

    fn sqrt_ratio<C: Chain>(tick: i32) -> U256 {
        to_sqrt_ratio::<C>(tick).unwrap()
    }

    fn zero_fee<C: Chain>() -> C::Fee {
        C::Fee::zero()
    }

    mod constructor_validation {
        use super::*;

        #[test]
        fn token0_must_be_less_than_token1() {
            run_for_all_chains!(ChainTy, _chain => {
                let result = BasePool::<ChainTy>::new(
                    PoolKey {
                        token0: ChainTy::zero_address(),
                        token1: ChainTy::zero_address(),
                        config: PoolConfig {
                            fee: zero_fee::<ChainTy>(),
                            pool_type_config: TickSpacing(0),
                            extension: ChainTy::zero_address(),
                        },
                    },
                    pool_state(SQRT_RATIO_ONE, 0, None),
                    vec![],
                );
                assert_eq!(
                    result.unwrap_err(),
                    BasePoolConstructionError::Common(
                        CommonPoolConstructionError::TokenOrderInvalid
                    )
                );
            });
        }

        #[test]
        fn tick_spacing_zero_reverts() {
            run_for_all_chains!(ChainTy, _chain => {
                let result = BasePool::<ChainTy>::new(
                    pool_key::<ChainTy>(0, zero_fee::<ChainTy>()),
                    pool_state(SQRT_RATIO_ONE, 0, None),
                    vec![],
                );
                assert_eq!(
                    result.unwrap_err(),
                    BasePoolConstructionError::TickSpacingCannotBeZero
                );
            });
        }

        #[test]
        fn tick_spacing_cannot_exceed_max() {
            run_for_all_chains!(ChainTy, _chain => {
                if let Some(invalid) = ChainTy::max_tick_spacing().0.checked_add(1) {
                    let result = BasePool::<ChainTy>::new(
                        pool_key::<ChainTy>(invalid, zero_fee::<ChainTy>()),
                        pool_state(SQRT_RATIO_ONE, 0, None),
                        vec![],
                    );
                    assert_eq!(
                        result.unwrap_err(),
                        BasePoolConstructionError::TickSpacingTooLarge
                    );
                }
            });
        }

        #[test]
        fn ticks_must_be_sorted() {
            run_for_all_chains!(ChainTy, _chain => {
                let result = BasePool::<ChainTy>::new(
                    pool_key::<ChainTy>(1, zero_fee::<ChainTy>()),
                    pool_state(sqrt_ratio::<ChainTy>(0), 1, Some(0)),
                    ticks(&[(ChainTy::max_tick(), 0), (0, 0)]),
                );
                assert_eq!(
                    result.unwrap_err(),
                    BasePoolConstructionError::TicksNotSorted
                );
            });
        }

        #[test]
        fn ticks_must_align_with_spacing() {
            run_for_all_chains!(ChainTy, _chain => {
                let spacing = ChainTy::max_tick_spacing();
                let result = BasePool::<ChainTy>::new(
                    pool_key::<ChainTy>(spacing.0, zero_fee::<ChainTy>()),
                    pool_state(sqrt_ratio::<ChainTy>(0), 1, Some(0)),
                    ticks(&[(-1, 1), (ChainTy::max_tick() - 1, -1)]),
                );
                assert_eq!(
                    result.unwrap_err(),
                    BasePoolConstructionError::TickNotMultipleOfSpacing
                );
            });
        }

        #[test]
        fn total_liquidity_must_sum_to_zero() {
            run_for_all_chains!(ChainTy, _chain => {
                let result = BasePool::<ChainTy>::new(
                    pool_key::<ChainTy>(1, zero_fee::<ChainTy>()),
                    pool_state(sqrt_ratio::<ChainTy>(0), 1, Some(0)),
                    ticks(&[(0, 2), (ChainTy::max_tick(), -1)]),
                );
                assert_eq!(
                    result.unwrap_err(),
                    BasePoolConstructionError::TotalLiquidityNotZero
                );
            });
        }

        #[test]
        fn active_tick_index_within_bounds() {
            run_for_all_chains!(ChainTy, _chain => {
                let result = BasePool::<ChainTy>::new(
                    pool_key::<ChainTy>(1, zero_fee::<ChainTy>()),
                    pool_state(sqrt_ratio::<ChainTy>(0), 0, Some(2)),
                    ticks(&[(0, 2), (ChainTy::max_tick(), -2)]),
                );
                assert_eq!(
                    result.unwrap_err(),
                    BasePoolConstructionError::ActiveTickIndexOutOfBounds
                );
            });
        }

        #[test]
        fn active_liquidity_must_match_sum_before_active_tick() {
            run_for_all_chains!(ChainTy, _chain => {
                let result = BasePool::<ChainTy>::new(
                    pool_key::<ChainTy>(1, zero_fee::<ChainTy>()),
                    pool_state(SQRT_RATIO_ONE, 0, Some(0)),
                    ticks(&[(0, 2), (ChainTy::max_tick(), -2)]),
                );
                assert_eq!(
                    result.unwrap_err(),
                    BasePoolConstructionError::ActiveLiquidityMismatch
                );
            });
        }

        #[test]
        fn active_tick_sqrt_ratio_cannot_exceed_state() {
            run_for_all_chains!(ChainTy, _chain => {
                let result = BasePool::<ChainTy>::new(
                    pool_key::<ChainTy>(1, zero_fee::<ChainTy>()),
                    pool_state(SQRT_RATIO_ONE - U256::ONE, 2, Some(0)),
                    ticks(&[(0, 2), (ChainTy::max_tick(), -2)]),
                );
                assert_eq!(
                    result.unwrap_err(),
                    BasePoolConstructionError::ActiveTickSqrtRatioInvalid
                );
            });
        }

        #[test]
        fn sqrt_ratio_must_be_below_first_tick_when_no_active_tick() {
            run_for_all_chains!(ChainTy, _chain => {
                let result = BasePool::<ChainTy>::new(
                    pool_key::<ChainTy>(1, zero_fee::<ChainTy>()),
                    pool_state(SQRT_RATIO_ONE + U256::ONE, 0, None),
                    ticks(&[(0, 2), (ChainTy::max_tick(), -2)]),
                );
                assert_eq!(
                    result.unwrap_err(),
                    BasePoolConstructionError::SqrtRatioTooHighWithNoActiveTick
                );
            });
        }
    }

    mod quoting {
        use super::*;

        #[test]
        fn zero_liquidity_token1_input() {
            run_for_all_chains!(ChainTy, _chain => {
                let pool = BasePool::<ChainTy>::new(
                    pool_key::<ChainTy>(1, zero_fee::<ChainTy>()),
                    pool_state(SQRT_RATIO_ONE, 0, None),
                    vec![],
                )
                .unwrap();

                let quote = pool
                    .quote(QuoteParams {
                        token_amount: TokenAmount {
                            amount: 1,
                            token: ChainTy::one_address(),
                        },
                        sqrt_ratio_limit: None,
                        override_state: None,
                        meta: (),
                    })
                    .unwrap();

                assert_eq!(
                    (quote.calculated_amount, quote.execution_resources.initialized_ticks_crossed),
                    (0, 0)
                );
            });
        }

        #[test]
        fn zero_liquidity_token0_input() {
            run_for_all_chains!(ChainTy, _chain => {
                let pool = BasePool::<ChainTy>::new(
                    pool_key::<ChainTy>(1, zero_fee::<ChainTy>()),
                    pool_state(SQRT_RATIO_ONE, 0, None),
                    vec![],
                )
                .unwrap();

                let quote = pool
                    .quote(QuoteParams {
                        token_amount: TokenAmount {
                            amount: 1,
                            token: ChainTy::zero_address(),
                        },
                        sqrt_ratio_limit: None,
                        override_state: None,
                        meta: (),
                    })
                    .unwrap();

                assert_eq!(
                    (quote.calculated_amount, quote.execution_resources.initialized_ticks_crossed),
                    (0, 0)
                );
            });
        }

        #[test]
        fn liquidity_token1_input() {
            run_for_all_chains!(ChainTy, _chain => {
                let pool = BasePool::<ChainTy>::new(
                    pool_key::<ChainTy>(1, zero_fee::<ChainTy>()),
                    pool_state(SQRT_RATIO_ONE, 1_000_000_000, Some(0)),
                    ticks(&[(0, 1_000_000_000), (1, -1_000_000_000)]),
                )
                .unwrap();

                let quote = pool
                    .quote(QuoteParams {
                        token_amount: TokenAmount {
                            amount: 1000,
                            token: ChainTy::one_address(),
                        },
                        sqrt_ratio_limit: None,
                        override_state: None,
                        meta: (),
                    })
                    .unwrap();

                assert_eq!(
                    (quote.calculated_amount, quote.execution_resources.initialized_ticks_crossed),
                    (499, 1)
                );
            });
        }

        #[test]
        fn liquidity_token0_input() {
            run_for_all_chains!(ChainTy, _chain => {
                let pool = BasePool::<ChainTy>::new(
                    pool_key::<ChainTy>(1, zero_fee::<ChainTy>()),
                    pool_state(sqrt_ratio::<ChainTy>(1), 0, Some(1)),
                    ticks(&[(0, 1_000_000_000), (1, -1_000_000_000)]),
                )
                .unwrap();

                let quote = pool
                    .quote(QuoteParams {
                        token_amount: TokenAmount {
                            amount: 1000,
                            token: ChainTy::zero_address(),
                        },
                        sqrt_ratio_limit: None,
                        override_state: None,
                        meta: (),
                    })
                    .unwrap();

                assert_eq!(
                    (quote.calculated_amount, quote.execution_resources.initialized_ticks_crossed),
                    (499, 2)
                );
            });
        }

        #[test]
        fn example_failing_quote_starknet_only() {
            let pool = BasePool::<Starknet>::new(
                pool_key::<Starknet>(100, 17014118346046923988514818429550592u128),
                BasePoolState {
                    sqrt_ratio: U256::from_limbs([16035209758820767612, 757181812420893, 0, 0]),
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
            )
            .unwrap();

            let quote_token0 = pool
                .quote(QuoteParams {
                    token_amount: TokenAmount {
                        amount: 1_000_000,
                        token: Starknet::zero_address(),
                    },
                    sqrt_ratio_limit: None,
                    override_state: None,
                    meta: (),
                })
                .unwrap();

            assert_eq!(
                (
                    quote_token0.calculated_amount,
                    quote_token0.execution_resources.initialized_ticks_crossed
                ),
                (0, 0)
            );

            let quote_token1 = pool
                .quote(QuoteParams {
                    token_amount: TokenAmount {
                        amount: 1_000_000,
                        token: Starknet::one_address(),
                    },
                    sqrt_ratio_limit: None,
                    override_state: None,
                    meta: (),
                })
                .unwrap();

            assert_eq!(quote_token1.consumed_amount, 1_000_000);
            assert_eq!(
                (
                    quote_token1.calculated_amount,
                    quote_token1.execution_resources.initialized_ticks_crossed
                ),
                (2_436_479_431, 2)
            );
        }
    }
}
