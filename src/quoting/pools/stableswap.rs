use crate::{
    chain::evm::{Evm, EVM_MAX_STABLESWAP_AMPLIFICATION_FACTOR},
    math::swap::{compute_step, is_price_increasing, ComputeStepError},
    private,
    quoting::pools::full_range::FullRangePoolState,
};
use crate::{
    chain::Chain,
    math::tick::to_sqrt_ratio,
    quoting::types::{Pool, PoolKey, Quote, QuoteParams, TokenAmount},
};
use core::ops::Not;
use derive_more::{Add, AddAssign, Sub, SubAssign};
use ruint::aliases::U256;
use thiserror::Error;

/// Configuration for a [`StableswapPool`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct StableswapPoolTypeConfig {
    /// Center tick where liquidity is concentrated.
    pub center_tick: i32,
    /// Amplification factor controlling curve shape.
    pub amplification_factor: u8,
}

/// Stableswap pool specialized for tightly-pegged assets.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct StableswapPool {
    /// Immutable pool configuration key.
    key: PoolKey<<Evm as Chain>::Address, <Evm as Chain>::Fee, StableswapPoolTypeConfig>,
    /// Current pool state (full range style).
    state: FullRangePoolState,
    /// Lower bound for the amplified price range.
    lower_price: U256,
    /// Upper bound for the amplified price range.
    upper_price: U256,
}

/// Resources consumed during stableswap quote execution.
#[derive(Clone, Copy, Default, Debug, PartialEq, Eq, Hash, Add, AddAssign, Sub, SubAssign)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct StableswapPoolResources {
    /// Whether price changed when no override was provided.
    pub no_override_price_change: u32,
    /// Count of initialized ticks crossed.
    pub initialized_ticks_crossed: u32,
}

/// Unique identifier for a [`StableswapPool`].
pub type StableswapPoolKey =
    PoolKey<<Evm as Chain>::Address, <Evm as Chain>::Fee, StableswapPoolTypeConfig>;

/// Errors that can occur when constructing a [`StableswapPool`].
#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, Error)]
pub enum StableswapPoolConstructionError {
    #[error("token0 must be less than token1")]
    TokenOrderInvalid,
    #[error("sqrt ratio out of bounds")]
    SqrtRatioInvalid,
    #[error("stableswap center tick is not between min and max tick")]
    InvalidCenterTick,
    #[error("stableswap amplification factor exceeds the maximum allowed value")]
    InvalidStableswapAmplification,
}

/// Errors that can occur when quoting a [`StableswapPool`].
#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, Error)]
pub enum StableswapPoolQuoteError {
    #[error("specified token not part of the pool")]
    InvalidToken,
    #[error("price limit invalid")]
    InvalidSqrtRatioLimit,
    #[error("failed swap computation step")]
    FailedComputeSwapStep(#[from] ComputeStepError),
}

impl StableswapPool {
    pub fn new(
        key: StableswapPoolKey,
        state: FullRangePoolState,
    ) -> Result<Self, StableswapPoolConstructionError> {
        let PoolKey {
            token0,
            token1,
            config,
        } = key;

        let StableswapPoolTypeConfig {
            center_tick,
            amplification_factor,
        } = config.pool_type_config;

        if token0 >= token1 {
            return Err(StableswapPoolConstructionError::TokenOrderInvalid);
        }

        if state.sqrt_ratio < Evm::min_sqrt_ratio() || state.sqrt_ratio > Evm::max_sqrt_ratio() {
            return Err(StableswapPoolConstructionError::SqrtRatioInvalid);
        }

        if center_tick < Evm::min_tick() || center_tick > Evm::max_tick() {
            return Err(StableswapPoolConstructionError::InvalidCenterTick);
        }

        if amplification_factor > EVM_MAX_STABLESWAP_AMPLIFICATION_FACTOR {
            return Err(StableswapPoolConstructionError::InvalidStableswapAmplification);
        }

        let liquidity_width = Evm::max_tick() >> amplification_factor;

        Ok(Self {
            key,
            state: FullRangePoolState {
                sqrt_ratio: state.sqrt_ratio,
                liquidity: state.liquidity,
            },
            lower_price: {
                let lower_tick = center_tick - liquidity_width;

                if lower_tick > Evm::min_tick() {
                    to_sqrt_ratio::<Evm>(lower_tick).unwrap()
                } else {
                    Evm::min_sqrt_ratio()
                }
            },
            upper_price: {
                let upper_tick = center_tick + liquidity_width;

                if upper_tick < Evm::max_tick() {
                    to_sqrt_ratio::<Evm>(upper_tick).unwrap()
                } else {
                    Evm::max_sqrt_ratio()
                }
            },
        })
    }
}

impl Pool for StableswapPool {
    type Address = <Evm as Chain>::Address;
    type Fee = <Evm as Chain>::Fee;
    type Resources = StableswapPoolResources;
    type State = FullRangePoolState;
    type QuoteError = StableswapPoolQuoteError;
    type Meta = ();
    type PoolTypeConfig = StableswapPoolTypeConfig;

    fn key(&self) -> StableswapPoolKey {
        self.key
    }

    fn state(&self) -> Self::State {
        self.state
    }

    fn quote(
        &self,
        params: QuoteParams<Self::Address, Self::State, Self::Meta>,
    ) -> Result<Quote<Self::Resources, Self::State>, Self::QuoteError> {
        let TokenAmount { amount, token } = params.token_amount;
        let is_token1 = token == self.key.token1;

        if !is_token1 && token != self.key.token0 {
            return Err(StableswapPoolQuoteError::InvalidToken);
        }

        let FullRangePoolState {
            mut sqrt_ratio,
            liquidity,
        } = params.override_state.unwrap_or(self.state);

        let increasing = is_price_increasing(amount, is_token1);

        let sqrt_ratio_limit = if let Some(limit) = params.sqrt_ratio_limit {
            if increasing && limit < sqrt_ratio {
                return Err(StableswapPoolQuoteError::InvalidSqrtRatioLimit);
            }
            if !increasing && limit > sqrt_ratio {
                return Err(StableswapPoolQuoteError::InvalidSqrtRatioLimit);
            }
            if limit < Evm::min_sqrt_ratio() {
                return Err(StableswapPoolQuoteError::InvalidSqrtRatioLimit);
            }
            if limit > Evm::max_sqrt_ratio() {
                return Err(StableswapPoolQuoteError::InvalidSqrtRatioLimit);
            }
            limit
        } else {
            if increasing {
                Evm::max_sqrt_ratio()
            } else {
                Evm::min_sqrt_ratio()
            }
        };

        let mut calculated_amount = 0;
        let mut fees_paid = 0;
        let mut initialized_ticks_crossed = 0;
        let mut amount_remaining = amount;
        let starting_sqrt_ratio = sqrt_ratio;

        while amount_remaining != 0 && sqrt_ratio != sqrt_ratio_limit {
            let mut step_liquidity = liquidity;
            let in_range = sqrt_ratio < self.upper_price && sqrt_ratio > self.lower_price;

            let next_tick_sqrt_ratio = if in_range {
                Some(if increasing {
                    self.upper_price
                } else {
                    self.lower_price
                })
            } else {
                step_liquidity = 0;

                if sqrt_ratio <= self.lower_price {
                    increasing.then_some(self.lower_price)
                } else {
                    increasing.not().then_some(self.upper_price)
                }
            };

            let step_sqrt_ratio_limit = next_tick_sqrt_ratio
                .filter(|&next_tick_sqrt_ratio| {
                    (next_tick_sqrt_ratio < sqrt_ratio_limit) == increasing
                })
                .unwrap_or(sqrt_ratio_limit);

            let step = compute_step::<Evm>(
                sqrt_ratio,
                step_liquidity,
                step_sqrt_ratio_limit,
                amount_remaining,
                is_token1,
                self.key.config.fee,
            )
            .map_err(StableswapPoolQuoteError::FailedComputeSwapStep)?;

            amount_remaining -= step.consumed_amount;
            calculated_amount += step.calculated_amount;
            fees_paid += step.fee_amount;
            sqrt_ratio = step.sqrt_ratio_next;

            if next_tick_sqrt_ratio
                .is_some_and(|next_tick_sqrt_ratio| next_tick_sqrt_ratio == sqrt_ratio)
            {
                initialized_ticks_crossed += 1;
            }
        }

        let resources = StableswapPoolResources {
            no_override_price_change: u32::from(
                starting_sqrt_ratio == self.state.sqrt_ratio && starting_sqrt_ratio != sqrt_ratio,
            ),
            initialized_ticks_crossed,
        };

        Ok(Quote {
            is_price_increasing: increasing,
            consumed_amount: amount - amount_remaining,
            calculated_amount,
            execution_resources: resources,
            state_after: FullRangePoolState {
                sqrt_ratio,
                liquidity,
            },
            fees_paid,
        })
    }

    // Checks if the pool has any liquidity
    fn has_liquidity(&self) -> bool {
        self.state.liquidity > 0
    }

    // For full range pools, if there's liquidity, then the max tick is MAX_TICK
    fn max_tick_with_liquidity(&self) -> Option<i32> {
        self.has_liquidity().then_some(Evm::max_tick())
    }

    // For full range pools, if there's liquidity, then the min tick is MIN_TICK
    fn min_tick_with_liquidity(&self) -> Option<i32> {
        self.has_liquidity().then_some(Evm::min_tick())
    }

    fn is_path_dependent(&self) -> bool {
        false
    }
}

impl private::Sealed for StableswapPool {}

#[cfg(test)]
mod tests {
    use alloy_primitives::Address;

    use super::*;
    use crate::{
        chain::tests::ChainTest,
        math::{
            delta::{amount0_delta, amount1_delta},
            tick::to_sqrt_ratio,
        },
        quoting::types::{PoolConfig, Quote, QuoteParams, TokenAmount},
    };

    const POSITION_AMOUNT: u128 = 1_000_000_000_000_000_000;
    const SMALL_AMOUNT: i128 = 1_000_000_000_000_000;

    fn key(center_tick: i32, amplification_factor: u8) -> StableswapPoolKey {
        PoolKey {
            token0: Evm::zero_address(),
            token1: Evm::one_address(),
            config: PoolConfig {
                extension: Evm::zero_address(),
                fee: 0,
                pool_type_config: StableswapPoolTypeConfig {
                    center_tick,
                    amplification_factor,
                },
            },
        }
    }

    fn state(tick: i32, liquidity: u128) -> FullRangePoolState {
        FullRangePoolState {
            sqrt_ratio: to_sqrt_ratio::<Evm>(tick).unwrap(),
            liquidity,
        }
    }

    fn build_pool(center_tick: i32, amplification: u8, current_tick: i32) -> StableswapPool {
        let liquidity = minted_liquidity(center_tick, amplification, current_tick);
        StableswapPool::new(
            key(center_tick, amplification),
            state(current_tick, liquidity),
        )
        .unwrap()
    }

    fn active_range(center_tick: i32, amplification: u8) -> (i32, i32) {
        let width = Evm::max_tick() >> amplification;
        let lower = center_tick.saturating_sub(width).max(Evm::min_tick());
        let upper = center_tick.saturating_add(width).min(Evm::max_tick());
        (lower, upper)
    }

    fn minted_liquidity(center_tick: i32, amplification: u8, current_tick: i32) -> u128 {
        let (lower_tick, upper_tick) = active_range(center_tick, amplification);
        let sqrt_lower = to_sqrt_ratio::<Evm>(lower_tick).unwrap();
        let sqrt_upper = to_sqrt_ratio::<Evm>(upper_tick).unwrap();
        let sqrt_current = to_sqrt_ratio::<Evm>(current_tick).unwrap();

        let mut low = 0u128;
        let mut high = u128::MAX;
        while low < high {
            let mid = low + (high - low) / 2 + 1;
            if within_budget(mid, sqrt_lower, sqrt_upper, sqrt_current) {
                low = mid;
            } else {
                high = mid - 1;
            }
        }
        low
    }

    fn within_budget(
        liquidity: u128,
        sqrt_lower: U256,
        sqrt_upper: U256,
        sqrt_current: U256,
    ) -> bool {
        if let Some((needed0, needed1)) =
            required_amounts(liquidity, sqrt_lower, sqrt_upper, sqrt_current)
        {
            needed0 <= POSITION_AMOUNT && needed1 <= POSITION_AMOUNT
        } else {
            false
        }
    }

    fn required_amounts(
        liquidity: u128,
        sqrt_lower: U256,
        sqrt_upper: U256,
        sqrt_current: U256,
    ) -> Option<(u128, u128)> {
        if sqrt_current <= sqrt_lower {
            let needed0 = amount0_delta(sqrt_lower, sqrt_upper, liquidity, true).ok()?;
            Some((needed0, 0))
        } else if sqrt_current >= sqrt_upper {
            let needed1 = amount1_delta(sqrt_lower, sqrt_upper, liquidity, true).ok()?;
            Some((0, needed1))
        } else {
            let needed0 = amount0_delta(sqrt_current, sqrt_upper, liquidity, true).ok()?;
            let needed1 = amount1_delta(sqrt_lower, sqrt_current, liquidity, true).ok()?;
            Some((needed0, needed1))
        }
    }

    fn quote_amount(
        pool: &StableswapPool,
        token: Address,
        amount: i128,
    ) -> Quote<StableswapPoolResources, FullRangePoolState> {
        pool.quote(QuoteParams {
            token_amount: TokenAmount { token, amount },
            sqrt_ratio_limit: None,
            override_state: None,
            meta: (),
        })
        .unwrap()
    }

    #[test]
    fn amplification_26_token0_in() {
        let pool = build_pool(0, 26, 0);

        let quote = quote_amount(&pool, Evm::zero_address(), SMALL_AMOUNT);

        assert_eq!(quote.consumed_amount, SMALL_AMOUNT);
        assert_eq!(quote.calculated_amount, 999_999_999_500_000);
    }

    #[test]
    fn amplification_26_token1_in() {
        let pool = build_pool(0, 26, 0);

        let quote = quote_amount(&pool, Evm::one_address(), SMALL_AMOUNT);

        assert_eq!(quote.consumed_amount, SMALL_AMOUNT);
        assert_eq!(quote.calculated_amount, 999_999_999_500_000);
    }

    #[test]
    fn amplification_1_token0_in() {
        let pool = build_pool(0, 1, 0);

        let quote = quote_amount(&pool, Evm::zero_address(), SMALL_AMOUNT);

        assert_eq!(quote.consumed_amount, SMALL_AMOUNT);
        assert_eq!(quote.calculated_amount, 999_000_999_001_231);
    }

    #[test]
    fn amplification_1_token1_in() {
        let pool = build_pool(0, 1, 0);

        let quote = quote_amount(&pool, Evm::one_address(), SMALL_AMOUNT);

        assert_eq!(quote.consumed_amount, SMALL_AMOUNT);
        assert_eq!(quote.calculated_amount, 999_000_999_001_231);
    }

    #[test]
    fn outside_range_has_no_liquidity() {
        let amplification = 10;
        let (_, upper) = active_range(0, amplification);
        let outside_tick = (upper + 1_000).min(Evm::max_tick());
        let pool = StableswapPool::new(
            key(0, amplification),
            state(
                outside_tick,
                minted_liquidity(0, amplification, outside_tick),
            ),
        )
        .unwrap();

        let quote = pool
            .quote(QuoteParams {
                token_amount: TokenAmount {
                    token: Evm::one_address(),
                    amount: SMALL_AMOUNT,
                },
                sqrt_ratio_limit: None,
                override_state: None,
                meta: (),
            })
            .unwrap();

        assert_eq!(quote.consumed_amount, 0);
        assert_eq!(quote.calculated_amount, 0);
        assert!(quote.state_after.sqrt_ratio >= pool.upper_price);
    }

    #[test]
    fn swap_through_range_boundary() {
        let amplification = 10;
        let (lower, upper) = active_range(0, amplification);
        let start_tick = upper - 100;
        let pool = build_pool(0, amplification, start_tick);

        let quote = pool
            .quote(QuoteParams {
                token_amount: TokenAmount {
                    token: Evm::zero_address(),
                    amount: 1_000_000_000_000_000_000i128,
                },
                sqrt_ratio_limit: None,
                override_state: None,
                meta: (),
            })
            .unwrap();

        assert!(quote.consumed_amount > 0);
        assert!(quote.calculated_amount > 0);
        assert!(quote.state_after.sqrt_ratio <= to_sqrt_ratio::<Evm>(lower + 10).unwrap());
        assert_eq!(quote.execution_resources.initialized_ticks_crossed, 0);
    }

    #[test]
    fn inside_range_has_liquidity() {
        let amplification = 10;
        let (lower, upper) = active_range(0, amplification);
        let mid_tick = (lower + upper) / 2;
        let pool = build_pool(0, amplification, mid_tick);

        let quote = quote_amount(&pool, Evm::zero_address(), SMALL_AMOUNT);

        assert_eq!(quote.consumed_amount, SMALL_AMOUNT);
        assert!(quote.calculated_amount > 0);
        assert!(quote.calculated_amount < SMALL_AMOUNT as u128);
    }
}
