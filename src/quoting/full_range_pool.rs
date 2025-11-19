use crate::{
    chain::Chain,
    quoting::types::{Pool, PoolKey, Quote, QuoteParams},
};
use crate::{
    chain::Evm,
    math::swap::{compute_step, is_price_increasing, ComputeStepError},
};
use crate::{math::uint::U256, quoting::types::PoolState};
use derive_more::{Add, AddAssign, Sub, SubAssign};
use num_traits::Zero;

// Resources consumed during any swap execution in a full range pool.
#[derive(Clone, Copy, Default, Debug, PartialEq, Eq, Add, AddAssign, Sub, SubAssign)]
pub struct FullRangePoolResources {
    pub no_override_price_change: u32,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum FullRangePoolQuoteError {
    InvalidToken,
    InvalidSqrtRatioLimit,
    FailedComputeSwapStep(ComputeStepError),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct FullRangePoolState {
    #[cfg_attr(feature = "serde", serde(with = "crate::quoting::types::serde_u256"))]
    pub sqrt_ratio: U256,
    pub liquidity: u128,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct FullRangePoolTypeConfig;
pub type FullRangePoolKey<C> = PoolKey<<C as Chain>::Fee, FullRangePoolTypeConfig>;

#[derive(Clone, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct FullRangePool {
    key: FullRangePoolKey<Evm>,
    state: FullRangePoolState,
}

/// Errors that can occur when constructing a FullRangePool.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum FullRangePoolError {
    /// Token0 must be less than token1.
    TokenOrderInvalid,
    SqrtRatioInvalid,
}

impl FullRangePool {
    pub fn new(
        key: FullRangePoolKey<Evm>,
        state: FullRangePoolState,
    ) -> Result<Self, FullRangePoolError> {
        if !(key.token0 < key.token1) {
            return Err(FullRangePoolError::TokenOrderInvalid);
        }

        if state.sqrt_ratio < Evm::MIN_SQRT_RATIO || state.sqrt_ratio > Evm::MAX_SQRT_RATIO {
            return Err(FullRangePoolError::SqrtRatioInvalid);
        }

        Ok(Self {
            key,
            state: FullRangePoolState {
                sqrt_ratio: state.sqrt_ratio,
                liquidity: state.liquidity,
            },
        })
    }
}

impl Pool<Evm> for FullRangePool {
    type Resources = FullRangePoolResources;
    type State = FullRangePoolState;
    type QuoteError = FullRangePoolQuoteError;
    type Meta = ();
    type PoolTypeConfig = FullRangePoolTypeConfig;

    fn key(&self) -> PoolKey<<Evm as Chain>::Fee, Self::PoolTypeConfig> {
        self.key
    }

    fn state(&self) -> Self::State {
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
            return Err(FullRangePoolQuoteError::InvalidToken);
        }

        let state = if let Some(override_state) = params.override_state {
            override_state
        } else {
            self.state
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
        let liquidity = state.liquidity;

        // If there's no liquidity, we can't perform a swap
        if liquidity.is_zero() {
            return Ok(Quote {
                is_price_increasing: is_increasing,
                consumed_amount: 0,
                calculated_amount: 0,
                execution_resources: Default::default(),
                state_after: state,
                fees_paid: 0,
            });
        }

        let sqrt_ratio_limit = if let Some(limit) = params.sqrt_ratio_limit {
            if is_increasing && limit < sqrt_ratio {
                return Err(FullRangePoolQuoteError::InvalidSqrtRatioLimit);
            }
            if !is_increasing && limit > sqrt_ratio {
                return Err(FullRangePoolQuoteError::InvalidSqrtRatioLimit);
            }
            if limit < Evm::MIN_SQRT_RATIO {
                return Err(FullRangePoolQuoteError::InvalidSqrtRatioLimit);
            }
            if limit > Evm::MAX_SQRT_RATIO {
                return Err(FullRangePoolQuoteError::InvalidSqrtRatioLimit);
            }
            limit
        } else {
            if is_increasing {
                Evm::MAX_SQRT_RATIO
            } else {
                Evm::MIN_SQRT_RATIO
            }
        };

        let starting_sqrt_ratio = sqrt_ratio;

        // Since we're in a full range pool, we can complete the swap in a single step
        let step = compute_step::<Evm>(
            sqrt_ratio,
            liquidity,
            sqrt_ratio_limit,
            amount,
            is_token1,
            self.key.config.fee,
        )
        .map_err(FullRangePoolQuoteError::FailedComputeSwapStep)?;

        // Update sqrt_ratio based on the swap step
        sqrt_ratio = step.sqrt_ratio_next;

        let resources = FullRangePoolResources {
            // Track if the price changed, but only if not overridden
            no_override_price_change: if starting_sqrt_ratio == self.state.sqrt_ratio
                && starting_sqrt_ratio != sqrt_ratio
            {
                1
            } else {
                0
            },
        };

        let state_after = FullRangePoolState {
            sqrt_ratio,
            liquidity,
        };

        Ok(Quote {
            is_price_increasing: is_increasing,
            consumed_amount: step.consumed_amount,
            calculated_amount: step.calculated_amount,
            execution_resources: resources,
            state_after,
            fees_paid: step.fee_amount,
        })
    }

    // Checks if the pool has any liquidity
    fn has_liquidity(&self) -> bool {
        self.state.liquidity > 0
    }

    // For full range pools, if there's liquidity, then the max tick is MAX_TICK
    fn max_tick_with_liquidity(&self) -> Option<i32> {
        self.has_liquidity().then_some(Evm::MAX_TICK)
    }

    // For full range pools, if there's liquidity, then the min tick is MIN_TICK
    fn min_tick_with_liquidity(&self) -> Option<i32> {
        self.has_liquidity().then_some(Evm::MIN_TICK)
    }

    fn is_path_dependent(&self) -> bool {
        false
    }
}

impl PoolState for FullRangePoolState {
    fn sqrt_ratio(&self) -> U256 {
        self.sqrt_ratio
    }

    fn liquidity(&self) -> u128 {
        self.liquidity
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::quoting::types::{Config, TokenAmount};

    const TOKEN0: U256 = U256([1, 0, 0, 0]);
    const TOKEN1: U256 = U256([2, 0, 0, 0]);

    fn pool_key(fee: u64) -> FullRangePoolKey<Evm> {
        PoolKey {
            token0: TOKEN0,
            token1: TOKEN1,
            config: Config {
                pool_type_config: FullRangePoolTypeConfig,
                fee,
                extension: U256::zero(),
            },
        }
    }

    use super::FullRangePoolError;

    #[test]
    fn test_token0_lt_token1() {
        let result = FullRangePool::new(
            PoolKey {
                token0: U256::zero(),
                token1: U256::zero(),
                config: Config {
                    extension: U256::zero(),
                    fee: 0,
                    pool_type_config: FullRangePoolTypeConfig,
                },
            },
            FullRangePoolState {
                sqrt_ratio: U256::one() << 128,
                liquidity: 0,
            },
        );
        assert_eq!(result.unwrap_err(), FullRangePoolError::TokenOrderInvalid);
    }

    #[test]
    fn test_quote_zero_liquidity() {
        let pool = FullRangePool::new(
            pool_key(0),
            FullRangePoolState {
                sqrt_ratio: U256::one() << 128,
                liquidity: 0,
            },
        )
        .expect("Pool creation should succeed");

        let params = QuoteParams {
            token_amount: TokenAmount {
                amount: 1000,
                token: TOKEN0,
            },
            sqrt_ratio_limit: None,
            override_state: None,
            meta: (),
        };

        let quote = pool.quote(params).expect("Failed to get quote");

        assert_eq!(quote.calculated_amount, 0);
        assert_eq!(quote.consumed_amount, 0);
        assert_eq!(quote.fees_paid, 0);
    }

    #[test]
    fn test_quote_with_liquidity_token0_input() {
        let pool = FullRangePool::new(
            pool_key(0),
            FullRangePoolState {
                sqrt_ratio: U256::one() << 128,
                liquidity: 1_000_000,
            },
        )
        .expect("Pool creation should succeed");

        let params = QuoteParams {
            token_amount: TokenAmount {
                amount: 1000,
                token: TOKEN0,
            },
            sqrt_ratio_limit: None,
            override_state: None,
            meta: (),
        };

        let quote = pool.quote(params).expect("Failed to get quote");

        assert!(quote.calculated_amount > 0);
        assert_eq!(quote.consumed_amount, 1000);
        assert_eq!(quote.execution_resources.no_override_price_change, 1);
    }

    #[test]
    fn test_quote_with_liquidity_token1_input() {
        let pool = FullRangePool::new(
            pool_key(0),
            FullRangePoolState {
                sqrt_ratio: U256::one() << 128,
                liquidity: 1_000_000,
            },
        )
        .expect("Pool creation should succeed");

        let params = QuoteParams {
            token_amount: TokenAmount {
                amount: 1000,
                token: TOKEN1,
            },
            sqrt_ratio_limit: None,
            override_state: None,
            meta: (),
        };

        let quote = pool.quote(params).expect("Failed to get quote");

        assert!(quote.calculated_amount > 0);
        assert_eq!(quote.consumed_amount, 1000);
        assert_eq!(quote.execution_resources.no_override_price_change, 1);
    }

    #[test]
    fn test_with_fee() {
        let pool = FullRangePool::new(
            pool_key(1 << 32), // 0.01% fee
            FullRangePoolState {
                sqrt_ratio: U256::one() << 128,
                liquidity: 1_000_000,
            },
        )
        .expect("Pool creation should succeed");

        let params = QuoteParams {
            token_amount: TokenAmount {
                amount: 10000,
                token: TOKEN0,
            },
            sqrt_ratio_limit: None,
            override_state: None,
            meta: (),
        };

        let quote = pool.quote(params).expect("Failed to get quote");

        // Assert that a fee was applied
        assert!(quote.fees_paid > 0);
    }
}
