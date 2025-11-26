use crate::{
    chain::evm::Evm,
    math::swap::{compute_step, is_price_increasing, ComputeStepError},
};
use crate::{
    chain::Chain,
    quoting::types::{Pool, PoolKey, Quote, QuoteParams},
};
use crate::{private, quoting::types::PoolState};
use derive_more::{Add, AddAssign, Sub, SubAssign};
use num_traits::Zero;
use ruint::aliases::U256;
use thiserror::Error;

/// Full range pool with constant liquidity across the entire price range.
#[derive(Clone, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct FullRangePool {
    /// Immutable pool configuration key.
    key: FullRangePoolKey,
    /// Current pool state.
    state: FullRangePoolState,
}

/// Unique identifier for a [`FullRangePool`].
pub type FullRangePoolKey =
    PoolKey<<Evm as Chain>::Address, <Evm as Chain>::Fee, FullRangePoolTypeConfig>;

/// Pool type config placeholder for a full range pool.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct FullRangePoolTypeConfig;

/// Price/liquidity state for a [`FullRangePool`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct FullRangePoolState {
    /// Current square root price ratio.
    pub sqrt_ratio: U256,
    /// Current active liquidity.
    pub liquidity: u128,
}

/// Resources consumed during full range swap execution.
#[derive(Clone, Copy, Default, Debug, PartialEq, Eq, Hash, Add, AddAssign, Sub, SubAssign)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct FullRangePoolResources {
    /// Whether price changed when no override was provided.
    pub no_override_price_change: u32,
}

/// Errors that can occur when constructing a [`FullRangePool`].
#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, Error)]
pub enum FullRangePoolConstructionError {
    #[error("token0 must be less than token1")]
    TokenOrderInvalid,
    #[error("sqrt ratio out of bounds")]
    SqrtRatioInvalid,
}

/// Errors that can occur when quoting a [`FullRangePool`].
#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, Error)]
pub enum FullRangePoolQuoteError {
    #[error("invalid token")]
    InvalidToken,
    #[error("invalid price limit")]
    InvalidSqrtRatioLimit,
    #[error("failed swap step computation")]
    FailedComputeSwapStep(#[from] ComputeStepError),
}

impl FullRangePool {
    pub fn new(
        key: FullRangePoolKey,
        state: FullRangePoolState,
    ) -> Result<Self, FullRangePoolConstructionError> {
        if !(key.token0 < key.token1) {
            return Err(FullRangePoolConstructionError::TokenOrderInvalid);
        }

        if state.sqrt_ratio < Evm::min_sqrt_ratio() || state.sqrt_ratio > Evm::max_sqrt_ratio() {
            return Err(FullRangePoolConstructionError::SqrtRatioInvalid);
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

impl Pool for FullRangePool {
    type Address = <Evm as Chain>::Address;
    type Fee = <Evm as Chain>::Fee;
    type Resources = FullRangePoolResources;
    type State = FullRangePoolState;
    type QuoteError = FullRangePoolQuoteError;
    type Meta = ();
    type PoolTypeConfig = FullRangePoolTypeConfig;

    fn key(&self) -> FullRangePoolKey {
        self.key
    }

    fn state(&self) -> Self::State {
        self.state
    }

    fn quote(
        &self,
        params: QuoteParams<<Evm as Chain>::Address, Self::State, Self::Meta>,
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
            if limit < Evm::min_sqrt_ratio() {
                return Err(FullRangePoolQuoteError::InvalidSqrtRatioLimit);
            }
            if limit > Evm::max_sqrt_ratio() {
                return Err(FullRangePoolQuoteError::InvalidSqrtRatioLimit);
            }
            limit
        } else {
            if is_increasing {
                Evm::max_sqrt_ratio_full_range()
            } else {
                Evm::min_sqrt_ratio_full_range()
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

impl PoolState for FullRangePoolState {
    fn sqrt_ratio(&self) -> U256 {
        self.sqrt_ratio
    }

    fn liquidity(&self) -> u128 {
        self.liquidity
    }
}

impl private::Sealed for FullRangePool {}
impl private::Sealed for FullRangePoolState {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        chain::tests::ChainTest,
        quoting::types::{PoolConfig, TokenAmount},
    };

    fn pool_key(fee: u64) -> FullRangePoolKey {
        PoolKey {
            token0: Evm::zero_address(),
            token1: Evm::one_address(),
            config: PoolConfig {
                pool_type_config: FullRangePoolTypeConfig,
                fee,
                extension: Evm::zero_address(),
            },
        }
    }

    use super::FullRangePoolConstructionError;

    #[test]
    fn test_token0_lt_token1() {
        let result = FullRangePool::new(
            PoolKey {
                token0: Evm::zero_address(),
                token1: Evm::zero_address(),
                config: PoolConfig {
                    extension: Evm::zero_address(),
                    fee: 0,
                    pool_type_config: FullRangePoolTypeConfig,
                },
            },
            FullRangePoolState {
                sqrt_ratio: U256::ONE << 128,
                liquidity: 0,
            },
        );
        assert_eq!(
            result.unwrap_err(),
            FullRangePoolConstructionError::TokenOrderInvalid
        );
    }

    #[test]
    fn test_quote_zero_liquidity() {
        let pool = FullRangePool::new(
            pool_key(0),
            FullRangePoolState {
                sqrt_ratio: U256::ONE << 128,
                liquidity: 0,
            },
        )
        .expect("Pool creation should succeed");

        let params = QuoteParams {
            token_amount: TokenAmount {
                amount: 1000,
                token: Evm::zero_address(),
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
                sqrt_ratio: U256::ONE << 128,
                liquidity: 1_000_000,
            },
        )
        .expect("Pool creation should succeed");

        let params = QuoteParams {
            token_amount: TokenAmount {
                amount: 1000,
                token: Evm::zero_address(),
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
                sqrt_ratio: U256::ONE << 128,
                liquidity: 1_000_000,
            },
        )
        .expect("Pool creation should succeed");

        let params = QuoteParams {
            token_amount: TokenAmount {
                amount: 1000,
                token: Evm::one_address(),
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
                sqrt_ratio: U256::ONE << 128,
                liquidity: 1_000_000,
            },
        )
        .expect("Pool creation should succeed");

        let params = QuoteParams {
            token_amount: TokenAmount {
                amount: 10000,
                token: Evm::zero_address(),
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
