#[cfg(feature = "evm")]
pub mod boosted_fees;
pub mod concentrated;
#[cfg(feature = "evm")]
pub mod full_range;
#[cfg(feature = "starknet")]
pub mod limit_order;
#[cfg(feature = "evm")]
pub mod mev_capture;
pub mod oracle;
#[cfg(feature = "starknet")]
pub mod spline;
#[cfg(feature = "evm")]
pub mod stableswap;
pub mod twamm;

use crate::quoting::types::PoolKey;
use thiserror::Error;

/// Errors shared by pool constructors.
#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, Error)]
pub enum CommonPoolConstructionError {
    /// Token0 must be less than token1.
    #[error("token0 must be less than token1")]
    TokenOrderInvalid,
}

/// Errors shared by pool quote implementations.
#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, Error)]
pub enum CommonPoolQuoteError {
    #[error("specified token not part of the pool")]
    InvalidToken,
}

/// Validates `token0 < token1` invariant across pool types.
pub fn ensure_valid_token_order<A, F, C>(
    key: &PoolKey<A, F, C>,
) -> Result<(), CommonPoolConstructionError>
where
    A: PartialOrd,
{
    if key.token0 < key.token1 {
        Ok(())
    } else {
        Err(CommonPoolConstructionError::TokenOrderInvalid)
    }
}

/// Returns whether `token` matches token1 in the pool, or an error if it is not part of the pool.
pub fn is_token1<A, F, C>(key: &PoolKey<A, F, C>, token: A) -> Result<bool, CommonPoolQuoteError>
where
    A: PartialEq + Copy,
{
    if token == key.token1 {
        Ok(true)
    } else if token == key.token0 {
        Ok(false)
    } else {
        Err(CommonPoolQuoteError::InvalidToken)
    }
}
