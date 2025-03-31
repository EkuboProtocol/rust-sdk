//! Error types for the Ekubo SDK.

/// Errors that can occur when constructing a BasePool.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum BasePoolError {
    /// Token0 must be less than token1.
    TokenOrderInvalid,
    /// Tick spacing must be less than or equal to max tick spacing.
    TickSpacingTooLarge,
    /// Ticks must be sorted in ascending order.
    TicksNotSorted,
    /// All ticks must be a multiple of tick_spacing.
    TickNotMultipleOfSpacing,
    /// The total liquidity across all ticks must sum to zero.
    TotalLiquidityNotZero,
    /// Active liquidity doesn't match the sum of liquidity deltas before the active tick.
    ActiveLiquidityMismatch,
    /// The sqrt_ratio of active tick is not less than or equal to current sqrt_ratio.
    ActiveTickSqrtRatioInvalid,
    /// current sqrt_ratio must be lower than the first tick's sqrt_ratio when active_tick_index is none.
    SqrtRatioTooHighWithNoActiveTick,
    /// The active tick index is out of bounds.
    ActiveTickIndexOutOfBounds,
    /// Invalid tick index.
    InvalidTickIndex(i32),
}

/// Errors that can occur when constructing a FullRangePool.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum FullRangePoolError {
    /// Token0 must be less than token1.
    TokenOrderInvalid,
}

/// Errors that can occur when constructing an OraclePool.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum OraclePoolError {
    /// Errors from the underlying FullRangePool constructor.
    FullRangePoolError(FullRangePoolError),
}

/// Errors that can occur when constructing a TwammPool.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum TwammPoolError {
    /// Errors from the underlying FullRangePool constructor.
    FullRangePoolError(FullRangePoolError),
    /// Sale rate deltas are not ordered or not greater than last_execution_time.
    SaleRateDeltasInvalid,
    /// Sum of current sale rate and sale rate deltas must be zero.
    SaleRateDeltaSumNonZero,
}
