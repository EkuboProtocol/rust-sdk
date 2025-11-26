use crate::math::muldiv::{muldiv, MuldivError};
use num_traits::Zero;
use ruint::aliases::U256;
use thiserror::Error;

pub const SQRT_RATIO_ONE: U256 = U256::from_limbs([0, 0, 1, 0]);

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, Error)]
pub enum PriceMathError {
    #[error("no liquidity")]
    NoLiquidity,
    #[error("overflow")]
    Overflow,
    #[error("underflow")]
    Underflow,
    #[error("muldiv error")]
    MuldivError(#[from] MuldivError),
}

pub fn next_sqrt_ratio_from_amount0(
    sqrt_ratio: U256,
    liquidity: u128,
    amount0: i128,
) -> Result<U256, PriceMathError> {
    if amount0 == 0 {
        return Ok(sqrt_ratio);
    }

    if liquidity.is_zero() {
        return Err(PriceMathError::NoLiquidity);
    }

    let numerator1 = U256::from(liquidity) << 128u8;

    if amount0 < 0 {
        let amount0_abs = U256::try_from(amount0.checked_abs().ok_or(PriceMathError::Overflow)?)
            .map_err(|_| PriceMathError::Overflow)?;

        // product = amount0_abs * sqrt_ratio
        let product = amount0_abs
            .checked_mul(sqrt_ratio)
            .ok_or(PriceMathError::Overflow)?;

        let denominator = numerator1
            .checked_sub(product)
            .ok_or(PriceMathError::Overflow)?;

        muldiv(numerator1, sqrt_ratio, denominator, true).map_err(PriceMathError::MuldivError)
    } else {
        let amount0_u256 = U256::try_from(amount0).map_err(|_| PriceMathError::Overflow)?;

        let denom_p1 = numerator1 / sqrt_ratio;

        let denom = denom_p1
            .checked_add(amount0_u256)
            .ok_or(PriceMathError::Overflow)?;

        muldiv(numerator1, U256::ONE, denom, true).map_err(PriceMathError::MuldivError)
    }
}

pub fn next_sqrt_ratio_from_amount1(
    sqrt_ratio: U256,
    liquidity: u128,
    amount1: i128,
) -> Result<U256, PriceMathError> {
    if amount1 == 0 {
        return Ok(sqrt_ratio);
    }

    if liquidity.is_zero() {
        return Err(PriceMathError::NoLiquidity);
    }

    let amount1_abs = U256::try_from(amount1.checked_abs().ok_or(PriceMathError::Overflow)?)
        .map_err(|_| PriceMathError::Overflow)?;

    let round_up = amount1 < 0;

    let quotient = muldiv(amount1_abs, SQRT_RATIO_ONE, U256::from(liquidity), round_up)
        .map_err(PriceMathError::MuldivError)?;

    if amount1 < 0 {
        sqrt_ratio
            .checked_sub(quotient)
            .ok_or(PriceMathError::Underflow)
    } else {
        sqrt_ratio
            .checked_add(quotient)
            .ok_or(PriceMathError::Overflow)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ruint::uint;

    const LIQUIDITY_ONE: u128 = 1;
    const LIQUIDITY_MILLION: u128 = 1_000_000;
    const LIQUIDITY_HUNDRED_BILLION: u128 = 100_000_000_000;

    const AMOUNT_SMALL_POS: i128 = 1_000;
    const AMOUNT_SMALL_NEG: i128 = -1_000;
    const AMOUNT_LARGE_POS: i128 = 100_000_000_000_000;
    const AMOUNT_LARGE_NEG: i128 = -100_000_000_000_000;

    mod amount0 {
        use super::*;

        #[test]
        fn add_price_goes_down() {
            assert_eq!(
                next_sqrt_ratio_from_amount0(SQRT_RATIO_ONE, LIQUIDITY_MILLION, AMOUNT_SMALL_POS)
                    .unwrap(),
                uint!(339942424496442021441932674757011200256_U256)
            );
        }

        #[test]
        fn exact_out_overflow() {
            assert_eq!(
                next_sqrt_ratio_from_amount0(SQRT_RATIO_ONE, LIQUIDITY_ONE, AMOUNT_LARGE_NEG)
                    .unwrap_err(),
                PriceMathError::Overflow
            );
        }

        #[test]
        fn exact_in_cant_underflow() {
            assert_eq!(
                next_sqrt_ratio_from_amount0(SQRT_RATIO_ONE, LIQUIDITY_ONE, AMOUNT_LARGE_POS)
                    .unwrap(),
                uint!(3402823669209350606397054_U256)
            );
        }

        #[test]
        fn sub_price_goes_up() {
            assert_eq!(
                next_sqrt_ratio_from_amount0(
                    SQRT_RATIO_ONE,
                    LIQUIDITY_HUNDRED_BILLION,
                    AMOUNT_SMALL_NEG
                )
                .unwrap(),
                uint!(340282370323762166700996274441730955874_U256)
            );
        }
    }

    mod amount1 {
        use super::*;

        #[test]
        fn add_price_goes_up() {
            assert_eq!(
                next_sqrt_ratio_from_amount1(SQRT_RATIO_ONE, LIQUIDITY_MILLION, AMOUNT_SMALL_POS)
                    .unwrap(),
                uint!(340622649287859401926837982039199979667_U256)
            );
        }

        #[test]
        fn exact_out_overflow() {
            assert_eq!(
                next_sqrt_ratio_from_amount1(SQRT_RATIO_ONE, LIQUIDITY_ONE, AMOUNT_LARGE_NEG)
                    .unwrap_err(),
                PriceMathError::Underflow
            );
        }

        #[test]
        fn exact_in_cant_underflow() {
            assert_eq!(
                next_sqrt_ratio_from_amount1(SQRT_RATIO_ONE, LIQUIDITY_ONE, AMOUNT_LARGE_POS)
                    .unwrap(),
                uint!(34028236692094186628704381681640284520207431768211456_U256)
            );
        }

        #[test]
        fn sub_price_goes_down() {
            assert_eq!(
                next_sqrt_ratio_from_amount1(
                    SQRT_RATIO_ONE,
                    LIQUIDITY_HUNDRED_BILLION,
                    AMOUNT_SMALL_NEG
                )
                .unwrap(),
                uint!(340282363518114794253989972798022137138_U256)
            );
        }
    }
}
