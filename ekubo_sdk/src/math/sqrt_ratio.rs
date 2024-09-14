use crate::math::muldiv::{muldiv, MuldivError};
use crate::math::uint::U256;
use num_traits::Zero;

#[derive(Debug, PartialEq)]
pub enum PriceMathError {
    NoLiquidity,
    Overflow,
    InvalidDenominator,
    NegativeResult,
    ExceedsMaxValue,
    MuldivError(MuldivError),
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

    let numerator1 = U256::from(liquidity) << 128;

    if amount0 < 0 {
        // amount0 is negative
        let amount0_abs = U256::from(amount0.checked_abs().ok_or(PriceMathError::Overflow)?);

        // product = amount0_abs * sqrt_ratio
        let product = amount0_abs.checked_mul(sqrt_ratio).ok_or(PriceMathError::Overflow)?;

        let denominator = numerator1.checked_sub(product).ok_or(PriceMathError::Overflow)?;

        muldiv(numerator1, sqrt_ratio, denominator, true).map_err(PriceMathError::MuldivError)
    } else {
        // amount0 is positive
        let amount0_u256 = U256::from(amount0);

        let denom_p1 = numerator1 / sqrt_ratio;

        let denom = denom_p1
            .checked_add(amount0_u256)
            .ok_or(PriceMathError::Overflow)?;

        muldiv(numerator1, U256::one(), denom, true)
            .map_err(PriceMathError::MuldivError)
    }
}

const TWO_POW_128: U256 = U256([0, 0, 1, 0]);

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

    let amount1_abs = U256::from(amount1.abs());

    let round_up = amount1 < 0;

    let quotient = muldiv(amount1_abs, TWO_POW_128, liquidity.into(), round_up)
        .map_err(PriceMathError::MuldivError)?;

    if amount1 < 0 {
        sqrt_ratio
            .checked_sub(quotient)
            .ok_or(PriceMathError::NegativeResult)
    } else {
        sqrt_ratio
            .checked_add(quotient)
            .ok_or(PriceMathError::Overflow)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_next_sqrt_ratio_from_amount0_add_price_goes_down() {
        // Corresponds to:
        // nextSqrtRatioFromAmount0(1n << 128n, 1000000n, 1000n)
        let sqrt_ratio = U256::from(1u64) << 128;
        let liquidity = 1_000_000u128;
        let amount0 = 1000i128;
        let result = next_sqrt_ratio_from_amount0(sqrt_ratio, liquidity, amount0).unwrap();
        let expected = U256::from_dec_str("339942424496442021441932674757011200256").unwrap();
        assert_eq!(result, expected);
    }

    #[test]
    fn test_next_sqrt_ratio_from_amount0_exact_out_overflow() {
        // Corresponds to:
        // nextSqrtRatioFromAmount0(1n << 128n, 1n, -100000000000000n)
        let sqrt_ratio = U256::from(1u64) << 128;
        let liquidity = 1u128;
        let amount0 = -100_000_000_000_000i128;
        let result = next_sqrt_ratio_from_amount0(sqrt_ratio, liquidity, amount0);
        assert!(result.is_err());
        assert_eq!(result.err().unwrap(), PriceMathError::Overflow);
    }

    #[test]
    fn test_next_sqrt_ratio_from_amount0_exact_in_cant_underflow() {
        // Corresponds to:
        // nextSqrtRatioFromAmount0(1n << 128n, 1n, 100000000000000n)
        let sqrt_ratio = U256::from(1u64) << 128;
        let liquidity = 1u128;
        let amount0 = 100_000_000_000_000i128;
        let result = next_sqrt_ratio_from_amount0(sqrt_ratio, liquidity, amount0).unwrap();
        let expected = U256::from_dec_str("3402823669209350606397054").unwrap();
        assert_eq!(result, expected);
    }

    #[test]
    fn test_next_sqrt_ratio_from_amount0_sub_price_goes_up() {
        // Corresponds to:
        // nextSqrtRatioFromAmount0(1n << 128n, 100000000000n, -1000n)
        let sqrt_ratio = U256::from(1u64) << 128;
        let liquidity = 100_000_000_000u128;
        let amount0 = -1000i128;
        let result = next_sqrt_ratio_from_amount0(sqrt_ratio, liquidity, amount0).unwrap();
        let expected =
            U256::from_dec_str("340282370323762166700996274441730955874").unwrap();
        assert_eq!(result, expected);
    }

    #[test]
    fn test_next_sqrt_ratio_from_amount1_add_price_goes_up() {
        // Corresponds to:
        // nextSqrtRatioFromAmount1(1n << 128n, 1000000n, 1000n)
        let sqrt_ratio = U256::from(1u64) << 128;
        let liquidity = 1_000_000u128;
        let amount1 = 1000i128;
        let result = next_sqrt_ratio_from_amount1(sqrt_ratio, liquidity, amount1).unwrap();
        let expected = U256::from_dec_str("340622649287859401926837982039199979667").unwrap();
        assert_eq!(result, expected);
    }

    #[test]
    fn test_next_sqrt_ratio_from_amount1_exact_out_overflow() {
        // Corresponds to:
        // nextSqrtRatioFromAmount1(1n << 128n, 1n, -100000000000000n)
        let sqrt_ratio = U256::from(1u64) << 128;
        let liquidity = 1u128;
        let amount1 = -100_000_000_000_000i128;
        let result = next_sqrt_ratio_from_amount1(sqrt_ratio, liquidity, amount1);
        assert!(result.is_err());
        assert_eq!(result.err().unwrap(), PriceMathError::NegativeResult);
    }

    #[test]
    fn test_next_sqrt_ratio_from_amount1_exact_in_cant_underflow() {
        // Corresponds to:
        // nextSqrtRatioFromAmount1(1n << 128n, 1n, 100000000000000n)
        let sqrt_ratio = U256::from(1u64) << 128;
        let liquidity = 1u128;
        let amount1 = 100_000_000_000_000i128;
        let result = next_sqrt_ratio_from_amount1(sqrt_ratio, liquidity, amount1).unwrap();
        let expected = U256::from_dec_str("34028236692094186628704381681640284520207431768211456").unwrap();
        assert_eq!(result, expected);
    }

    #[test]
    fn test_next_sqrt_ratio_from_amount1_sub_price_goes_down() {
        // Corresponds to:
        // nextSqrtRatioFromAmount1(1n << 128n, 100000000000n, -1000n)
        let sqrt_ratio = U256::from(1u64) << 128;
        let liquidity = 100_000_000_000u128;
        let amount1 = -1000i128;
        let result = next_sqrt_ratio_from_amount1(sqrt_ratio, liquidity, amount1).unwrap();
        let expected =
            U256::from_dec_str("340282363518114794253989972798022137138").unwrap();
        assert_eq!(result, expected);
    }
}

