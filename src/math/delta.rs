use crate::math::muldiv::{muldiv, MuldivError};
use crate::math::uint::U256;
use num_traits::Zero;

fn sort_ratios(sqrt_ratio_a: U256, sqrt_ratio_b: U256) -> Option<(U256, U256)> {
    let (lower, higher) = if sqrt_ratio_a < sqrt_ratio_b {
        (sqrt_ratio_a, sqrt_ratio_b)
    } else {
        (sqrt_ratio_b, sqrt_ratio_a)
    };

    if lower.is_zero() {
        None
    } else {
        Some((lower, higher))
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum AmountDeltaError {
    ZeroRatio,
    Overflow,
    MuldivError(MuldivError),
}

pub fn amount0_delta(
    sqrt_ratio_a: U256,
    sqrt_ratio_b: U256,
    liquidity: u128,
    round_up: bool,
) -> Result<u128, AmountDeltaError> {
    let (lower, upper) =
        sort_ratios(sqrt_ratio_a, sqrt_ratio_b).ok_or(AmountDeltaError::ZeroRatio)?;

    if liquidity == 0 || lower == upper {
        return Ok(0);
    }

    let result_0 = muldiv(upper - lower, U256::from(liquidity) << 128, upper, round_up)
        .map_err(AmountDeltaError::MuldivError)?;

    let (result, remainder) = result_0.div_mod(lower);
    let rounded = if round_up && !remainder.is_zero() {
        result
            .checked_add(U256::from(1))
            .ok_or(AmountDeltaError::Overflow)?
    } else {
        result
    };

    if rounded > u128::MAX.into() {
        return Err(AmountDeltaError::Overflow);
    }

    Ok(rounded.low_u128())
}
#[cfg(test)]
mod amount0_delta_tests {
    use super::*;
    use crate::math::uint::U256;

    #[test]
    fn price_down() {
        let sqrt_ratio_a = U256::from_dec_str("339942424496442021441932674757011200255").unwrap();
        let sqrt_ratio_b = U256::from_str_radix("100000000000000000000000000000000", 16).unwrap(); // Equivalent to 2^128
        let liquidity = 1_000_000u128;
        let round_up = false;

        let result = amount0_delta(sqrt_ratio_a, sqrt_ratio_b, liquidity, round_up).unwrap();

        assert_eq!(result, 1_000u128);
    }

    #[test]
    fn price_down_reverse() {
        let sqrt_ratio_a = U256::from_str_radix("100000000000000000000000000000000", 16).unwrap(); // Equivalent to 2^128
        let sqrt_ratio_b = U256::from_dec_str("339942424496442021441932674757011200255").unwrap();
        let liquidity = 1_000_000u128;
        let round_up = false;

        let result = amount0_delta(sqrt_ratio_a, sqrt_ratio_b, liquidity, round_up).unwrap();

        assert_eq!(result, 1_000u128);
    }

    #[test]
    fn price_example_down() {
        let sqrt_ratio_a = U256::from_str_radix("100000000000000000000000000000000", 16).unwrap(); // Equivalent to 2^128
        let two_pow_128 = U256::from(1u64) << 128;
        let sqrt_ratio_b =
            U256::from_dec_str("34028236692093846346337460743176821145").unwrap() + two_pow_128;
        let liquidity = 1_000_000_000_000_000_000u128; // 1e18
        let round_up = false;

        let result = amount0_delta(sqrt_ratio_a, sqrt_ratio_b, liquidity, round_up).unwrap();

        assert_eq!(result, 90_909_090_909_090_909u128);
    }

    #[test]
    fn price_example_up() {
        let sqrt_ratio_a = U256::from_str_radix("100000000000000000000000000000000", 16).unwrap(); // Equivalent to 2^128
        let two_pow_128 = U256::from(1u64) << 128;
        let sqrt_ratio_b =
            U256::from_dec_str("34028236692093846346337460743176821145").unwrap() + two_pow_128;
        let liquidity = 1_000_000_000_000_000_000u128; // 1e18
        let round_up = true;

        let result = amount0_delta(sqrt_ratio_a, sqrt_ratio_b, liquidity, round_up).unwrap();

        assert_eq!(result, 90_909_090_909_090_910u128);
    }
}

const TWO_POW_128: U256 = U256([0, 0, 1, 0]);

pub fn amount1_delta(
    sqrt_ratio_a: U256,
    sqrt_ratio_b: U256,
    liquidity: u128,
    round_up: bool,
) -> Result<u128, AmountDeltaError> {
    let (lower, upper) =
        sort_ratios(sqrt_ratio_a, sqrt_ratio_b).ok_or(AmountDeltaError::ZeroRatio)?;
    if liquidity.is_zero() || lower == upper {
        return Ok(Zero::zero());
    }

    let result = muldiv(
        U256::from(liquidity),
        upper - lower,
        TWO_POW_128.clone(),
        round_up,
    )
    .map_err(AmountDeltaError::MuldivError)?;
    if result > u128::MAX.into() {
        Err(AmountDeltaError::Overflow)
    } else {
        Ok(result.low_u128())
    }
}

#[cfg(test)]
mod amount1_delta_tests {
    use super::*;
    use crate::math::tick::{MAX_SQRT_RATIO, MIN_SQRT_RATIO};
    use crate::math::uint::U256;

    #[test]
    fn price_down() {
        let sqrt_ratio_a = U256::from_dec_str("339942424496442021441932674757011200255").unwrap();
        let sqrt_ratio_b = U256::from_str_radix("100000000000000000000000000000000", 16).unwrap(); // Equivalent to 2^128
        let liquidity = 1_000_000u128;
        let round_up = false;

        let result = amount1_delta(sqrt_ratio_a, sqrt_ratio_b, liquidity, round_up).unwrap();

        assert_eq!(result, 999u128);
    }

    #[test]
    fn price_down_reverse() {
        let sqrt_ratio_a = U256::from_str_radix("100000000000000000000000000000000", 16).unwrap(); // 2^128
        let sqrt_ratio_b = U256::from_dec_str("339942424496442021441932674757011200255").unwrap();
        let liquidity = 1_000_000u128;
        let round_up = false;

        let result = amount1_delta(sqrt_ratio_a, sqrt_ratio_b, liquidity, round_up).unwrap();

        assert_eq!(result, 999u128);
    }

    #[test]
    fn price_up() {
        let sqrt_ratio_a = U256::from_dec_str("340622989910849312776150758189957120").unwrap()
            + (U256::one() << 128);
        let sqrt_ratio_b = U256::from_str_radix("100000000000000000000000000000000", 16).unwrap(); // 2^128
        let liquidity = 1_000_000u128;
        let round_up = false;

        let result = amount1_delta(sqrt_ratio_a, sqrt_ratio_b, liquidity, round_up).unwrap();

        assert_eq!(result, 1001u128);
    }

    #[test]
    fn price_up_reverse() {
        let sqrt_ratio_a = U256::from_str_radix("100000000000000000000000000000000", 16).unwrap(); // 2^128
        let sqrt_ratio_b = U256::from_dec_str("339942424496442021441932674757011200255").unwrap();
        let liquidity = 1_000_000u128;
        let round_up = true;

        let result = amount1_delta(sqrt_ratio_a, sqrt_ratio_b, liquidity, round_up).unwrap();

        assert_eq!(result, 1000u128);
    }

    #[test]
    fn price_example_down() {
        let sqrt_ratio_a = U256::from_str_radix("100000000000000000000000000000000", 16).unwrap(); // 2^128
        let sqrt_ratio_b = U256::from_dec_str("309347606291762239512158734028880192232").unwrap();
        let liquidity = 1_000_000_000_000_000_000u128; // 1e18
        let round_up = false;

        let result = amount1_delta(sqrt_ratio_a, sqrt_ratio_b, liquidity, round_up).unwrap();

        assert_eq!(result, 90_909_090_909_090_909u128);
    }

    #[test]
    fn price_example_up() {
        let sqrt_ratio_a = U256::from_str_radix("100000000000000000000000000000000", 16).unwrap(); // 2^128
        let sqrt_ratio_b = U256::from_dec_str("309347606291762239512158734028880192232").unwrap();
        let liquidity = 1_000_000_000_000_000_000u128; // 1e18
        let round_up = true;

        let result = amount1_delta(sqrt_ratio_a, sqrt_ratio_b, liquidity, round_up).unwrap();

        assert_eq!(result, 90_909_090_909_090_910u128);
    }

    #[test]
    fn no_overflow_half_price_range() {
        let sqrt_ratio_a = U256::from_str_radix("100000000000000000000000000000000", 16).unwrap(); // 2^128
        let sqrt_ratio_b = MAX_SQRT_RATIO;
        let liquidity = 0xffffffffffffffffu128; // Maximum u64 value
        let round_up = false;

        let result = amount1_delta(sqrt_ratio_a, sqrt_ratio_b, liquidity, round_up).unwrap();

        assert_eq!(
            result,
            U256::from_dec_str("340274119756928397675478831269759003622")
                .unwrap()
                .as_u128()
        );
    }

    #[test]
    fn should_panic() {
        let sqrt_ratio_a = MIN_SQRT_RATIO;
        let sqrt_ratio_b = MAX_SQRT_RATIO;
        let liquidity = u128::MAX;
        let round_up = false;

        let result = amount1_delta(sqrt_ratio_a, sqrt_ratio_b, liquidity, round_up);

        assert!(matches!(result, Err(AmountDeltaError::Overflow)));
    }
}
