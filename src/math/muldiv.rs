use crate::math::uint::U256;
use num_traits::Zero;

#[derive(Debug, PartialEq)]
pub enum MuldivError {
    Overflow,
    DenominatorZero,
}

uint::construct_uint! {
    struct U512(8);
}

impl From<U256> for U512 {
    fn from(value: U256) -> Self {
        let mut result = U512::default();
        for (i, &limb) in value.0.iter().enumerate() {
            result.0[i] = limb;
        }
        result
    }
}

impl TryFrom<U512> for U256 {
    type Error = ();

    fn try_from(value: U512) -> Result<Self, Self::Error> {
        let mut result = U256::default();
        for (i, &limb) in value.0.iter().enumerate() {
            if i >= 4 && !limb.is_zero() {
                return Err(());
            }
            if i < 4 {
                result.0[i] = limb;
            }
        }
        Ok(result)
    }
}

pub(crate) fn muldiv(x: U256, y: U256, d: U256, round_up: bool) -> Result<U256, MuldivError> {
    if d.is_zero() {
        return Err(MuldivError::DenominatorZero);
    }

    if y == U256::one() {
        let (quotient, remainder) = x.div_mod(d);
        return if round_up && !remainder.is_zero() {
            Ok(quotient + 1)
        } else {
            Ok(quotient)
        };
    }

    let intermediate: U512 = U512::from(x) * U512::from(y);
    let (quotient, remainder) = intermediate.div_mod(U512::from(d));

    let result = if round_up && !remainder.is_zero() {
        quotient + U512::one()
    } else {
        quotient
    };

    result.try_into().map_err(|_| MuldivError::Overflow)
}


#[cfg(test)]
mod tests {
    use super::*;
    use crate::math::uint::U256;

    #[test]
    fn test_muldiv_no_rounding() {
        // Test without rounding
        let x = U256::from(6);
        let y = U256::from(7);
        let d = U256::from(2);
        let result = muldiv(x, y, d, false).unwrap();
        assert_eq!(result, U256::from(21)); // (6 * 7) / 2 = 21
    }

    #[test]
    fn test_muldiv_with_rounding() {
        // Test with rounding up
        let x = U256::from(6);
        let y = U256::from(7);
        let d = U256::from(4);
        let result = muldiv(x, y, d, true).unwrap();
        assert_eq!(result, U256::from(11)); // (6 * 7) / 4 = 10.5, rounds up to 11
    }

    #[test]
    fn test_muldiv_no_rounding_needed() {
        // Test where rounding doesn't change the result
        let x = U256::from(8);
        let y = U256::from(2);
        let d = U256::from(4);
        let result = muldiv(x, y, d, true).unwrap();
        assert_eq!(result, U256::from(4)); // (8 * 2) / 4 = 4, exact division
    }

    #[test]
    fn test_muldiv_divide_by_zero() {
        // Test division by zero
        let x = U256::from(1);
        let y = U256::from(1);
        let d = U256::zero();
        let result = muldiv(x, y, d, false);
        assert!(matches!(result, Err(MuldivError::DenominatorZero)));
    }

    #[test]
    fn test_muldiv_overflow() {
        // Test overflow when result doesn't fit into U256
        let x = U256::max_value();
        let y = U256::from(2);
        let d = U256::from(1);
        let result = muldiv(x, y, d, false);
        assert!(matches!(result, Err(MuldivError::Overflow)));
    }

    #[test]
    fn test_muldiv_large_numbers() {
        // Test with large numbers that fit into U256
        let x = U256::from_dec_str("123456789012345678901234567890").unwrap();
        let y = U256::from_dec_str("987654321098765432109876543210").unwrap();
        let d = U256::from(1);
        let result = muldiv(x, y, d, false).unwrap();

        let expected = U256::from_dec_str("121932631137021795226185032733622923332237463801111263526900").unwrap();
        assert_eq!(result, expected);
    }

    #[test]
    fn test_muldiv_rounding_behavior() {
        // Test rounding behavior when remainder is zero
        let x = U256::from(10);
        let y = U256::from(10);
        let d = U256::from(5);
        let result = muldiv(x, y, d, true).unwrap();
        assert_eq!(result, U256::from(20)); // Exact division, no rounding needed

        // Test rounding behavior when remainder is not zero
        let d = U256::from(6);
        let result = muldiv(x, y, d, true).unwrap();
        assert_eq!(result, U256::from(17)); // (100 / 6) = 16.666..., rounds up to 17
    }

    #[test]
    fn test_muldiv_zero_numerator() {
        // Test with zero numerator
        let x = U256::zero();
        let y = U256::from(100);
        let d = U256::from(10);
        let result = muldiv(x, y, d, false).unwrap();
        assert_eq!(result, U256::zero());
    }

    #[test]
    fn test_muldiv_one_denominator() {
        // Test with denominator of one
        let x = U256::from(123456789);
        let y = U256::from(987654321);
        let d = U256::one();
        let result = muldiv(x, y, d, false).unwrap();
        let expected = U256::from(121932631112635269u64);
        assert_eq!(result, expected);
    }


    #[test]
    fn test_muldiv_max_values_no_rounding() {
        // Test with maximum U256 values that result in a valid U256 output
        let x = U256::max_value();
        let y = U256::from(1);
        let d = U256::from(1);
        let result = muldiv(x, y, d, false).unwrap();
        assert_eq!(result, U256::max_value());
    }

    #[test]
    fn test_muldiv_max_values_with_rounding() {
        // Test with maximum U256 values that result in an overflow when rounding up
        let x = U256::max_value();
        let y = U256::from(1);
        let d = U256::from(1);
        let result = muldiv(x, y, d, true).unwrap();
        assert_eq!(result, U256::max_value()); // No overflow, rounding doesn't change the result
    }

    #[test]
    fn test_muldiv_rounding_up() {
        let x = U256::MAX;
        let y = U256::from(1);
        let d = U256::from(2);
        let result = muldiv(x, y, d, true);
        assert_eq!(result.unwrap(), U256::from_dec_str("57896044618658097711785492504343953926634992332820282019728792003956564819968").unwrap());
    }

    #[test]
    fn test_muldiv_intermediate_overflow() {
        let x = U256::max_value();
        let y = U256::max_value();
        let d = U256::from(1);
        let result = muldiv(x, y, d, false);
        assert!(result.is_err()); // Should overflow as result exceeds U256::max_value()
        assert!(matches!(result, Err(MuldivError::Overflow)));
    }

    #[test]
    fn test_muldiv_result_exactly_u256_max() {
        // Test where the result is exactly U256::max_value()
        let x = U256::max_value();
        let y = U256::one();
        let d = U256::one();
        let result = muldiv(x, y, d, false).unwrap();
        assert_eq!(result, U256::max_value());
    }

    #[test]
    fn test_muldiv_result_exceeds_u256_max() {
        // Test where the result exceeds U256::max_value()
        let x = U256::max_value();
        let y = U256::from(2);
        let d = U256::one();
        let result = muldiv(x, y, d, false);
        assert!(matches!(result, Err(MuldivError::Overflow)));
    }

    #[test]
    fn test_muldiv_zero_denominator() {
        // Test division by zero with non-zero numerator
        let x = U256::from(12345);
        let y = U256::from(67890);
        let d = U256::zero();
        let result = muldiv(x, y, d, false);
        assert!(matches!(result, Err(MuldivError::DenominatorZero)));
    }

    #[test]
    fn test_muldiv_one_numerator_zero() {
        // Test with zero numerator and rounding up
        let x = U256::zero();
        let y = U256::from(12345);
        let d = U256::from(67890);
        let result = muldiv(x, y, d, true).unwrap();
        assert_eq!(result, U256::zero());
    }

    #[test]
    fn test_muldiv_max_values_rounding_up_overflow() {
        // Test where rounding up the maximum possible quotient causes overflow
        let x = U256::MAX - U256::one();
        let y = U256::MAX;
        let d = U256::MAX - U256::one();
        let result = muldiv(x, y, d, true);
        assert_eq!(
            result.unwrap(),
            U256::from_dec_str("115792089237316195423570985008687907853269984665640564039457584007913129639935").unwrap()
        );
    }

    #[test]
    fn test_muldiv_large_numbers_no_overflow() {
        // Test with large numbers that produce a result within U256
        let x = U256::from_dec_str("340282366920938463463374607431768211455").unwrap(); // U256::max_value()
        let y = U256::from(1);
        let d = U256::from(2);
        let result = muldiv(x, y, d, false).unwrap();
        let expected = U256::from_dec_str("170141183460469231731687303715884105727").unwrap();
        assert_eq!(result, expected);
    }

    #[test]
    fn test_muldiv_rounding_edge_case() {
        // Test rounding edge case where remainder is exactly half of the denominator
        let x = U256::from(5);
        let y = U256::from(5);
        let d = U256::from(2);
        let result = muldiv(x, y, d, true).unwrap();
        assert_eq!(result, U256::from(13)); // (5*5)/2 = 12.5, rounds up to 13
    }

    #[test]
    fn test_muldiv_large_intermediate_result() {
        // Test where intermediate multiplication is large but result fits in U256
        let x = U256::from_dec_str("123456789012345678901234567890").unwrap();
        let y = U256::from_dec_str("98765432109876543210987654321").unwrap();
        let d = U256::from_dec_str("1219326311370217952261850327336229233322374638011112635269").unwrap();
        let result = muldiv(x, y, d, false).unwrap();
        assert_eq!(result, U256::from(10));
    }

    #[test]
    fn test_muldiv_small_denominator_large_numerator() {
        // Test where numerator is large and denominator is small, but result fits in U256
        let x = U256::from_dec_str("340282366920938463463374607431768211455").unwrap();
        let y = U256::from(2);
        let d = U256::from(3);
        let result = muldiv(x, y, d, false).unwrap();
        let expected = U256::from_dec_str("226854911280625642308916404954512140970").unwrap();
        assert_eq!(result, expected);
    }
}
