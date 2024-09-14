use crate::math::uint::{U256, U512};

#[derive(Debug, PartialEq)]
pub enum MuldivError {
    Overflow,
    DenominatorZero,
}

pub(crate) fn muldiv(x: U256, y: U256, d: U256, round_up: bool) -> Result<U256, MuldivError> {
    if d.is_zero() {
        return Err(MuldivError::DenominatorZero);
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
}
