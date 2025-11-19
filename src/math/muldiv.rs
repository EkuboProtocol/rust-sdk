use crate::math::uint::U256;
use num_traits::Zero;

uint::construct_uint! {
    struct U512(8);
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum MuldivError {
    Overflow,
    DenominatorZero,
}

pub fn muldiv(x: U256, y: U256, d: U256, round_up: bool) -> Result<U256, MuldivError> {
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::math::uint::U256;

    #[test]
    fn no_rounding() {
        assert_eq!(
            muldiv(U256::from(6), U256::from(7), U256::from(2), false).unwrap(),
            U256::from(21)
        );
    }

    #[test]
    fn with_rounding() {
        assert_eq!(
            muldiv(U256::from(6), U256::from(7), U256::from(4), true).unwrap(),
            U256::from(11)
        );
    }

    #[test]
    fn no_rounding_needed() {
        assert_eq!(
            muldiv(U256::from(8), U256::from(2), U256::from(4), true).unwrap(),
            U256::from(4)
        );
    }

    #[test]
    fn div_by_zero() {
        assert!(matches!(
            muldiv(U256::from(1), U256::from(1), U256::zero(), false),
            Err(MuldivError::DenominatorZero)
        ));
    }

    #[test]
    fn overflow() {
        assert!(matches!(
            muldiv(U256::max_value(), U256::from(2), U256::from(1), false),
            Err(MuldivError::Overflow)
        ));
    }

    #[test]
    fn large_numbers() {
        assert_eq!(
            muldiv(
                U256::from_dec_str("123456789012345678901234567890").unwrap(),
                U256::from_dec_str("987654321098765432109876543210").unwrap(),
                U256::from(1),
                false
            )
            .unwrap(),
            U256::from_dec_str("121932631137021795226185032733622923332237463801111263526900")
                .unwrap()
        );
    }

    #[test]
    fn rounding_behavior_remainder_zero() {
        assert_eq!(
            muldiv(U256::from(10), U256::from(10), U256::from(5), true).unwrap(),
            U256::from(20)
        );
    }

    #[test]
    fn rounding_behavior_remainder_non_zero() {
        assert_eq!(
            muldiv(U256::from(10), U256::from(10), U256::from(6), true).unwrap(),
            U256::from(17)
        );
    }

    #[test]
    fn zero_numerator() {
        assert_eq!(
            muldiv(U256::zero(), U256::from(100), U256::from(10), false).unwrap(),
            U256::zero()
        );
    }

    #[test]
    fn one_denominator() {
        assert_eq!(
            muldiv(
                U256::from(123456789),
                U256::from(987654321),
                U256::one(),
                false
            )
            .unwrap(),
            U256::from(121932631112635269u64)
        );
    }

    #[test]
    fn max_values_no_rounding() {
        assert_eq!(
            muldiv(U256::max_value(), U256::from(1), U256::from(1), false).unwrap(),
            U256::max_value()
        );
    }

    #[test]
    fn max_values_with_rounding() {
        assert_eq!(
            muldiv(U256::max_value(), U256::from(1), U256::from(1), true).unwrap(),
            U256::max_value()
        );
    }

    #[test]
    fn rounding_up() {
        assert_eq!(
            muldiv(U256::MAX, U256::from(1), U256::from(2), true).unwrap(),
            U256::from_dec_str(
                "57896044618658097711785492504343953926634992332820282019728792003956564819968"
            )
            .unwrap()
        );
    }

    #[test]
    fn intermediate_overflow() {
        assert!(matches!(
            muldiv(U256::max_value(), U256::max_value(), U256::from(1), false),
            Err(MuldivError::Overflow)
        ));
    }

    #[test]
    fn result_exactly_u256_max() {
        assert_eq!(
            muldiv(U256::max_value(), U256::one(), U256::one(), false).unwrap(),
            U256::max_value()
        );
    }

    #[test]
    fn result_exceeds_u256_max() {
        assert!(matches!(
            muldiv(U256::max_value(), U256::from(2), U256::one(), false),
            Err(MuldivError::Overflow)
        ));
    }

    #[test]
    fn zero_denominator() {
        assert!(matches!(
            muldiv(U256::from(12345), U256::from(67890), U256::zero(), false),
            Err(MuldivError::DenominatorZero)
        ));
    }

    #[test]
    fn one_numerator_zero() {
        assert_eq!(
            muldiv(U256::zero(), U256::from(12345), U256::from(67890), true).unwrap(),
            U256::zero()
        );
    }

    #[test]
    fn max_values_rounding_up_overflow() {
        assert_eq!(
            muldiv(
                U256::MAX - U256::one(),
                U256::MAX,
                U256::MAX - U256::one(),
                true
            )
            .unwrap(),
            U256::from_dec_str(
                "115792089237316195423570985008687907853269984665640564039457584007913129639935"
            )
            .unwrap()
        );
    }

    #[test]
    fn large_numbers_no_overflow() {
        assert_eq!(
            muldiv(
                U256::from_dec_str("340282366920938463463374607431768211455").unwrap(),
                U256::from(1),
                U256::from(2),
                false
            )
            .unwrap(),
            U256::from_dec_str("170141183460469231731687303715884105727").unwrap()
        );
    }

    #[test]
    fn rounding_edge_case() {
        assert_eq!(
            muldiv(U256::from(5), U256::from(5), U256::from(2), true).unwrap(),
            U256::from(13)
        );
    }

    #[test]
    fn large_intermediate_result() {
        assert_eq!(
            muldiv(
                U256::from_dec_str("123456789012345678901234567890").unwrap(),
                U256::from_dec_str("98765432109876543210987654321").unwrap(),
                U256::from_dec_str("1219326311370217952261850327336229233322374638011112635269")
                    .unwrap(),
                false
            )
            .unwrap(),
            U256::from(10)
        );
    }

    #[test]
    fn small_denominator_large_numerator() {
        assert_eq!(
            muldiv(
                U256::from_dec_str("340282366920938463463374607431768211455").unwrap(),
                U256::from(2),
                U256::from(3),
                false
            )
            .unwrap(),
            U256::from_dec_str("226854911280625642308916404954512140970").unwrap()
        );
    }
}
