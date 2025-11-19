use core::ops::Not;

use crate::math::uint::U256;
use crate::math::{
    muldiv::{muldiv, MuldivError},
    sqrt_ratio::SQRT_RATIO_ONE,
};
use num_traits::Zero;

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
        SQRT_RATIO_ONE,
        round_up,
    )
    .map_err(AmountDeltaError::MuldivError)?;

    if result > u128::MAX.into() {
        Err(AmountDeltaError::Overflow)
    } else {
        Ok(result.low_u128())
    }
}

fn sort_ratios(sqrt_ratio_a: U256, sqrt_ratio_b: U256) -> Option<(U256, U256)> {
    let (lower, higher) = if sqrt_ratio_a < sqrt_ratio_b {
        (sqrt_ratio_a, sqrt_ratio_b)
    } else {
        (sqrt_ratio_b, sqrt_ratio_a)
    };

    lower.is_zero().not().then_some((lower, higher))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::chain::{
        tests::{ChainEnum, CHAINS},
        Evm, Starknet,
    };
    use crate::math::uint::U256;

    const SMALL_LIQUIDITY: u128 = 1_000_000;
    const LARGE_LIQUIDITY: u128 = 1_000_000_000_000_000_000;

    fn sqrt_ratio_one() -> U256 {
        U256::from_str_radix("100000000000000000000000000000000", 16).unwrap()
    }

    fn sqrt_ratio_close_to_one() -> U256 {
        U256::from_dec_str("339942424496442021441932674757011200255").unwrap()
    }

    mod amount0_delta {
        use super::*;

        fn sqrt_ratio_far_from_one() -> U256 {
            let point_one = U256::from_dec_str("34028236692093846346337460743176821145").unwrap();
            sqrt_ratio_one() + point_one
        }

        #[test]
        fn small_delta() {
            assert_eq!(
                amount0_delta(
                    sqrt_ratio_one(),
                    sqrt_ratio_close_to_one(),
                    SMALL_LIQUIDITY,
                    false,
                )
                .unwrap(),
                1_000
            );
        }

        #[test]
        fn large_delta() {
            assert_eq!(
                amount0_delta(
                    sqrt_ratio_one(),
                    sqrt_ratio_far_from_one(),
                    LARGE_LIQUIDITY,
                    false
                )
                .unwrap(),
                90_909_090_909_090_909
            );
        }

        #[test]
        fn no_overflow_half_price_range() {
            for chain in CHAINS {
                let (expected, min_sqrt_ratio) = match chain {
                    ChainEnum::Evm => (
                        "340274119756928397712370531121900180028",
                        Evm::MIN_SQRT_RATIO,
                    ),
                    ChainEnum::Starknet => (
                        "340282286429718909724583623827301092853",
                        Starknet::MIN_SQRT_RATIO,
                    ),
                };

                assert_eq!(
                    amount0_delta(sqrt_ratio_one(), min_sqrt_ratio, u64::MAX.into(), false)
                        .unwrap(),
                    U256::from_dec_str(expected).unwrap().as_u128()
                );
            }
        }

        #[test]
        fn overflow() {
            for chain in CHAINS {
                let (min_sqrt_ratio, max_sqrt_ratio) = match chain {
                    ChainEnum::Evm => (Evm::MIN_SQRT_RATIO, Evm::MAX_SQRT_RATIO),
                    ChainEnum::Starknet => (Starknet::MIN_SQRT_RATIO, Starknet::MAX_SQRT_RATIO),
                };

                assert_eq!(
                    amount0_delta(min_sqrt_ratio, max_sqrt_ratio, u128::MAX, false).unwrap_err(),
                    AmountDeltaError::Overflow
                );
            }
        }
    }

    mod amount1_delta {
        use super::*;

        fn sqrt_ratio_far_from_one() -> U256 {
            U256::from_dec_str("309347606291762239512158734028880192232").unwrap()
        }

        #[test]
        fn small_delta() {
            assert_eq!(
                amount1_delta(
                    sqrt_ratio_one(),
                    sqrt_ratio_close_to_one(),
                    SMALL_LIQUIDITY,
                    false,
                )
                .unwrap(),
                999
            );
        }

        #[test]
        fn large_delta() {
            assert_eq!(
                amount1_delta(
                    sqrt_ratio_one(),
                    sqrt_ratio_far_from_one(),
                    LARGE_LIQUIDITY,
                    false
                )
                .unwrap(),
                90_909_090_909_090_909
            );
        }

        #[test]
        fn no_overflow_half_price_range() {
            for chain in CHAINS {
                let (expected, max_sqrt_ratio) = match chain {
                    ChainEnum::Evm => (
                        "340274119756928397675478831269759003622",
                        Evm::MAX_SQRT_RATIO,
                    ),
                    ChainEnum::Starknet => (
                        "340282286429718909724583623827301092853",
                        Starknet::MAX_SQRT_RATIO,
                    ),
                };

                assert_eq!(
                    amount1_delta(sqrt_ratio_one(), max_sqrt_ratio, u64::MAX.into(), false)
                        .unwrap(),
                    U256::from_dec_str(expected).unwrap().as_u128()
                );
            }
        }

        #[test]
        fn overflow() {
            for chain in CHAINS {
                let (min_sqrt_ratio, max_sqrt_ratio) = match chain {
                    ChainEnum::Evm => (Evm::MIN_SQRT_RATIO, Evm::MAX_SQRT_RATIO),
                    ChainEnum::Starknet => (Starknet::MIN_SQRT_RATIO, Starknet::MAX_SQRT_RATIO),
                };

                assert_eq!(
                    amount1_delta(min_sqrt_ratio, max_sqrt_ratio, u128::MAX, false).unwrap_err(),
                    AmountDeltaError::Overflow
                );
            }
        }
    }
}
