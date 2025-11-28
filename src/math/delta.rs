use core::ops::Not;

use crate::math::{
    muldiv::{muldiv, MuldivError},
    sqrt_ratio::SQRT_RATIO_ONE,
};
use num_traits::Zero;
use ruint::aliases::U256;
use thiserror::Error;

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, Error)]
pub enum AmountDeltaError {
    #[error("ratio is zero")]
    ZeroRatio,
    #[error("overflow")]
    Overflow,
    #[error("muldiv error")]
    MuldivError(#[from] MuldivError),
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

    let (result, remainder) = result_0.div_rem(lower);
    let rounded = if round_up && !remainder.is_zero() {
        result
            .checked_add(U256::ONE)
            .ok_or(AmountDeltaError::Overflow)?
    } else {
        result
    };

    rounded.try_into().map_err(|_| AmountDeltaError::Overflow)
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

    result.try_into().map_err(|_| AmountDeltaError::Overflow)
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
        evm::Evm,
        starknet::Starknet,
        tests::{ChainEnum, CHAINS},
        Chain,
    };
    use ruint::uint;

    const SMALL_LIQUIDITY: u128 = 1_000_000;
    const LARGE_LIQUIDITY: u128 = 1_000_000_000_000_000_000;

    fn sqrt_ratio_close_to_one() -> U256 {
        uint!(339942424496442021441932674757011200255_U256)
    }

    mod amount0_delta {
        use super::*;

        fn sqrt_ratio_far_from_one() -> U256 {
            let point_one = uint!(34028236692093846346337460743176821145_U256);
            SQRT_RATIO_ONE + point_one
        }

        #[test]
        fn small_delta() {
            assert_eq!(
                amount0_delta(
                    SQRT_RATIO_ONE,
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
                    SQRT_RATIO_ONE,
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
                        340_274_119_756_928_397_712_370_531_121_900_180_028,
                        Evm::min_sqrt_ratio(),
                    ),
                    ChainEnum::Starknet => (
                        340_282_286_429_718_909_724_583_623_827_301_092_853,
                        Starknet::min_sqrt_ratio(),
                    ),
                };

                assert_eq!(
                    amount0_delta(SQRT_RATIO_ONE, min_sqrt_ratio, u64::MAX.into(), false).unwrap(),
                    expected
                );
            }
        }

        #[test]
        fn overflow() {
            for chain in CHAINS {
                let (min_sqrt_ratio, max_sqrt_ratio) = match chain {
                    ChainEnum::Evm => (Evm::min_sqrt_ratio(), Evm::max_sqrt_ratio()),
                    ChainEnum::Starknet => (Starknet::min_sqrt_ratio(), Starknet::max_sqrt_ratio()),
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
            uint!(309347606291762239512158734028880192232_U256)
        }

        #[test]
        fn small_delta() {
            assert_eq!(
                amount1_delta(
                    SQRT_RATIO_ONE,
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
                    SQRT_RATIO_ONE,
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
                        340_274_119_756_928_397_675_478_831_269_759_003_622,
                        Evm::max_sqrt_ratio(),
                    ),
                    ChainEnum::Starknet => (
                        340_282_286_429_718_909_724_583_623_827_301_092_853,
                        Starknet::max_sqrt_ratio(),
                    ),
                };

                assert_eq!(
                    amount1_delta(SQRT_RATIO_ONE, max_sqrt_ratio, u64::MAX.into(), false).unwrap(),
                    expected
                );
            }
        }

        #[test]
        fn overflow() {
            for chain in CHAINS {
                let (min_sqrt_ratio, max_sqrt_ratio) = match chain {
                    ChainEnum::Evm => (Evm::min_sqrt_ratio(), Evm::max_sqrt_ratio()),
                    ChainEnum::Starknet => (Starknet::min_sqrt_ratio(), Starknet::max_sqrt_ratio()),
                };

                assert_eq!(
                    amount1_delta(min_sqrt_ratio, max_sqrt_ratio, u128::MAX, false).unwrap_err(),
                    AmountDeltaError::Overflow
                );
            }
        }
    }
}
