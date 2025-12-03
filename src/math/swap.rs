use crate::math::sqrt_ratio::{next_sqrt_ratio_from_amount0, next_sqrt_ratio_from_amount1};
use crate::{
    chain::Chain,
    math::delta::{amount0_delta, amount1_delta, AmountDeltaError},
};
use num_traits::Zero;
use ruint::aliases::U256;
use thiserror::Error;

#[derive(Debug, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct SwapResult {
    pub consumed_amount: i128,
    pub calculated_amount: u128,
    pub sqrt_ratio_next: U256,
    pub fee_amount: u128,
}

#[must_use]
pub fn is_price_increasing(amount: i128, is_token1: bool) -> bool {
    (amount < 0) != is_token1
}

pub fn amount_before_fee<C: Chain>(after_fee: u128, fee: C::Fee) -> Option<u128> {
    let denominator = C::fee_denominator() - U256::from(fee.into());
    let (quotient, remainder) = (U256::from(after_fee) << C::fee_bits()).div_rem(denominator);

    let unrounded = u128::try_from(quotient).ok()?;
    if remainder.is_zero() {
        Some(unrounded)
    } else {
        unrounded.checked_add(1)
    }
}

pub fn compute_fee<C: Chain>(amount: u128, fee: C::Fee) -> u128 {
    let num = U256::from(amount) * U256::from(fee.into());
    let (quotient, remainder) = num.div_rem(C::fee_denominator());

    let unrounded = u128::try_from(quotient).expect("fee quotient should not exceed u128");
    if remainder.is_zero() {
        unrounded
    } else {
        unrounded + 1
    }
}

fn no_op(sqrt_ratio_next: U256) -> SwapResult {
    SwapResult {
        consumed_amount: 0,
        calculated_amount: 0,
        sqrt_ratio_next,
        fee_amount: 0,
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Error, Hash)]
pub enum ComputeStepError {
    #[error("wrong direction")]
    WrongDirection,
    #[error("amount before fee overflow")]
    AmountBeforeFeeOverflow,
    #[error("signed integer overflow")]
    SignedIntegerOverflow,
    #[error("amount delta error")]
    AmountDelta(#[from] AmountDeltaError),
}

pub fn compute_step<C: Chain>(
    sqrt_ratio: U256,
    liquidity: u128,
    sqrt_ratio_limit: U256,
    amount: i128,
    is_token1: bool,
    fee: C::Fee,
) -> Result<SwapResult, ComputeStepError> {
    if amount.is_zero() || sqrt_ratio == sqrt_ratio_limit {
        return Ok(no_op(sqrt_ratio));
    }

    let increasing = is_price_increasing(amount, is_token1);

    if (sqrt_ratio_limit < sqrt_ratio) == increasing {
        return Err(ComputeStepError::WrongDirection);
    }

    if liquidity.is_zero() {
        return Ok(no_op(sqrt_ratio_limit));
    }

    let price_impact_amount = if amount < 0 {
        amount
    } else {
        // compute_fee always returns a value less than amount so we can just unwrap
        let fee: i128 = compute_fee::<C>(amount.unsigned_abs(), fee)
            .try_into()
            .unwrap();
        amount - fee
    };

    let sqrt_ratio_next_from_amount = if is_token1 {
        next_sqrt_ratio_from_amount1(sqrt_ratio, liquidity, price_impact_amount)
    } else {
        next_sqrt_ratio_from_amount0(sqrt_ratio, liquidity, price_impact_amount)
    };

    // we got a next price
    if let Ok(sqrt_ratio_next) = sqrt_ratio_next_from_amount {
        // and it's not in excess of the limit
        if (sqrt_ratio_next <= sqrt_ratio_limit) == increasing {
            // price did not move so we consume the entire amount
            if sqrt_ratio_next == sqrt_ratio {
                return Ok(SwapResult {
                    consumed_amount: amount,
                    calculated_amount: 0,
                    fee_amount: amount.unsigned_abs(),
                    sqrt_ratio_next: sqrt_ratio,
                });
            }

            let calculated_amount_excluding_fee = if is_token1 {
                amount0_delta(sqrt_ratio_next, sqrt_ratio, liquidity, amount < 0)
            } else {
                amount1_delta(sqrt_ratio_next, sqrt_ratio, liquidity, amount < 0)
            }
            .map_err(ComputeStepError::AmountDelta)?;

            return if amount < 0 {
                let including_fee = amount_before_fee::<C>(calculated_amount_excluding_fee, fee)
                    .ok_or(ComputeStepError::AmountBeforeFeeOverflow)?;
                Ok(SwapResult {
                    consumed_amount: amount,
                    calculated_amount: including_fee,
                    sqrt_ratio_next,
                    fee_amount: including_fee - calculated_amount_excluding_fee,
                })
            } else {
                Ok(SwapResult {
                    consumed_amount: amount,
                    calculated_amount: calculated_amount_excluding_fee,
                    sqrt_ratio_next,
                    fee_amount: amount.unsigned_abs() - price_impact_amount.unsigned_abs(),
                })
            };
        }
    }

    // this branch is only reached if we are trading all the way up to the limit
    let (specified_amount_delta, calculated_amount_delta) = if is_token1 {
        (
            amount1_delta(sqrt_ratio_limit, sqrt_ratio, liquidity, amount > 0),
            amount0_delta(sqrt_ratio_limit, sqrt_ratio, liquidity, amount < 0),
        )
    } else {
        (
            amount0_delta(sqrt_ratio_limit, sqrt_ratio, liquidity, amount > 0),
            amount1_delta(sqrt_ratio_limit, sqrt_ratio, liquidity, amount < 0),
        )
    };

    if amount < 0 {
        let amount_after_fee = calculated_amount_delta.map_err(ComputeStepError::AmountDelta)?;
        let before_fee = amount_before_fee::<C>(amount_after_fee, fee)
            .ok_or(ComputeStepError::AmountBeforeFeeOverflow)?;
        Ok(SwapResult {
            consumed_amount: -specified_amount_delta
                .map_err(ComputeStepError::AmountDelta)?
                .try_into()
                .map_err(|_| ComputeStepError::SignedIntegerOverflow)?,
            calculated_amount: before_fee,
            fee_amount: before_fee - amount_after_fee,
            sqrt_ratio_next: sqrt_ratio_limit,
        })
    } else {
        let specified_amount = specified_amount_delta.map_err(ComputeStepError::AmountDelta)?;
        let before_fee = amount_before_fee::<C>(specified_amount, fee)
            .ok_or(ComputeStepError::AmountBeforeFeeOverflow)?;

        Ok(SwapResult {
            consumed_amount: before_fee
                .try_into()
                .map_err(|_| ComputeStepError::SignedIntegerOverflow)?,
            calculated_amount: calculated_amount_delta.map_err(ComputeStepError::AmountDelta)?,
            fee_amount: before_fee - specified_amount,
            sqrt_ratio_next: sqrt_ratio_limit,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        chain::{
            evm::Evm,
            starknet::Starknet,
            tests::{ChainEnum, CHAINS},
        },
        math::sqrt_ratio::SQRT_RATIO_ONE,
    };
    use ruint::uint;

    const DEFAULT_LIQUIDITY: u128 = 100_000;
    const ZERO_AMOUNT: i128 = 0;
    const POSITIVE_AMOUNT: i128 = 10_000;
    const NEGATIVE_AMOUNT: i128 = -10_000;
    const HALF_FEE_STARKNET: u128 = 1u128 << 127;
    const HALF_FEE_EVM: u64 = 1u64 << 63;

    #[derive(Clone, Copy)]
    struct StepParams<C: Chain> {
        sqrt_ratio: U256,
        liquidity: u128,
        sqrt_ratio_limit: U256,
        amount: i128,
        is_token1: bool,
        fee: C::Fee,
    }

    fn step_params<C: Chain>(
        sqrt_ratio_limit: U256,
        amount: i128,
        is_token1: bool,
        fee: C::Fee,
    ) -> StepParams<C> {
        StepParams {
            sqrt_ratio: SQRT_RATIO_ONE,
            liquidity: DEFAULT_LIQUIDITY,
            sqrt_ratio_limit,
            amount,
            is_token1,
            fee,
        }
    }

    fn compute_step<C: Chain>(params: StepParams<C>) -> SwapResult {
        super::compute_step::<C>(
            params.sqrt_ratio,
            params.liquidity,
            params.sqrt_ratio_limit,
            params.amount,
            params.is_token1,
            params.fee,
        )
        .unwrap()
    }

    #[test]
    fn zero_amount_token0() {
        for chain in CHAINS {
            let res = match chain {
                ChainEnum::Starknet => {
                    compute_step::<Starknet>(step_params(U256::ZERO, ZERO_AMOUNT, false, 0))
                }
                ChainEnum::Evm => {
                    compute_step::<Evm>(step_params(U256::ZERO, ZERO_AMOUNT, false, 0))
                }
            };

            assert_eq!(
                res,
                SwapResult {
                    consumed_amount: 0,
                    calculated_amount: 0,
                    fee_amount: 0,
                    sqrt_ratio_next: SQRT_RATIO_ONE
                }
            )
        }
    }

    #[test]
    fn zero_amount_token1() {
        for chain in CHAINS {
            let res = match chain {
                ChainEnum::Starknet => {
                    compute_step::<Starknet>(step_params(U256::ZERO, ZERO_AMOUNT, true, 0))
                }
                ChainEnum::Evm => {
                    compute_step::<Evm>(step_params(U256::ZERO, ZERO_AMOUNT, true, 0))
                }
            };

            assert_eq!(
                res,
                SwapResult {
                    consumed_amount: 0,
                    calculated_amount: 0,
                    fee_amount: 0,
                    sqrt_ratio_next: SQRT_RATIO_ONE,
                }
            );
        }
    }

    #[test]
    fn swap_ratio_equal_limit_token1() {
        for chain in CHAINS {
            let res = match chain {
                ChainEnum::Starknet => {
                    compute_step::<Starknet>(step_params(SQRT_RATIO_ONE, POSITIVE_AMOUNT, true, 0))
                }
                ChainEnum::Evm => {
                    compute_step::<Evm>(step_params(SQRT_RATIO_ONE, POSITIVE_AMOUNT, true, 0))
                }
            };

            assert_eq!(
                res,
                SwapResult {
                    consumed_amount: 0,
                    calculated_amount: 0,
                    fee_amount: 0,
                    sqrt_ratio_next: SQRT_RATIO_ONE,
                }
            );
        }
    }

    #[test]
    fn max_limit_token0_input() {
        for chain in CHAINS {
            let res = match chain {
                ChainEnum::Starknet => compute_step::<Starknet>(step_params(
                    Starknet::min_sqrt_ratio(),
                    POSITIVE_AMOUNT,
                    false,
                    HALF_FEE_STARKNET,
                )),
                ChainEnum::Evm => compute_step::<Evm>(step_params(
                    Evm::min_sqrt_ratio(),
                    POSITIVE_AMOUNT,
                    false,
                    HALF_FEE_EVM,
                )),
            };

            assert_eq!(
                res,
                SwapResult {
                    consumed_amount: POSITIVE_AMOUNT,
                    calculated_amount: 4_761,
                    sqrt_ratio_next: U256::from_str_radix(
                        "324078444686608060441309149935017344244",
                        10
                    )
                    .unwrap(),
                    fee_amount: 5_000,
                }
            );
        }
    }

    #[test]
    fn max_limit_token1_input() {
        for chain in CHAINS {
            let res = match chain {
                ChainEnum::Starknet => compute_step::<Starknet>(step_params(
                    Starknet::max_sqrt_ratio(),
                    POSITIVE_AMOUNT,
                    true,
                    HALF_FEE_STARKNET,
                )),
                ChainEnum::Evm => compute_step::<Evm>(step_params(
                    Evm::max_sqrt_ratio(),
                    POSITIVE_AMOUNT,
                    true,
                    HALF_FEE_EVM,
                )),
            };

            assert_eq!(
                res,
                SwapResult {
                    consumed_amount: POSITIVE_AMOUNT,
                    calculated_amount: 4_761,
                    sqrt_ratio_next: U256::from_str_radix(
                        "357296485266985386636543337803356622028",
                        10
                    )
                    .unwrap(),
                    fee_amount: 5_000,
                }
            );
        }
    }

    #[test]
    fn max_limit_token0_output() {
        for chain in CHAINS {
            let res = match chain {
                ChainEnum::Starknet => compute_step::<Starknet>(step_params(
                    Starknet::max_sqrt_ratio(),
                    NEGATIVE_AMOUNT,
                    false,
                    HALF_FEE_STARKNET,
                )),
                ChainEnum::Evm => compute_step::<Evm>(step_params(
                    Evm::max_sqrt_ratio(),
                    NEGATIVE_AMOUNT,
                    false,
                    HALF_FEE_EVM,
                )),
            };

            assert_eq!(
                res,
                SwapResult {
                    consumed_amount: NEGATIVE_AMOUNT,
                    calculated_amount: 22_224,
                    sqrt_ratio_next: U256::from_str_radix(
                        "378091518801042737181527341590853568285",
                        10
                    )
                    .unwrap(),
                    fee_amount: 11_112,
                }
            );
        }
    }

    #[test]
    fn max_limit_token1_output() {
        for chain in CHAINS {
            let res = match chain {
                ChainEnum::Starknet => compute_step::<Starknet>(step_params(
                    Starknet::min_sqrt_ratio(),
                    NEGATIVE_AMOUNT,
                    true,
                    HALF_FEE_STARKNET,
                )),
                ChainEnum::Evm => compute_step::<Evm>(step_params(
                    Evm::min_sqrt_ratio(),
                    NEGATIVE_AMOUNT,
                    true,
                    HALF_FEE_EVM,
                )),
            };

            assert_eq!(
                res,
                SwapResult {
                    consumed_amount: NEGATIVE_AMOUNT,
                    calculated_amount: 22_224,
                    sqrt_ratio_next: U256::from_str_radix(
                        "306254130228844617117037146688591390310",
                        10
                    )
                    .unwrap(),
                    fee_amount: 11_112,
                }
            );
        }
    }

    #[test]
    fn limited_token0_output() {
        let limit = uint!(359186942860990600322450974511310889870_U256);

        for chain in CHAINS {
            let res = match chain {
                ChainEnum::Starknet => compute_step::<Starknet>(step_params(
                    limit.clone(),
                    NEGATIVE_AMOUNT,
                    false,
                    HALF_FEE_STARKNET,
                )),
                ChainEnum::Evm => compute_step::<Evm>(step_params(
                    limit.clone(),
                    NEGATIVE_AMOUNT,
                    false,
                    HALF_FEE_EVM,
                )),
            };

            assert_eq!(
                res,
                SwapResult {
                    consumed_amount: -5_263,
                    calculated_amount: 11_112,
                    sqrt_ratio_next: limit.clone(),
                    fee_amount: 5_556,
                }
            );
        }
    }

    #[test]
    fn limited_token1_output() {
        let limit = uint!(323268248574891540290205877060179800883_U256);

        for chain in CHAINS {
            let res = match chain {
                ChainEnum::Starknet => compute_step::<Starknet>(step_params(
                    limit.clone(),
                    NEGATIVE_AMOUNT,
                    true,
                    HALF_FEE_STARKNET,
                )),
                ChainEnum::Evm => compute_step::<Evm>(step_params(
                    limit.clone(),
                    NEGATIVE_AMOUNT,
                    true,
                    HALF_FEE_EVM,
                )),
            };

            assert_eq!(
                res,
                SwapResult {
                    consumed_amount: -5_000,
                    calculated_amount: 10_528,
                    sqrt_ratio_next: limit.clone(),
                    fee_amount: 5_264,
                }
            );
        }
    }
}
