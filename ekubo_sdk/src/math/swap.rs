use crate::math::delta::AmountDeltaError;
use crate::math::sqrt_ratio::{next_sqrt_ratio_from_amount0, next_sqrt_ratio_from_amount1};
use crate::math::swap::ComputeStepError::WrongDirection;
use crate::math::uint::U256;
use num_traits::Zero;


pub struct SwapResult {
    pub consumed_amount: i128,
    pub calculated_amount: i128,
    pub sqrt_ratio_next: U256,
    pub fee_amount: u128,
}

pub fn is_price_increasing(amount: i128, is_token1: bool) -> bool {
    (amount < 0) != is_token1
}

const TWO_POW_128: U256 = U256([0, 0, 1, 0]);

pub fn amount_before_fee(after_fee: u128, fee: u128) -> Option<u128> {
    let (quotient, remainder) = (U256::from(after_fee) << 128).div_mod(
        TWO_POW_128 - U256::from(fee),
    );

    if !quotient.0[3].is_zero() || !quotient.0[2].is_zero() {
        None
    } else {
        if remainder.is_zero() {
            Some(quotient.low_u128())
        } else {
            quotient.low_u128().checked_add(1)
        }
    }
}
pub fn compute_fee(amount: u128, fee: u128) -> u128 {
    let num = U256::from(amount) * U256::from(fee);
    let (quotient, remainder) = num.div_mod(TWO_POW_128);
    if !remainder.is_zero() {
        quotient.low_u128() + 1
    } else {
        quotient.low_u128()
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

enum ComputeStepError {
    WrongDirection,
    AmountCheckedAbsOverflow,
    DeltaOverflow,
    AmountDeltaError(AmountDeltaError),
    AmountBeforeFeeOverflow,
    FeeOverflow,
    TODO,
}

fn compute_step(
    sqrt_ratio: U256,
    liquidity: u128,
    sqrt_ratio_limit: U256,
    amount: i128,
    is_token1: bool,
    fee: u128,
) -> Result<SwapResult, ComputeStepError> {
    if amount == 0 || sqrt_ratio == sqrt_ratio_limit {
        return Ok(no_op(sqrt_ratio));
    }

    let increasing = is_price_increasing(amount, is_token1);

    if (sqrt_ratio_limit < sqrt_ratio) == increasing {
        return Err(WrongDirection);
    }

    if liquidity.is_zero() {
        return Ok(no_op(sqrt_ratio_limit));
    }


    let price_impact_amount = if amount < 0 {
        amount
    } else {
        // compute_fee always returns a value less than amount so we can just unwrap
        let fee: i128 = compute_fee(amount.unsigned_abs(), fee).try_into().unwrap();
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
        if (sqrt_ratio_next > sqrt_ratio_limit) == increasing {
            // price did not move so we consume the entire amount
            if sqrt_ratio_next == sqrt_ratio {
                return Ok(SwapResult {
                    consumed_amount: amount,
                    calculated_amount: 0,
                    fee_amount: amount.unsigned_abs(),
                    sqrt_ratio_next: sqrt_ratio,
                });
            }

            return Err(ComputeStepError::TODO);

            // let calculated_amount_excluding_fee = if is_token1 {
            //     amount0_delta(
            //         sqrt_ratio_next,
            //         sqrt_ratio,
            //         liquidity,
            //         amount < 0,
            //     ).map_err(ComputeStepError::AmountDeltaError)?
            // } else {
            //     amount1_delta(
            //         sqrt_ratio_next,
            //         sqrt_ratio,
            //         liquidity,
            //         amount < 0,
            //     ).map_err(ComputeStepError::AmountDeltaError)?
            // };
            //
            // if amount < 0 {
            //     let including_fee = amount_before_fee(calculated_amount_excluding_fee, fee)
            //         .ok_or(ComputeStepError::AmountBeforeFeeOverflow)?;
            //     return Ok(SwapResult {
            //         consumed_amount: amount,
            //         calculated_amount: including_fee.try_into().map_err(|_| ComputeStepError::AmountBeforeFeeOverflow)?,
            //         sqrt_ratio_next,
            //         fee_amount: including_fee - calculated_amount_excluding_fee,
            //     });
            // } else {
            //     return Ok(SwapResult {
            //         consumed_amount: amount,
            //         calculated_amount: calculated_amount_excluding_fee.try_into().map_err(|_| ComputeStepError::AmountBeforeFeeOverflow)?,
            //         sqrt_ratio_next,
            //         fee_amount: amount - price_impact_amount.into(),
            //     });
            // }
        }
    }


    return Err(ComputeStepError::TODO);
    //
    // // this branch is only reached if we are not trading all the way up to the next sqrt ratio
    // let multiplier: i128 = if amount < 0 { -1 } else { 1 };
    //
    // let (specified_amount_delta, calculated_amount_delta): (i128, i128) = if is_token1 {
    //     (
    //         amount1_delta(
    //             sqrt_ratio_limit,
    //             sqrt_ratio,
    //             liquidity,
    //             amount >= 0,
    //         ).map_err(ComputeStepError::AmountDeltaError)?.try_into().map_err(|_| ComputeStepError::DeltaOverflow)? * multiplier,
    //         amount0_delta(
    //             sqrt_ratio_limit,
    //             sqrt_ratio,
    //             liquidity,
    //             amount < 0,
    //         ).map_err(ComputeStepError::AmountDeltaError)?.try_into().map_err(|_| ComputeStepError::DeltaOverflow)?,
    //     )
    // } else {
    //     (
    //         amount0_delta(
    //             sqrt_ratio_limit,
    //             sqrt_ratio,
    //             liquidity,
    //             amount >= 0,
    //         ).map_err(ComputeStepError::AmountDeltaError)?.try_into().map_err(|_| ComputeStepError::DeltaOverflow)? * multiplier,
    //         amount1_delta(
    //             sqrt_ratio_limit,
    //             sqrt_ratio,
    //             liquidity,
    //             amount < 0,
    //         ).map_err(ComputeStepError::AmountDeltaError)?.try_into().map_err(|_| ComputeStepError::DeltaOverflow)?,
    //     )
    // };
    //
    // if amount < 0 {
    //     let before_fee = amount_before_fee(calculated_amount_delta.unsigned_abs(), fee).ok_or(ComputeStepError::AmountBeforeFeeOverflow)?;
    //     Ok(SwapResult {
    //         consumed_amount: specified_amount_delta,
    //         calculated_amount: before_fee.try_into().map_err(|_| ComputeStepError::DeltaOverflow)?,
    //         fee_amount: before_fee - calculated_amount_delta.try_into().map_err(|_| ComputeStepError::AmountDeltaError(AmountDeltaError::Overflow))?,
    //         sqrt_ratio_next: sqrt_ratio_limit,
    //     })
    // } else {
    //     let before_fee = amount_before_fee(specified_amount_delta.unsigned_abs(), fee).ok_or(ComputeStepError::AmountBeforeFeeOverflow)?;
    //     Ok(SwapResult {
    //         consumed_amount: before_fee.try_into().map_err(|_| ComputeStepError::FeeOverflow)?,
    //         calculated_amount: calculated_amount_delta,
    //         fee_amount: before_fee - specified_amount_delta.try_into().map_err(|_| ComputeStepError::AmountDeltaError(AmountDeltaError::Overflow))?,
    //         sqrt_ratio_next: sqrt_ratio_limit,
    //     })
    // }
}