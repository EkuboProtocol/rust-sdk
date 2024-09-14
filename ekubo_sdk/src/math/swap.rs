use crate::math::delta::{amount0_delta, amount1_delta, AmountDeltaError};
use crate::math::sqrt_ratio::{next_sqrt_ratio_from_amount0, next_sqrt_ratio_from_amount1};
use crate::math::uint::U256;
use core::num::TryFromIntError;
use num_traits::Zero;

#[derive(Debug, PartialEq)]
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

#[derive(Debug, PartialEq)]
enum ComputeStepError {
    WrongDirection,
    AmountBeforeFeeOverflow,
    SignedIntegerOverflow(TryFromIntError),
    AmountDeltaError(AmountDeltaError),
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
                amount0_delta(
                    sqrt_ratio_next,
                    sqrt_ratio,
                    liquidity,
                    amount < 0,
                )
            } else {
                amount1_delta(
                    sqrt_ratio_next,
                    sqrt_ratio,
                    liquidity,
                    amount < 0,
                )
            }.map_err(ComputeStepError::AmountDeltaError)?;

            return if amount < 0 {
                let including_fee = amount_before_fee(calculated_amount_excluding_fee, fee)
                    .ok_or(ComputeStepError::AmountBeforeFeeOverflow)?;
                Ok(SwapResult {
                    consumed_amount: amount,
                    calculated_amount: including_fee.try_into().map_err(ComputeStepError::SignedIntegerOverflow)?,
                    sqrt_ratio_next,
                    fee_amount: including_fee - calculated_amount_excluding_fee,
                })
            } else {
                Ok(SwapResult {
                    consumed_amount: amount,
                    calculated_amount: calculated_amount_excluding_fee.try_into().map_err(ComputeStepError::SignedIntegerOverflow)?,
                    sqrt_ratio_next,
                    fee_amount: amount.unsigned_abs() - price_impact_amount.unsigned_abs(),
                })
            };
        }
    }

    // this branch is only reached if we are trading all the way up to the limit
    let (specified_amount_delta, calculated_amount_delta) = if is_token1 {
        (
            amount1_delta(
                sqrt_ratio_limit,
                sqrt_ratio,
                liquidity,
                amount > 0,
            ),
            amount0_delta(
                sqrt_ratio_limit,
                sqrt_ratio,
                liquidity,
                amount < 0,
            ),
        )
    } else {
        (
            amount0_delta(
                sqrt_ratio_limit,
                sqrt_ratio,
                liquidity,
                amount > 0,
            ),
            amount1_delta(
                sqrt_ratio_limit,
                sqrt_ratio,
                liquidity,
                amount < 0,
            ),
        )
    };

    if amount < 0 {
        let amount_after_fee = calculated_amount_delta.map_err(ComputeStepError::AmountDeltaError)?;
        let before_fee = amount_before_fee(amount_after_fee, fee)
            .ok_or(ComputeStepError::AmountBeforeFeeOverflow)?;
        Ok(SwapResult {
            consumed_amount: -specified_amount_delta.map_err(ComputeStepError::AmountDeltaError)?
                .try_into().map_err(ComputeStepError::SignedIntegerOverflow)?,
            calculated_amount: before_fee.try_into().map_err(ComputeStepError::SignedIntegerOverflow)?,
            fee_amount: before_fee - amount_after_fee,
            sqrt_ratio_next: sqrt_ratio_limit,
        })
    } else {
        let specified_amount = specified_amount_delta.map_err(ComputeStepError::AmountDeltaError)?;
        let before_fee = amount_before_fee(specified_amount, fee).ok_or(ComputeStepError::AmountBeforeFeeOverflow)?;
        let calculated_amount = calculated_amount_delta.map_err(ComputeStepError::AmountDeltaError)?;

        Ok(SwapResult {
            consumed_amount: before_fee.try_into().map_err(ComputeStepError::SignedIntegerOverflow)?,
            calculated_amount: calculated_amount.try_into().map_err(ComputeStepError::SignedIntegerOverflow)?,
            fee_amount: before_fee - specified_amount,
            sqrt_ratio_next: sqrt_ratio_limit,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::math::tick::{MAX_SQRT_RATIO, MIN_SQRT_RATIO};

    #[test]
    fn zero_amount_token0() {
        let sqrt_ratio = U256::from(1u128) << 128;
        let liquidity = 100_000u128;
        let sqrt_ratio_limit = U256::zero();
        let amount = 0i128;
        let is_token1 = false;
        let fee = 0u128;

        let result = compute_step(
            sqrt_ratio,
            liquidity,
            sqrt_ratio_limit,
            amount,
            is_token1,
            fee,
        )
            .unwrap();

        assert_eq!(result.calculated_amount, 0i128);
        assert_eq!(result.consumed_amount, 0i128);
        assert_eq!(result.fee_amount, 0u128);
        assert_eq!(result.sqrt_ratio_next, sqrt_ratio);
    }

    #[test]
    fn zero_amount_token1() {
        let sqrt_ratio = U256::from(1u128) << 128;
        let liquidity = 100_000u128;
        let sqrt_ratio_limit = U256::zero();
        let amount = 0i128;
        let is_token1 = true;
        let fee = 0u128;

        let result = compute_step(
            sqrt_ratio,
            liquidity,
            sqrt_ratio_limit,
            amount,
            is_token1,
            fee,
        )
            .unwrap();

        assert_eq!(result.calculated_amount, 0i128);
        assert_eq!(result.consumed_amount, 0i128);
        assert_eq!(result.fee_amount, 0u128);
        assert_eq!(result.sqrt_ratio_next, sqrt_ratio);
    }

    #[test]
    fn swap_ratio_equal_limit_token1() {
        let sqrt_ratio = U256::from(1u128) << 128;
        let liquidity = 100_000u128;
        let sqrt_ratio_limit = sqrt_ratio;
        let amount = 10_000i128;
        let is_token1 = true;
        let fee = 0u128;

        let result = compute_step(
            sqrt_ratio,
            liquidity,
            sqrt_ratio_limit,
            amount,
            is_token1,
            fee,
        )
            .unwrap();

        assert_eq!(result.calculated_amount, 0i128);
        assert_eq!(result.consumed_amount, 0i128);
        assert_eq!(result.fee_amount, 0u128);
        assert_eq!(result.sqrt_ratio_next, sqrt_ratio);
    }

    #[test]
    fn max_limit_token0_input() {
        let sqrt_ratio = U256::from(1u128) << 128;
        let liquidity = 100_000u128;
        let sqrt_ratio_limit = MIN_SQRT_RATIO;
        let amount = 10_000i128;
        let is_token1 = false;
        let fee = 1u128 << 127;

        let result = compute_step(
            sqrt_ratio,
            liquidity,
            sqrt_ratio_limit,
            amount,
            is_token1,
            fee,
        )
            .unwrap();

        assert_eq!(result.calculated_amount, 4_761i128);
        assert_eq!(result.consumed_amount, 10_000i128);
        assert_eq!(result.fee_amount, 5_000u128);
        assert_eq!(
            result.sqrt_ratio_next,
            U256::from_dec_str("324078444686608060441309149935017344244").unwrap()
        );
    }

    #[test]
    fn max_limit_token1_input() {
        let sqrt_ratio = U256::from(1u128) << 128;
        let liquidity = 100_000u128;
        let sqrt_ratio_limit = MAX_SQRT_RATIO;
        let amount = 10_000i128;
        let is_token1 = true;
        let fee = 1u128 << 127;

        let result = compute_step(
            sqrt_ratio,
            liquidity,
            sqrt_ratio_limit,
            amount,
            is_token1,
            fee,
        )
            .unwrap();

        assert_eq!(result.calculated_amount, 4_761i128);
        assert_eq!(result.consumed_amount, 10_000i128);
        assert_eq!(result.fee_amount, 5_000u128);
        assert_eq!(
            result.sqrt_ratio_next,
            U256::from_dec_str("357296485266985386636543337803356622028").unwrap()
        );
    }

    #[test]
    fn max_limit_token0_output() {
        let sqrt_ratio = U256::from(1u128) << 128;
        let liquidity = 100_000u128;
        let sqrt_ratio_limit = MAX_SQRT_RATIO;
        let amount = -10_000i128;
        let is_token1 = false;
        let fee = 1u128 << 127;

        let result = compute_step(
            sqrt_ratio,
            liquidity,
            sqrt_ratio_limit,
            amount,
            is_token1,
            fee,
        )
            .unwrap();

        assert_eq!(result.calculated_amount, 22_224i128);
        assert_eq!(result.consumed_amount, -10_000i128);
        assert_eq!(result.fee_amount, 11_112u128);
        assert_eq!(
            result.sqrt_ratio_next,
            U256::from_dec_str("378091518801042737181527341590853568285").unwrap()
        );
    }

    #[test]
    fn max_limit_token1_output() {
        let sqrt_ratio = U256::from(1u128) << 128;
        let liquidity = 100_000u128;
        let sqrt_ratio_limit = MIN_SQRT_RATIO;
        let amount = -10_000i128;
        let is_token1 = true;
        let fee = 1u128 << 127;

        let result = compute_step(
            sqrt_ratio,
            liquidity,
            sqrt_ratio_limit,
            amount,
            is_token1,
            fee,
        )
            .unwrap();

        assert_eq!(result.calculated_amount, 22_224i128);
        assert_eq!(result.consumed_amount, -10_000i128);
        assert_eq!(result.fee_amount, 11_112u128);
        assert_eq!(
            result.sqrt_ratio_next,
            U256::from_dec_str("306254130228844617117037146688591390310").unwrap()
        );
    }

    #[test]
    fn limited_token0_output() {
        let sqrt_ratio = U256::from(1u128) << 128;
        let liquidity = 100_000u128;
        let sqrt_ratio_limit =
            U256::from_dec_str("359186942860990600322450974511310889870").unwrap();
        let amount = -10_000i128;
        let is_token1 = false;
        let fee = 1u128 << 127;

        let result = compute_step(
            sqrt_ratio,
            liquidity,
            sqrt_ratio_limit,
            amount,
            is_token1,
            fee,
        )
            .unwrap();

        assert_eq!(result.calculated_amount, 11_112i128);
        assert_eq!(result.consumed_amount, -5_263i128);
        assert_eq!(result.fee_amount, 5_556u128);
        assert_eq!(result.sqrt_ratio_next, sqrt_ratio_limit);
    }

    #[test]
    fn limited_token1_output() {
        let sqrt_ratio = U256::from(1u128) << 128;
        let liquidity = 100_000u128;
        let sqrt_ratio_limit =
            U256::from_dec_str("323268248574891540290205877060179800883").unwrap();
        let amount = -10_000i128;
        let is_token1 = true;
        let fee = 1u128 << 127;

        let result = compute_step(
            sqrt_ratio,
            liquidity,
            sqrt_ratio_limit,
            amount,
            is_token1,
            fee,
        )
            .unwrap();

        assert_eq!(result.calculated_amount, 10_528i128);
        assert_eq!(result.consumed_amount, -5_000i128);
        assert_eq!(result.fee_amount, 5_264u128);
        assert_eq!(result.sqrt_ratio_next, sqrt_ratio_limit);
    }
}
