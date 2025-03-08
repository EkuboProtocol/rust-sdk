use crate::math::muldiv::muldiv;
use crate::math::twamm::exp2::exp2;
use crate::math::uint::U256;
use num_traits::Zero;

const EXPONENT_LIMIT: U256 = U256([0, 64, 0, 0]);
const TWO_POW_64: U256 = U256([0, 1, 0, 0]);

pub fn calculate_next_sqrt_ratio(
    sqrt_ratio: U256,
    liquidity: u128,
    token0_sale_rate: u128,
    token1_sale_rate: u128,
    time_elapsed: u32,
    fee: u64,
) -> Option<U256> {
    let sqrt_sale_ratio =
        ((U256::from(token1_sale_rate) << 128) / token0_sale_rate).integer_sqrt() << 64;

    if liquidity.is_zero() {
        return Some(sqrt_sale_ratio);
    }

    let sale_rate = ((U256::from(token1_sale_rate) * U256::from(token0_sale_rate)).integer_sqrt()
        * (TWO_POW_64 - fee))
        / TWO_POW_64;

    let round_up = sqrt_ratio > sqrt_sale_ratio;

    let exponent = muldiv(
        // 12392656037 = Math.floor(Math.LOG2E * 2**33).
        // this combines the doubling, the left shifting and the converting to a base 2 exponent into a single multiplication
        sale_rate * U256::from(12392656037i64),
        U256::from(time_elapsed),
        U256::from(liquidity),
        round_up,
    )
    .ok()?
    .low_u128();

    if exponent >= 0x400000000000000000 {
        return Some(sqrt_sale_ratio);
    }

    let e = U256::from(exp2(exponent.try_into().ok()?)) << 64;

    let (num, sign) = if round_up {
        (sqrt_ratio - sqrt_sale_ratio, true)
    } else {
        (sqrt_sale_ratio - sqrt_ratio, false)
    };

    let c = muldiv(
        num,
        TWO_POW_64 * TWO_POW_64,
        sqrt_sale_ratio + sqrt_ratio,
        round_up,
    )
    .ok()?;

    let (term1, term2) = (e - c, e + c);

    let scale = if sign {
        muldiv(term2, TWO_POW_64 * TWO_POW_64, term1, round_up)
    } else {
        muldiv(term1, TWO_POW_64 * TWO_POW_64, term2, round_up)
    }
    .ok()?;

    muldiv(sqrt_sale_ratio, scale, TWO_POW_64 * TWO_POW_64, false).ok()
}

#[cfg(test)]
mod tests {
    use crate::math::twamm::sqrt_ratio::calculate_next_sqrt_ratio;
    use crate::math::uint::U256;
    use alloc::vec;
    use insta::{assert_debug_snapshot, assert_snapshot};

    const ONE_E18: u128 = 1_000_000_000_000_000_000; // 10^18
    const SHIFT_32: u128 = 1u128 << 32; // 2^32 = 4294967296
    const TOKEN_SALE_RATE: u128 = ONE_E18 * SHIFT_32; // 10^18 * 2^32

    struct TestCase {
        description: &'static str,
        sqrt_ratio: U256,
        liquidity: u128,
        token0_sale_rate: u128,
        token1_sale_rate: u128,
        time_elapsed: u32,
        fee: u64,
    }

    #[test]
    fn test_calculate_next_sqrt_ratio() {
        let test_cases = vec![
            TestCase {
                description: "zero_liquidity_price_eq_sale_ratio",
                sqrt_ratio: U256::zero(),
                liquidity: 0,
                token0_sale_rate: TOKEN_SALE_RATE,
                token1_sale_rate: TOKEN_SALE_RATE,
                time_elapsed: 0,
                fee: 0,
            },
            TestCase {
                description: "large_exponent_price_sqrt_ratio",
                sqrt_ratio: U256::one() << 128,
                liquidity: 1,
                token0_sale_rate: TOKEN_SALE_RATE,
                token1_sale_rate: 1980 * ONE_E18 * SHIFT_32,
                time_elapsed: 1,
                fee: 0,
            },
            TestCase {
                description: "low_liquiidty_same_sale_ratio",
                sqrt_ratio: U256::from(2u128) << 128,
                liquidity: 1,
                token0_sale_rate: TOKEN_SALE_RATE,
                token1_sale_rate: TOKEN_SALE_RATE,
                time_elapsed: 1,
                fee: 0,
            },
            TestCase {
                description: "low_liquidity_token0_gt_token1",
                sqrt_ratio: U256::one() << 128,
                liquidity: 1,
                token0_sale_rate: 2 * TOKEN_SALE_RATE,
                token1_sale_rate: TOKEN_SALE_RATE,
                time_elapsed: 16,
                fee: 0,
            },
            TestCase {
                description: "low_liquidity_token1_gt_token0",
                sqrt_ratio: U256::one() << 128,
                liquidity: 1,
                token0_sale_rate: TOKEN_SALE_RATE,
                token1_sale_rate: 2 * TOKEN_SALE_RATE,
                time_elapsed: 16,
                fee: 0,
            },
            TestCase {
                description: "high_liquidity_same_sale_rate",
                sqrt_ratio: U256::from(2u128) << 128,
                liquidity: 1_000_000 * ONE_E18,
                token0_sale_rate: TOKEN_SALE_RATE,
                token1_sale_rate: TOKEN_SALE_RATE,
                time_elapsed: 1,
                fee: 0,
            },
            TestCase {
                description: "high_liquidity_token0_gt_token1",
                sqrt_ratio: U256::one() << 128,
                liquidity: 1_000_000 * ONE_E18,
                token0_sale_rate: 2 * TOKEN_SALE_RATE,
                token1_sale_rate: TOKEN_SALE_RATE,
                time_elapsed: 1,
                fee: 0,
            },
            TestCase {
                description: "high_liquidity_token1_gt_token0",
                sqrt_ratio: U256::one() << 128,
                liquidity: 1_000_000 * ONE_E18,
                token0_sale_rate: TOKEN_SALE_RATE,
                token1_sale_rate: 2 * TOKEN_SALE_RATE,
                time_elapsed: 1,
                fee: 0,
            },
            TestCase {
                description: "round_in_direction_of_price",
                sqrt_ratio: U256::from_dec_str("481231811499356508086519009265716982182").unwrap(),
                liquidity: 70_710_696_755_630_728_101_718_334,
                token0_sale_rate: 10_526_880_627_450_980_392_156_862_745,
                token1_sale_rate: 10_526_880_627_450_980_392_156_862_745,
                time_elapsed: 2040,
                fee: 0,
            },
        ];

        for test_case in test_cases {
            assert_debug_snapshot!(
                test_case.description,
                calculate_next_sqrt_ratio(
                    test_case.sqrt_ratio,
                    test_case.liquidity,
                    test_case.token0_sale_rate,
                    test_case.token1_sale_rate,
                    test_case.time_elapsed,
                    test_case.fee,
                )
            );
        }
    }
}
