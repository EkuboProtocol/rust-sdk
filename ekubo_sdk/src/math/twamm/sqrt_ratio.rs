use crate::math::muldiv::muldiv;
use crate::math::twamm::exp::exp;
use crate::math::uint::U256;
use num_traits::Zero;

const EXPONENT_LIMIT: U256 = U256([0, 88, 0, 0]);
const TWO_POW_128: U256 = U256([0, 0, 1, 0]);

pub fn calculate_next_sqrt_ratio(
    sqrt_ratio: U256,
    liquidity: u128,
    token0_sale_rate: u128,
    token1_sale_rate: u128,
    time_elapsed: u32,
    fee: u128,
) -> Option<U256> {
    let sqrt_sale_ratio =
        ((U256::from(token1_sale_rate) << 128) / token0_sale_rate).integer_sqrt() << 64;

    if liquidity.is_zero() {
        return Some(sqrt_sale_ratio);
    }

    let sale_rate = ((U256::from(token1_sale_rate) * U256::from(token0_sale_rate)).integer_sqrt()
        * (TWO_POW_128 - fee))
        / TWO_POW_128;

    let round_up = sqrt_ratio > sqrt_sale_ratio;

    let exponent = muldiv(
        sale_rate * U256::from(0x200000000u128),
        U256::from(time_elapsed),
        U256::from(liquidity),
        round_up,
    )
        .ok()?;

    if exponent > EXPONENT_LIMIT {
        return Some(sqrt_sale_ratio);
    }

    let e = exp(exponent.low_u128())?;

    let (num, sign) = if round_up {
        (sqrt_ratio - sqrt_sale_ratio, true)
    } else {
        (sqrt_sale_ratio - sqrt_ratio, false)
    };

    let c = muldiv(num, TWO_POW_128, sqrt_sale_ratio + sqrt_ratio, round_up).ok()?;

    let (term1, term2) = (e - c, e + c);

    let scale = if sign {
        muldiv(term2, TWO_POW_128, term1, round_up)
    } else {
        muldiv(term1, TWO_POW_128, term2, round_up)
    }
        .ok()?;

    muldiv(sqrt_sale_ratio, scale, TWO_POW_128, false).ok()
}

#[cfg(test)]
mod tests {
    use crate::math::twamm::sqrt_ratio::calculate_next_sqrt_ratio;
    use crate::math::uint::U256;
    use alloc::vec;

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
        fee: u128,
        expected: U256,
    }

    #[test]
    fn test_calculate_next_sqrt_ratio() {
        let test_cases = vec![
            TestCase {
                description: "liquidity is zero, price is sqrtSaleRatio",
                sqrt_ratio: U256::zero(),
                liquidity: 0,
                token0_sale_rate: TOKEN_SALE_RATE,
                token1_sale_rate: TOKEN_SALE_RATE,
                time_elapsed: 0,
                fee: 0,
                expected: U256::from_dec_str("340282366920938463463374607431768211456").unwrap(),
            },
            TestCase {
                description: "large exponent (> 88), price is sqrtSaleRatio",
                sqrt_ratio: U256::one() << 128,
                liquidity: 1,
                token0_sale_rate: TOKEN_SALE_RATE,
                token1_sale_rate: 1980 * ONE_E18 * SHIFT_32,
                time_elapsed: 1,
                fee: 0,
                expected: U256::from_dec_str("15141609448466370575819539296664158208000").unwrap(),
            },
            TestCase {
                description: "low liquidity, same sale rate",
                sqrt_ratio: U256::from(2u128) << 128,
                liquidity: 1,
                token0_sale_rate: TOKEN_SALE_RATE,
                token1_sale_rate: TOKEN_SALE_RATE,
                time_elapsed: 1,
                fee: 0,
                expected: U256::from_dec_str("340282366920938463463374607431768211456").unwrap(),
            },
            TestCase {
                description: "low liquidity, token0SaleRate > token1SaleRate",
                sqrt_ratio: U256::one() << 128,
                liquidity: 1,
                token0_sale_rate: 2 * TOKEN_SALE_RATE,
                token1_sale_rate: TOKEN_SALE_RATE,
                time_elapsed: 16,
                fee: 0,
                expected: U256::from_dec_str("240615969168004511538585310832300654592").unwrap(),
            },
            TestCase {
                description: "low liquidity, token1SaleRate > token0SaleRate",
                sqrt_ratio: U256::one() << 128,
                liquidity: 1,
                token0_sale_rate: TOKEN_SALE_RATE,
                token1_sale_rate: 2 * TOKEN_SALE_RATE,
                time_elapsed: 16,
                fee: 0,
                expected: U256::from_dec_str("481231938336009023077170621664601309184").unwrap(),
            },
            TestCase {
                description: "high liquidity, same sale rate",
                sqrt_ratio: U256::from(2u128) << 128,
                liquidity: 1_000_000 * ONE_E18,
                token0_sale_rate: TOKEN_SALE_RATE,
                token1_sale_rate: TOKEN_SALE_RATE,
                time_elapsed: 1,
                fee: 0,
                expected: U256::from_dec_str("680563712996817854544971649595310676716").unwrap(),
            },
            TestCase {
                description: "high liquidity, token0SaleRate > token1SaleRate",
                sqrt_ratio: U256::one() << 128,
                liquidity: 1_000_000 * ONE_E18,
                token0_sale_rate: 2 * TOKEN_SALE_RATE,
                token1_sale_rate: TOKEN_SALE_RATE,
                time_elapsed: 1,
                fee: 0,
                expected: U256::from_dec_str("340282026639252106118798709911530476351").unwrap(),
            },
            TestCase {
                description: "high liquidity, token1SaleRate > token0SaleRate",
                sqrt_ratio: U256::one() << 128,
                liquidity: 1_000_000 * ONE_E18,
                token0_sale_rate: TOKEN_SALE_RATE,
                token1_sale_rate: 2 * TOKEN_SALE_RATE,
                time_elapsed: 1,
                fee: 0,
                expected: U256::from_dec_str("340282707202965102147504331693640508329").unwrap(),
            },
            TestCase {
                description: "round in direction of price",
                sqrt_ratio: U256::from_dec_str("481231811499356508086519009265716982182").unwrap(),
                liquidity: 70_710_696_755_630_728_101_718_334,
                token0_sale_rate: 10_526_880_627_450_980_392_156_862_745,
                token1_sale_rate: 10_526_880_627_450_980_392_156_862_745,
                time_elapsed: 2040,
                fee: 0,
                expected: U256::from_dec_str("481207752340103616358571818546900413164").unwrap(),
            },
        ];

        for test_case in test_cases {
            let result = calculate_next_sqrt_ratio(
                test_case.sqrt_ratio,
                test_case.liquidity,
                test_case.token0_sale_rate,
                test_case.token1_sale_rate,
                test_case.time_elapsed,
                test_case.fee,
            )
                .unwrap(); // Assuming the function returns Option<U256>

            assert_eq!(
                result, test_case.expected,
                "Test case failed: {}",
                test_case.description
            );
        }
    }
}
