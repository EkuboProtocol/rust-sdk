use crate::math::{sqrt_ratio::SQRT_RATIO_ONE, twamm::exp2::exp2, uint::U256};
use crate::{chain::Chain, math::muldiv::muldiv};
use num_traits::Zero;

pub fn calculate_next_sqrt_ratio<C: Chain>(
    sqrt_ratio: U256,
    liquidity: u128,
    sale_rate_token0: u128,
    sale_rate_token1: u128,
    time_elapsed: u32,
    fee: C::Fee,
) -> U256 {
    let sqrt_sale_ratio = compute_sqrt_sale_ratio_x128(sale_rate_token0, sale_rate_token1);

    let round_up = sqrt_ratio > sqrt_sale_ratio;
    let (c, c_sign_negative) = (compute_c(sqrt_ratio, sqrt_sale_ratio), round_up);

    if c.is_zero() || liquidity.is_zero() {
        return sqrt_sale_ratio;
    }

    let sale_rate = ((U256::from(sale_rate_token1) * U256::from(sale_rate_token0)).integer_sqrt()
        * (C::fee_denominator() - fee))
        / C::fee_denominator();

    let round_up = sqrt_ratio > sqrt_sale_ratio;

    let exponent: U256 =
        (sale_rate * U256::from(time_elapsed) * U256([12392656037, 0, 0, 0])) / liquidity;

    if exponent >= U256::from(0x400000000000000000_u128) {
        return sqrt_sale_ratio;
    }

    let e_pow_exponent_x128 = U256::from(exp2(exponent.low_u128())) << 64;

    let mut sqrt_ratio_next = if c_sign_negative {
        muldiv(
            sqrt_sale_ratio,
            e_pow_exponent_x128.checked_add(c).unwrap(),
            e_pow_exponent_x128.checked_sub(c).unwrap(),
            false,
        )
        .unwrap_or(sqrt_sale_ratio)
    } else {
        muldiv(
            sqrt_sale_ratio,
            e_pow_exponent_x128.checked_sub(c).unwrap(),
            e_pow_exponent_x128.checked_add(c).unwrap(),
            false,
        )
        .unwrap_or(sqrt_sale_ratio)
    };

    // we should never exceed the sale ratio
    if round_up {
        sqrt_ratio_next = sqrt_ratio_next.max(sqrt_sale_ratio);
    } else {
        sqrt_ratio_next = sqrt_ratio_next.min(sqrt_sale_ratio);
    }

    sqrt_ratio_next
}

fn compute_sqrt_sale_ratio_x128(sale_rate_token0: u128, sale_rate_token1: u128) -> U256 {
    let sale_ratio: U256 = (U256::from(sale_rate_token1) << 128) / sale_rate_token0;

    if sale_ratio < U256([0, 0, 1, 0]) {
        // full precision
        (sale_ratio << 128).integer_sqrt()
    } else if sale_ratio < U256([0, 0, 0, 1]) {
        // we know it only has 192 bits, so we can shift it 64 before rooting to get more precision
        (sale_ratio << 64).integer_sqrt() << 32
    } else {
        (sale_ratio << 16).integer_sqrt() << 56
    }
}

fn compute_c(sqrt_ratio: U256, sqrt_sale_ratio: U256) -> U256 {
    muldiv(
        sqrt_sale_ratio.abs_diff(sqrt_ratio),
        SQRT_RATIO_ONE,
        sqrt_sale_ratio + sqrt_ratio,
        false,
    )
    .unwrap()
}

#[cfg(test)]
mod tests {
    use super::*;

    const ONE_E18: u128 = 1_000_000_000_000_000_000; // 10^18
    const SHIFT_32: u128 = 1u128 << 32; // 2^32 = 4294967296
    const TOKEN_SALE_RATE: u128 = ONE_E18 * SHIFT_32; // 10^18 * 2^32

    mod calculate_next_sqrt_ratio {
        use crate::chain::{tests::chain_test, Evm};

        use super::*;

        fn run_case<C: Chain>(
            sqrt_ratio: U256,
            liquidity: u128,
            token0_sale_rate: u128,
            token1_sale_rate: u128,
            time_elapsed: u32,
        ) -> U256 {
            calculate_next_sqrt_ratio::<C>(
                sqrt_ratio,
                liquidity,
                token0_sale_rate,
                token1_sale_rate,
                time_elapsed,
                C::Fee::zero(),
            )
        }

        fn dec(value: &str) -> U256 {
            U256::from_dec_str(value).unwrap()
        }

        chain_test!(zero_liquidity_price_eq_sale_ratio, {
            let result = run_case::<ChainTy>(
                U256::zero(),
                0,
                TOKEN_SALE_RATE,
                TOKEN_SALE_RATE,
                0,
            );
            assert_eq!(result, dec("340282366920938463463374607431768211456"));
        });

        chain_test!(large_exponent_price_sqrt_ratio, {
            let result = run_case::<ChainTy>(
                U256::one() << 128,
                1,
                TOKEN_SALE_RATE,
                1980 * ONE_E18 * SHIFT_32,
                1,
            );
            assert_eq!(result, dec("15141609448466370575828005229206655991808"));
        });

        chain_test!(low_liquiidty_same_sale_ratio, {
            let result = run_case::<ChainTy>(
                U256::from(2u128) << 128,
                1,
                TOKEN_SALE_RATE,
                TOKEN_SALE_RATE,
                1,
            );
            assert_eq!(result, dec("340282366920938463463374607431768211456"));
        });

        chain_test!(low_liquidity_token0_gt_token1, {
            let result = run_case::<ChainTy>(
                U256::one() << 128,
                1,
                2 * TOKEN_SALE_RATE,
                TOKEN_SALE_RATE,
                16,
            );
            assert_eq!(result, dec("240615969168004511545033772477625056927"));
        });

        chain_test!(low_liquidity_token1_gt_token0, {
            let result = run_case::<ChainTy>(
                U256::one() << 128,
                1,
                TOKEN_SALE_RATE,
                2 * TOKEN_SALE_RATE,
                16,
            );
            assert_eq!(result, dec("481231938336009023090067544951314448384"));
        });

        chain_test!(high_liquidity_same_sale_ratio, {
            let result = run_case::<ChainTy>(
                U256::from(2u128) << 128,
                1_000_000 * ONE_E18,
                TOKEN_SALE_RATE,
                TOKEN_SALE_RATE,
                1,
            );
            assert_eq!(result, dec("680563712996817890757827685335626524191"));
        });

        chain_test!(high_liquidity_token0_gt_token1, {
            let result = run_case::<ChainTy>(
                U256::one() << 128,
                1_000_000 * ONE_E18,
                2 * TOKEN_SALE_RATE,
                TOKEN_SALE_RATE,
                1,
            );
            assert_eq!(result, dec("340282026639252118183347287047607050305"));
        });

        chain_test!(high_liquidity_token1_gt_token0, {
            let result = run_case::<ChainTy>(
                U256::one() << 128,
                1_000_000 * ONE_E18,
                TOKEN_SALE_RATE,
                2 * TOKEN_SALE_RATE,
                1,
            );
            assert_eq!(result, dec("340282707202965090089453576058304747105"));
        });

        chain_test!(round_in_direction_of_price, {
            let result = run_case::<ChainTy>(
                U256::from_dec_str("481231811499356508086519009265716982182").unwrap(),
                70_710_696_755_630_728_101_718_334,
                10_526_880_627_450_980_392_156_862_745,
                10_526_880_627_450_980_392_156_862_745,
                2040,
            );
            assert_eq!(result, dec("481207752340104468493822013619596511452"));
        });

        mod evm {
            use super::*;

            #[test]
            fn solidity_example_lower() {
                assert_eq!(
                    calculate_next_sqrt_ratio::<Evm>(
                        // price is 10k**2
                        U256::from_dec_str("3402823669209384634633746074317682114560000").unwrap(),
                        // low liquidity
                        10_000,
                        // 0.1 per second
                        458864027,
                        // 0.065384615212679 per second
                        280824784,
                        46_800,
                        0
                    ),
                    // expect 2.100594408164651 ** 2
                    U256::from_dec_str("714795237151155238093993646993154300599").unwrap()
                );
            }

            #[test]
            fn solidity_example_upper() {
                assert_eq!(
                    calculate_next_sqrt_ratio::<Evm>(
                        U256::from_dec_str("2738179289227384381927918250491904").unwrap(),
                        4472135213867,
                        3728260255814876407785,
                        1597830095238095,
                        2688,
                        9223372036854775
                    ),
                    U256::from_dec_str("75660834358443397537995256863811143").unwrap()
                );
            }
        }
    }
}
