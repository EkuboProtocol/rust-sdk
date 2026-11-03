#![cfg(feature = "evm")]

use ekubo_sdk::{
    alloy_primitives::Address,
    chain::evm::{
        Evm, EvmConcentratedPool, EvmConcentratedPoolState, EvmFullRangePool,
        EvmFullRangePoolState, EvmStableswapPool,
    },
    math::{sqrt_ratio::SQRT_RATIO_ONE, swap::compute_step},
    quoting::{
        pools::{
            concentrated::TickSpacing, full_range::FullRangePoolTypeConfig,
            stableswap::StableswapPoolTypeConfig,
        },
        types::{Pool, PoolConfig, PoolKey, QuoteFees, QuoteParams, Tick, TokenAmount},
    },
};

#[test]
fn both_token_sides_reconcile_to_raw_step_at_identical_state_and_limit() {
    for fee in [0, 1, u64::MAX / 100, u64::MAX / 4] {
        for is_token1 in [false, true] {
            for amount in [0, 1, 9, 1_000_000, -1, -9, -1_000_000] {
                let key = PoolKey {
                    token0: Address::ZERO,
                    token1: Address::with_last_byte(1),
                    config: PoolConfig {
                        extension: Address::ZERO,
                        fee,
                        pool_type_config: FullRangePoolTypeConfig,
                    },
                };
                let pool = EvmFullRangePool::new(
                    key,
                    EvmFullRangePoolState {
                        sqrt_ratio: SQRT_RATIO_ONE,
                        liquidity: 1_000_000_000,
                    },
                )
                .unwrap();
                let increasing = is_token1 != (amount < 0);
                // Explicit limit is shared with the raw calculation, including dust.
                let limit = if increasing {
                    SQRT_RATIO_ONE << 1
                } else {
                    SQRT_RATIO_ONE >> 1
                };
                let step = compute_step::<Evm>(
                    SQRT_RATIO_ONE,
                    1_000_000_000,
                    limit,
                    amount,
                    is_token1,
                    fee,
                )
                .unwrap();
                let quote = pool
                    .quote(QuoteParams {
                        token_amount: TokenAmount {
                            token: if is_token1 { key.token1 } else { key.token0 },
                            amount,
                        },
                        sqrt_ratio_limit: Some(limit),
                        override_state: None,
                        meta: (),
                    })
                    .unwrap();
                let (expected0, expected1) = if increasing {
                    (0, step.fee_amount)
                } else {
                    (step.fee_amount, 0)
                };
                assert_eq!(quote.fees.fees0(), expected0);
                assert_eq!(quote.fees.fees1(), expected1);
                assert_eq!(quote.fees.extension0, 0);
                assert_eq!(quote.fees.extension1, 0);
                assert_eq!(quote.consumed_amount, step.consumed_amount);
                assert_eq!(quote.calculated_amount, step.calculated_amount);
                // The same raw step also underlies these models when no tick
                // or stableswap boundary is reached in this deterministic grid.
                let concentrated = EvmConcentratedPool::new(
                    PoolKey {
                        token0: key.token0,
                        token1: key.token1,
                        config: PoolConfig {
                            extension: Address::ZERO,
                            fee,
                            pool_type_config: TickSpacing(1),
                        },
                    },
                    EvmConcentratedPoolState {
                        sqrt_ratio: SQRT_RATIO_ONE,
                        liquidity: 1_000_000_000,
                        active_tick_index: Some(0),
                    },
                    vec![
                        Tick {
                            index: -100_000,
                            liquidity_delta: 1_000_000_000,
                        },
                        Tick {
                            index: 100_000,
                            liquidity_delta: -1_000_000_000,
                        },
                    ],
                )
                .unwrap();
                let stable = EvmStableswapPool::new(
                    PoolKey {
                        token0: key.token0,
                        token1: key.token1,
                        config: PoolConfig {
                            extension: Address::ZERO,
                            fee,
                            pool_type_config: StableswapPoolTypeConfig {
                                center_tick: 0,
                                amplification_factor: 1,
                            },
                        },
                    },
                    pool.state(),
                )
                .unwrap();
                let params = QuoteParams {
                    token_amount: TokenAmount {
                        token: if is_token1 { key.token1 } else { key.token0 },
                        amount,
                    },
                    sqrt_ratio_limit: Some(limit),
                    override_state: None,
                    meta: (),
                };
                let c = concentrated.quote(params).unwrap();
                let s = stable
                    .quote(QuoteParams {
                        token_amount: params.token_amount,
                        sqrt_ratio_limit: params.sqrt_ratio_limit,
                        override_state: None,
                        meta: (),
                    })
                    .unwrap();
                assert_eq!(c.fees, quote.fees);
                assert_eq!(s.fees, quote.fees);
                assert_eq!(c.consumed_amount, step.consumed_amount);
                assert_eq!(s.consumed_amount, step.consumed_amount);
                assert_eq!(c.calculated_amount, step.calculated_amount);
                assert_eq!(s.calculated_amount, step.calculated_amount);
            }
        }
    }
}

#[test]
fn totals_keep_token_denominations_separate_at_full_integer_precision() {
    let fees = QuoteFees {
        core0: u128::MAX - 9,
        core1: 23,
        extension0: 9,
        extension1: 42,
    };
    assert_eq!(fees.fees0(), u128::MAX);
    assert_eq!(fees.fees1(), 65);
    #[cfg(feature = "serde")]
    {
        let json = serde_json::to_string(&fees).unwrap();
        assert_eq!(serde_json::from_str::<QuoteFees>(&json).unwrap(), fees);
    }
}

#[test]
fn time_extensions_keep_only_selected_trader_charges_not_donations_or_virtual_orders() {
    use ekubo_sdk::{
        chain::evm::{EvmBoostedFeesConcentratedPool, EvmOraclePool, EvmTwammPool},
        quoting::types::LastTimeInfo,
    };
    let (token0, token1, extension) = (
        Address::ZERO,
        Address::with_last_byte(1),
        Address::with_last_byte(2),
    );
    let fee = u64::MAX / 100;
    let concentrated = EvmConcentratedPool::new(
        PoolKey {
            token0,
            token1,
            config: PoolConfig {
                extension,
                fee,
                pool_type_config: TickSpacing(1),
            },
        },
        EvmConcentratedPoolState {
            sqrt_ratio: SQRT_RATIO_ONE,
            liquidity: 1_000_000_000,
            active_tick_index: Some(0),
        },
        vec![
            Tick {
                index: -100_000,
                liquidity_delta: 1_000_000_000,
            },
            Tick {
                index: 100_000,
                liquidity_delta: -1_000_000_000,
            },
        ],
    )
    .unwrap();
    let boosted = EvmBoostedFeesConcentratedPool::new(
        concentrated.clone(),
        LastTimeInfo::Real(1),
        100,
        200,
        vec![ekubo_sdk::quoting::types::TimeRateDelta {
            time: 100,
            rate_delta0: -100,
            rate_delta1: -200,
        }],
    )
    .unwrap();
    let twamm = EvmTwammPool::new(
        token0,
        token1,
        fee,
        extension,
        SQRT_RATIO_ONE,
        1_000_000_000,
        1,
        100,
        200,
        vec![ekubo_sdk::quoting::types::TimeRateDelta {
            time: 100,
            rate_delta0: -100,
            rate_delta1: -200,
        }],
    )
    .unwrap();
    let oracle =
        EvmOraclePool::new(token0, token1, extension, SQRT_RATIO_ONE, 1_000_000_000, 1).unwrap();
    for token in [token0, token1] {
        for amount in [0, 1, 1_000_000, -1, -1_000_000] {
            for meta in [1, 42] {
                let b = boosted
                    .quote(QuoteParams {
                        token_amount: TokenAmount { token, amount },
                        sqrt_ratio_limit: None,
                        override_state: None,
                        meta,
                    })
                    .unwrap();
                let c = concentrated
                    .quote(QuoteParams {
                        token_amount: TokenAmount { token, amount },
                        sqrt_ratio_limit: None,
                        override_state: None,
                        meta: (),
                    })
                    .unwrap();
                assert_eq!(b.fees, c.fees); // Donation accrual is not a trader charge.
                let t = twamm
                    .quote(QuoteParams {
                        token_amount: TokenAmount { token, amount },
                        sqrt_ratio_limit: None,
                        override_state: None,
                        meta,
                    })
                    .unwrap();
                assert_eq!(
                    t.fees,
                    QuoteFees::core(
                        t.fees_paid,
                        token == token1 && amount >= 0 || token == token0 && amount < 0
                    )
                );
                let o = oracle
                    .quote(QuoteParams {
                        token_amount: TokenAmount { token, amount },
                        sqrt_ratio_limit: None,
                        override_state: None,
                        meta,
                    })
                    .unwrap();
                assert_eq!(o.fees, QuoteFees::default());
            }
        }
    }
}
