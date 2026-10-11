//! Reproduces the `ZeroSeedLaunch` vectors in `tests/vectors`: the frozen integer vectors of the
//! contracts packet and the parity vectors read from local `Core` and extension state and events.
#![cfg(any(feature = "evm-alloy-0_6", feature = "evm-alloy-1"))]

use core::str::FromStr;
use std::collections::HashMap;

use ekubo_sdk::{
    U256,
    alloy_primitives::Address,
    chain::evm::{Evm, EvmZeroSeedLaunchPool, EvmZeroSeedLaunchPoolKey},
    math::tick::to_sqrt_ratio,
    quoting::{
        pools::{
            concentrated::TickSpacing,
            zero_seed_launch::{
                ZeroSeedLaunchConfig, ZeroSeedLaunchFeeSchedule, ZeroSeedLaunchFullFillError,
                ZeroSeedLaunchParameterError, ZeroSeedLaunchParameters,
                ZeroSeedLaunchPoolConstructionError, ZeroSeedLaunchPoolQuoteError,
                ZeroSeedLaunchPoolState, ZeroSeedLaunchRange, check_launch_binding,
                preview_installation,
            },
        },
        types::{Pool, PoolConfig, PoolKey, QuoteParams, TokenAmount},
    },
};
use serde_json::Value;

const FROZEN: &str = include_str!("vectors/zero-seed-launch.json");
const PARITY: &str = include_str!("vectors/zero-seed-launch-parity.json");

/// Fixture quote tokens of the contract tests: the high one makes the launch token token0.
const QUOTE_HIGH: &str = "0xffffffffffffffffffffffffffffffffffffffff";
const QUOTE_LOW: &str = "0x0000000000000000000000000000000000010000";

const TRANSFER_FROM_FAILED: &str = "0x7939f424";
const TRADING_NOT_STARTED: &str = "0xacf75be8";
const SQRT_RATIO_LIMIT_WRONG_DIRECTION: &str = "0xa574a6b4";
/// solady `SafeCastLib.Overflow()`: a delta does not fit an int128.
const SAFE_CAST_OVERFLOW: &str = "0x35278d12";

fn address(s: &str) -> Address {
    Address::from_str(s).unwrap()
}

fn fixture_quotes() -> [Address; 2] {
    [address(QUOTE_HIGH), address(QUOTE_LOW)]
}

fn s<'a>(v: &'a Value, field: &str) -> &'a str {
    v[field]
        .as_str()
        .unwrap_or_else(|| panic!("{field} is not a string in {v}"))
}

fn num<T: FromStr>(v: &Value, field: &str) -> T
where
    T::Err: core::fmt::Debug,
{
    match &v[field] {
        Value::String(x) => x.parse().unwrap(),
        Value::Number(x) => x.to_string().parse().unwrap(),
        other => panic!("{field} is {other}"),
    }
}

fn state(v: &Value) -> ZeroSeedLaunchPoolState {
    ZeroSeedLaunchPoolState {
        sqrt_ratio: U256::from_str(s(v, "sqrt_ratio")).unwrap(),
        tick: num(v, "tick"),
        liquidity: num(v, "liquidity"),
    }
}

fn fee_schedule(v: &Value) -> ZeroSeedLaunchFeeSchedule {
    ZeroSeedLaunchFeeSchedule {
        trading_start: num(v, "tradingStart"),
        fee_duration: num(v, "feeDuration"),
        initial_fee: num(v, "initialFee"),
        final_fee: num(v, "finalFee"),
    }
}

/// The SDK's own initial `Core` state for an installation: price at the token-only bound, active
/// liquidity only while the tick is inside the position.
fn initial_state(range: &ZeroSeedLaunchRange, liquidity: u128) -> ZeroSeedLaunchPoolState {
    let tick = range.initial_tick();
    let (lower, upper) = range.pool_bounds();
    ZeroSeedLaunchPoolState {
        sqrt_ratio: to_sqrt_ratio::<Evm>(tick).unwrap(),
        tick,
        liquidity: if tick >= lower && tick < upper {
            liquidity
        } else {
            0
        },
    }
}

/// Builds the pool from `LaunchCreated` fields only.
fn pool_from_created(created: &Value, state: ZeroSeedLaunchPoolState) -> EvmZeroSeedLaunchPool {
    let token0 = address(s(created, "token0"));
    let token1 = address(s(created, "token1"));
    let token = address(s(created, "token"));
    let tick_spacing: u32 = num(created, "tickSpacing");
    let key = EvmZeroSeedLaunchPoolKey {
        token0,
        token1,
        config: PoolConfig {
            extension: address(s(created, "extension")),
            fee: num(created, "fee"),
            pool_type_config: TickSpacing(tick_spacing),
        },
    };
    let config = ZeroSeedLaunchConfig {
        range: ZeroSeedLaunchRange {
            launch_token_is_token1: token == token1,
            ask_tick: num(created, "askTick"),
            upper_tick: num(created, "upperTick"),
            tick_spacing,
        },
        liquidity: num(created, "liquidity"),
        fee: fee_schedule(created),
    };
    assert_eq!(
        config.range.pool_bounds(),
        (num(created, "tickLower"), num(created, "tickUpper"))
    );
    EvmZeroSeedLaunchPool::new(key, config, state, &fixture_quotes()).unwrap()
}

fn optional_limit(step: &Value) -> Option<U256> {
    let limit = U256::from_str(s(step, "limit")).unwrap();
    (!limit.is_zero()).then_some(limit)
}

#[derive(Default)]
struct GasSample {
    measured: u64,
    estimate: u64,
    ticks_crossed: u32,
    extra_lookups: u32,
}

#[test]
fn parity_with_local_core_state_and_events() {
    let vectors: Value = serde_json::from_str(PARITY).unwrap();
    let scenarios = vectors["scenarios"].as_array().unwrap();
    assert_eq!(scenarios.len(), 7);
    let mut compared = 0;
    let mut refused = 0;
    let mut claims = 0;
    let mut gas = Vec::new();

    for scenario in scenarios {
        let name = s(scenario, "name");
        let created = &scenario["create"];
        assert_eq!(
            s(created, "coreCodehash"),
            "0xc5f90c9d0dbc5037f8f9e248f4bb292e7c1824f584eb6550cb4cad525b38c71a"
        );
        let core_state = state(&created["state"]);
        let pool = pool_from_created(created, core_state);
        // The SDK's installation state equals what Core holds after create.
        assert_eq!(
            initial_state(&pool.launch().range, pool.launch().liquidity),
            core_state,
            "{name} initial state"
        );
        let launch_is1 = pool.launch().range.launch_token_is_token1;

        let mut current = pool.state();
        let mut fees = [0u128; 2];
        let mut first_fill = true;
        for step in scenario["steps"].as_array().unwrap() {
            let label = format!("{name} #{} {}", num::<u32>(step, "i"), s(step, "label"));
            if s(step, "label") == "sellClaimedExactIn" {
                // The creator's claim withdraws exactly the fees the SDK charged and leaves the
                // pool alone.
                let claim = &scenario["claim"];
                assert_eq!(
                    [num::<u128>(claim, "amount0"), num::<u128>(claim, "amount1")],
                    fees,
                    "{name} claimed ledger"
                );
                assert_eq!(
                    state(&claim["post"]),
                    current,
                    "{name} claim moved the pool"
                );
                fees = [0, 0];
                claims += 1;
            }
            assert_eq!(state(&step["pre"]), current, "{label}: chained pre state");
            let ts: u64 = num(step, "ts");
            let amount: i128 = num(step, "amount");
            let is_token1 = step["specified_is_token1"].as_bool().unwrap();
            let result = pool.simulate_swap(current, amount, is_token1, optional_limit(step), ts);

            if !step["ok"].as_bool().unwrap() {
                let error = s(step, "error");
                assert_eq!(
                    state(&step["post"]),
                    current,
                    "{label}: reverted swap moved"
                );
                match error {
                    TRADING_NOT_STARTED => assert_eq!(
                        result,
                        Err(ZeroSeedLaunchPoolQuoteError::TradingNotStarted),
                        "{label}"
                    ),
                    SQRT_RATIO_LIMIT_WRONG_DIRECTION => assert_eq!(
                        result,
                        Err(ZeroSeedLaunchPoolQuoteError::SqrtRatioLimitWrongDirection),
                        "{label}"
                    ),
                    SAFE_CAST_OVERFLOW => assert_eq!(
                        result,
                        Err(ZeroSeedLaunchPoolQuoteError::Overflow),
                        "{label}"
                    ),
                    TRANSFER_FROM_FAILED => {
                        // Settlement, not pool math: the test account cannot pay what the swap
                        // needs.
                        let swap = result.unwrap();
                        let (token_owed, quote_owed) = if launch_is1 {
                            (swap.delta1, swap.delta0)
                        } else {
                            (swap.delta0, swap.delta1)
                        };
                        let held_token: u128 = num(step, "held_token");
                        let held_quote: u128 = num(step, "held_quote");
                        assert!(
                            (token_owed > 0 && token_owed as u128 > held_token)
                                || (quote_owed > 0 && quote_owed as u128 > held_quote),
                            "{label}: owes {token_owed}/{quote_owed}, holds {held_token}/{held_quote}"
                        );
                    }
                    other => panic!("{label}: unexpected revert {other}"),
                }
                refused += 1;
                continue;
            }

            let swap = result.unwrap_or_else(|e| panic!("{label}: {e}"));
            let event = &step["event"];
            assert_eq!(swap.delta0, num::<i128>(step, "delta0"), "{label} delta0");
            assert_eq!(swap.delta1, num::<i128>(step, "delta1"), "{label} delta1");
            assert_eq!(
                swap.delta0,
                num::<i128>(event, "delta0"),
                "{label} event delta0"
            );
            assert_eq!(
                swap.delta1,
                num::<i128>(event, "delta1"),
                "{label} event delta1"
            );
            assert_eq!(swap.fee_rate, num::<u64>(event, "fee_rate"), "{label} rate");
            assert_eq!(swap.fee_rate, num::<u64>(step, "fee_at"), "{label} feeAt");
            assert_eq!(
                swap.fee_amount,
                num::<u128>(event, "fee_amount"),
                "{label} fee"
            );
            assert_eq!(
                swap.fee_is_token1,
                event["fee_is_token1"].as_bool().unwrap(),
                "{label} fee side"
            );
            let ledger = [
                num::<u128>(step, "ledger_delta0"),
                num::<u128>(step, "ledger_delta1"),
            ];
            let side = usize::from(swap.fee_is_token1);
            assert_eq!(ledger[side], swap.fee_amount, "{label} ledger");
            assert_eq!(ledger[1 - side], 0, "{label} other ledger");
            fees[side] += swap.fee_amount;
            assert_eq!(swap.state_after, state(&step["post"]), "{label} post state");

            // The Pool interface reports the same fill.
            let specified_token = if is_token1 {
                pool.key().token1
            } else {
                pool.key().token0
            };
            let quote = pool
                .quote(QuoteParams {
                    token_amount: TokenAmount {
                        token: specified_token,
                        amount,
                    },
                    sqrt_ratio_limit: optional_limit(step),
                    override_state: Some(current),
                    meta: ts,
                })
                .unwrap();
            let (specified, calculated) = if is_token1 {
                (swap.delta1, swap.delta0)
            } else {
                (swap.delta0, swap.delta1)
            };
            assert_eq!(quote.consumed_amount, specified, "{label} consumed");
            assert_eq!(
                quote.calculated_amount,
                calculated.unsigned_abs(),
                "{label} calc"
            );
            assert_eq!(quote.fees_paid, swap.fee_amount);
            assert_eq!(quote.state_after, swap.state_after);

            if swap.delta0 != 0 || swap.delta1 != 0 {
                let r = swap.resources;
                let sample = GasSample {
                    measured: num(step, "gas"),
                    estimate: r.uncalibrated_gas_estimate(),
                    ticks_crossed: r.concentrated.initialized_ticks_crossed,
                    extra_lookups: r.concentrated.extra_distinct_bitmap_lookups,
                };
                if !first_fill {
                    gas.push((label.clone(), sample));
                }
                first_fill = false;
            }
            current = swap.state_after;
            compared += 1;
        }
    }
    assert_eq!(claims, 6);
    assert_eq!(compared + refused, 307);
    assert!(compared >= 240, "compared {compared}");

    // Gas: the fitted estimate stays within 30% of the measured in-test gas for every fill except
    // the first of each launch and the two that write a zero storage slot (the first fee after the
    // claim, the first tokens bought after the holder sold out), which it underestimates. Set
    // ZERO_SEED_GAS_TABLE to print the table.
    let mut worst = 0f64;
    let mut cold = 0;
    for (label, g) in &gas {
        let error = (g.estimate as f64 - g.measured as f64) / g.measured as f64;
        if label.ends_with("sellClaimedExactIn") || label.ends_with("farFutureBuy") {
            assert!(
                g.estimate < g.measured && g.measured - g.estimate < 30_000,
                "{label}"
            );
            cold += 1;
            continue;
        }
        if std::env::var_os("ZERO_SEED_GAS_TABLE").is_some() {
            println!(
                "{label}\tmeasured={}\testimate={}\tticks={}\tlookups={}\terr={:+.3}",
                g.measured, g.estimate, g.ticks_crossed, g.extra_lookups, error
            );
        }
        worst = worst.max(error.abs());
    }
    assert_eq!(cold, 12);
    assert!(worst < 0.30, "worst gas estimate error {worst}");
}

fn parameters_of(preview: &Value) -> ZeroSeedLaunchParameters {
    let label = s(preview, "label");
    ZeroSeedLaunchParameters {
        quote_token: address(s(preview, "quote")),
        supply: num(preview, "supply"),
        range: ZeroSeedLaunchRange {
            launch_token_is_token1: label.starts_with("t1"),
            ask_tick: num(preview, "askTick"),
            upper_tick: num(preview, "upperTick"),
            tick_spacing: num(preview, "tickSpacing"),
        },
        fee: fee_schedule(preview),
    }
}

/// Decodes a contract revert into the SDK error it corresponds to.
fn decode_error(data: &str) -> ZeroSeedLaunchParameterError {
    let word = |i: usize| -> u128 {
        let start = 10 + 64 * i;
        u128::from_str_radix(&data[start + 32..start + 64], 16).unwrap()
    };
    match &data[..10] {
        "0x658d8331" => ZeroSeedLaunchParameterError::UnsupportedQuoteToken,
        "0xe5239090" => ZeroSeedLaunchParameterError::InvalidParameters,
        "0xcd4e6167" => ZeroSeedLaunchParameterError::FeeTooHigh,
        "0xf75a271a" => ZeroSeedLaunchParameterError::InvalidFeeSchedule,
        "0xe0839259" => ZeroSeedLaunchParameterError::InvalidTradingStart,
        "0x89fd41b1" => ZeroSeedLaunchParameterError::BoundsTickSpacing,
        "0x10074548" => ZeroSeedLaunchParameterError::ZeroLiquidity,
        // solady SafeCastLib `Overflow()`
        "0x35278d12" => ZeroSeedLaunchParameterError::Overflow,
        "0x20ea795f" => ZeroSeedLaunchParameterError::LiquidityAboveTickCap {
            liquidity: word(0),
            cap: word(1),
        },
        "0xad00b597" => ZeroSeedLaunchParameterError::SupplyNotExactlyInstallable {
            requested: word(0),
            installable: word(1),
        },
        other => panic!("unknown revert {other}"),
    }
}

#[test]
fn installation_preview_and_binding_match_the_contract() {
    let vectors: Value = serde_json::from_str(PARITY).unwrap();
    let mut by_label = HashMap::new();
    let mut ok = 0;
    let previews = vectors["previews"].as_array().unwrap();
    for preview in previews {
        let label = s(preview, "label");
        let parameters = parameters_of(preview);
        let now: u64 = num(preview, "now");
        let result = preview_installation(&parameters, now, &fixture_quotes());
        if preview["ok"].as_bool().unwrap() {
            let installation = result.unwrap_or_else(|e| panic!("{label}: {e}"));
            let token_is0 = s(preview, "token") == s(preview, "token0");
            assert_eq!(
                token_is0, !parameters.range.launch_token_is_token1,
                "{label}"
            );
            assert_eq!(
                installation.tick_lower,
                num::<i32>(preview, "tickLower"),
                "{label}"
            );
            assert_eq!(
                installation.tick_upper,
                num::<i32>(preview, "tickUpper"),
                "{label}"
            );
            assert_eq!(
                installation.initial_tick,
                num::<i32>(preview, "initialTick"),
                "{label}"
            );
            assert_eq!(
                installation.liquidity,
                num::<u128>(preview, "liquidity"),
                "{label}"
            );
            assert_eq!(
                installation.installed_supply,
                num::<u128>(preview, "installedSupply"),
                "{label}"
            );
            assert!(
                installation.installed_supply <= parameters.supply,
                "{label}"
            );
            ok += 1;
        } else {
            assert_eq!(result, Err(decode_error(s(preview, "err"))), "{label}");
        }
        by_label.insert(label.to_owned(), parameters);
    }
    assert_eq!(previews.len(), 108);
    assert_eq!(ok, 40);

    let bindings = vectors["bindings"].as_array().unwrap();
    assert_eq!(bindings.len(), 4 * ok);
    for binding in bindings {
        let label = s(binding, "label");
        let mut parameters = by_label[label];
        parameters.supply = num(binding, "supply");
        let liquidity: u128 = num(binding, "liquidity");
        // Creation happens in the block after the preview's timestamp in the generator, at the
        // same timestamp.
        let result = check_launch_binding(&parameters, liquidity, 1, &fixture_quotes());
        if binding["ok"].as_bool().unwrap() {
            let installation = result.unwrap_or_else(|e| panic!("{label}: {e}"));
            assert_eq!(installation.installed_supply, parameters.supply);
            assert_eq!(installation.liquidity, liquidity);
        } else {
            assert_eq!(
                result,
                Err(decode_error(s(binding, "err"))),
                "{label} {liquidity}"
            );
        }
    }

    // The documented trap: previewing the installed supply again does not return the same pair.
    let frozen = &by_label["t0_18_6_frozen"];
    let first = preview_installation(frozen, 1, &fixture_quotes()).unwrap();
    let mut again = *frozen;
    again.supply = first.installed_supply;
    let second = preview_installation(&again, 1, &fixture_quotes()).unwrap();
    assert_eq!(second.liquidity, first.liquidity - 1);
    assert!(second.installed_supply < first.installed_supply);
}

#[test]
fn frozen_integer_vectors() {
    let vectors: Value = serde_json::from_str(FROZEN).unwrap();
    let fixture = &vectors["fixture"];
    let fee = |duration: u32| ZeroSeedLaunchFeeSchedule {
        trading_start: num(fixture, "trading_start"),
        fee_duration: duration,
        initial_fee: num(fixture, "fee_initial_q64"),
        final_fee: num(fixture, "fee_final_q64"),
    };
    let start: u64 = num(fixture, "trading_start");

    for entry in vectors["fee"].as_array().unwrap() {
        let duration: u32 = num(entry, "duration");
        let offset: i128 = num(entry, "t_minus_start");
        let t = u64::try_from(i128::from(start) + offset).unwrap();
        assert_eq!(
            fee(duration).fee_at(t),
            num::<u64>(entry, "fee_q64"),
            "{entry}"
        );
    }

    let mut pools = HashMap::new();
    for entry in vectors["create"].as_array().unwrap() {
        let is1 = s(entry, "order") == "t1";
        let quote = if is1 { QUOTE_LOW } else { QUOTE_HIGH };
        let range = ZeroSeedLaunchRange {
            launch_token_is_token1: is1,
            ask_tick: num(entry, "ask"),
            upper_tick: num(entry, "upper"),
            tick_spacing: num(fixture, "tick_spacing"),
        };
        let parameters = ZeroSeedLaunchParameters {
            quote_token: address(quote),
            supply: num(entry, "requested"),
            range,
            fee: fee(3600),
        };
        let installation = preview_installation(&parameters, 1, &fixture_quotes()).unwrap();
        assert_eq!(
            installation.installed_supply,
            num::<u128>(entry, "installed")
        );
        assert_eq!(installation.liquidity, num::<u128>(entry, "liquidity"));
        assert_eq!(installation.tick_lower, num::<i32>(entry, "tickLower"));
        assert_eq!(installation.tick_upper, num::<i32>(entry, "tickUpper"));
        assert_eq!(installation.initial_tick, num::<i32>(entry, "initialTick"));

        // A launch token address on the right side of the fixture quote.
        let token = address("0x00000000000000000000000000000000000a0000");
        let token = if is1 {
            address("0x00000000000000000000000000000000000f0000")
        } else {
            token
        };
        let (token0, token1) = if is1 {
            (address(quote), token)
        } else {
            (token, address(quote))
        };
        let pool = EvmZeroSeedLaunchPool::new(
            PoolKey {
                token0,
                token1,
                config: PoolConfig {
                    extension: address("0x5100000000000000000000000000000000000000"),
                    fee: 0,
                    pool_type_config: TickSpacing(range.tick_spacing),
                },
            },
            ZeroSeedLaunchConfig {
                range,
                liquidity: installation.liquidity,
                fee: fee(3600),
            },
            initial_state(&range, installation.liquidity),
            &fixture_quotes(),
        )
        .unwrap();
        pools.insert(
            format!("{}|18/{}", s(entry, "order"), &s(entry, "dec")[3..]),
            (pool, token, address(quote)),
        );
    }

    let quote_fill = |pool: &EvmZeroSeedLaunchPool,
                      state: ZeroSeedLaunchPoolState,
                      token: Address,
                      amount: i128| {
        pool.quote(QuoteParams {
            token_amount: TokenAmount { token, amount },
            sqrt_ratio_limit: None,
            override_state: Some(state),
            meta: start,
        })
        .unwrap()
    };

    let mut checked = 0;
    for entry in vectors["trade"].as_array().unwrap() {
        let key = format!("{}|{}", s(entry, "order"), s(entry, "decimals"));
        let (pool, token, quote) = &pools[&key];
        let state = pool.state();
        match s(entry, "step") {
            "buyExactIn" => {
                let q = quote_fill(pool, state, *quote, num(entry, "quoteIn"));
                assert_eq!(q.calculated_amount, num::<u128>(entry, "net"), "{entry}");
                assert_eq!(q.fees_paid, num::<u128>(entry, "fee"), "{entry}");
                assert_eq!(
                    q.calculated_amount + q.fees_paid,
                    num::<u128>(entry, "gross"),
                    "{entry}"
                );
                checked += 1;
            }
            "buyExactOut" => {
                // After the exact-input buy of one quote unit.
                let unit = 10i128.pow(if key.ends_with("18/6") { 6 } else { 18 });
                let first = quote_fill(pool, state, *quote, unit);
                let net: i128 = num(entry, "tokenOut");
                let q = quote_fill(pool, first.state_after, *token, -net);
                assert_eq!(q.consumed_amount, -net);
                assert_eq!(q.calculated_amount, num::<u128>(entry, "paid"), "{entry}");
                assert_eq!(q.fees_paid, num::<u128>(entry, "fee"), "{entry}");
                assert_eq!(
                    q.calculated_amount - q.fees_paid,
                    num::<u128>(entry, "calcQuote"),
                    "{entry}"
                );
                // Then sell half of the 2 * net held, exact input.
                let sell = vectors["trade"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .find(|e| {
                        s(e, "order") == s(entry, "order")
                            && s(e, "decimals") == s(entry, "decimals")
                            && s(e, "step") == "sellExactIn"
                    })
                    .unwrap();
                let held = 2 * net;
                assert_eq!(num::<i128>(sell, "tokenIn"), held / 2);
                let q = quote_fill(pool, q.state_after, *token, held / 2);
                assert_eq!(q.calculated_amount, num::<u128>(sell, "quoteOut"), "{sell}");
                checked += 2;
            }
            _ => {}
        }
    }
    assert_eq!(checked, 12);

    // The deployed router fixture's 1e18 quote buy and the one-unit dust buy.
    for entry in vectors["router"].as_array().unwrap() {
        let (pool, _, quote) = &pools[&format!("{}|18/18", s(entry, "order"))];
        let q = quote_fill(pool, pool.state(), *quote, num(entry, "paid"));
        assert_eq!(q.calculated_amount, num::<u128>(entry, "got"), "{entry}");
    }
    let dust = &vectors["other"][0];
    let (pool, _, quote) = &pools["t0|18/18"];
    let q = quote_fill(pool, pool.state(), *quote, num(dust, "quoteIn"));
    assert_eq!(
        (q.calculated_amount, q.fees_paid),
        (num(dust, "net"), num(dust, "fee"))
    );
}

#[test]
fn full_fill_refusal_and_explicit_partial_result() {
    let vectors: Value = serde_json::from_str(PARITY).unwrap();
    let mut overflow_checked = false;
    for scenario in vectors["scenarios"].as_array().unwrap() {
        let created = &scenario["create"];
        let pool = pool_from_created(created, state(&created["state"]));
        let find = |label: &str| {
            scenario["steps"]
                .as_array()
                .unwrap()
                .iter()
                .find(|step| s(step, "label") == label)
                .unwrap()
        };
        let params = |step: &Value| {
            let token = if step["specified_is_token1"].as_bool().unwrap() {
                pool.key().token1
            } else {
                pool.key().token0
            };
            QuoteParams {
                token_amount: TokenAmount {
                    token,
                    amount: num(step, "amount"),
                },
                sqrt_ratio_limit: optional_limit(step),
                override_state: Some(state(&step["pre"])),
                meta: num(step, "ts"),
            }
        };

        if s(scenario, "name").starts_with("overflow") {
            // Near the top of the price range an exact-input buy can take all its input and pay
            // out nothing (the creator fee takes the last rounded unit); an exact-output buy of
            // one raw token does not fit an int128 and reverts.
            for label in ["buyMaxExactIn", "buyHalfMaxExactIn"] {
                let step = find(label);
                let q = pool.quote(params(step)).unwrap();
                assert_eq!(q.consumed_amount, num::<i128>(step, "amount"), "{label}");
                assert_eq!(q.calculated_amount, 0, "{label}");
                assert_eq!(
                    pool.quote_full_fill(params(step)),
                    Err(ZeroSeedLaunchFullFillError::ZeroOutput),
                    "{label}"
                );
            }
            assert_eq!(
                pool.quote_full_fill(params(find("buyOneTokenExactOut"))),
                Err(ZeroSeedLaunchFullFillError::Quote(
                    ZeroSeedLaunchPoolQuoteError::Overflow
                ))
            );
            overflow_checked = true;
            continue;
        }
        // Buying beyond the inventory: the low-level quote is the explicit partial fill Core
        // executes; the full-fill variant refuses it.
        for label in ["exhaustExactIn", "exhaustExactOut", "buyToMidLimit"] {
            let step = find(label);
            let partial = pool.quote(params(step)).unwrap();
            let requested: i128 = num(step, "amount");
            assert!(partial.consumed_amount.abs() < requested.abs(), "{label}");
            assert_eq!(
                pool.quote_full_fill(params(step)),
                Err(ZeroSeedLaunchFullFillError::PartialFill {
                    requested,
                    filled: partial.consumed_amount
                }),
                "{label}"
            );
        }
        // Nothing left above the upper bound and no bid at the ask: zero fills.
        for label in [
            "afterUpperExactIn",
            "afterUpperExactOut",
            "noBidSellExactIn",
        ] {
            let step = find(label);
            let q = pool.quote(params(step)).unwrap();
            assert_eq!(
                (q.consumed_amount, q.calculated_amount, q.fees_paid),
                (0, 0, 0)
            );
            assert!(matches!(
                pool.quote_full_fill(params(step)),
                Err(ZeroSeedLaunchFullFillError::PartialFill { filled: 0, .. })
            ));
        }
        // A full exact-input fill that pays out nothing is refused too.
        let step = find("dustSellExactIn");
        let q = pool.quote(params(step)).unwrap();
        if q.calculated_amount == 0 {
            assert_eq!(
                pool.quote_full_fill(params(step)),
                Err(ZeroSeedLaunchFullFillError::ZeroOutput)
            );
        }
        // An ordinary buy passes.
        assert!(pool.quote_full_fill(params(find("buyExactIn"))).is_ok());
    }
    assert!(overflow_checked);
}

#[test]
fn unsupported_quote_tokens_fail_closed() {
    let vectors: Value = serde_json::from_str(PARITY).unwrap();
    let created = &vectors["scenarios"][0]["create"];
    let mut key = EvmZeroSeedLaunchPoolKey {
        token0: address(s(created, "token0")),
        token1: address(s(created, "token1")),
        config: PoolConfig {
            extension: address(s(created, "extension")),
            fee: 0,
            pool_type_config: TickSpacing(num(created, "tickSpacing")),
        },
    };
    let launch = *pool_from_created(created, state(&created["state"])).launch();
    let core = state(&created["state"]);
    assert_eq!(
        EvmZeroSeedLaunchPool::new(key, launch, core, &[]),
        Err(ZeroSeedLaunchPoolConstructionError::UnsupportedQuoteToken)
    );
    assert_eq!(
        EvmZeroSeedLaunchPool::new(key, launch, core, &[key.token0]),
        Err(ZeroSeedLaunchPoolConstructionError::UnsupportedQuoteToken)
    );
    key.config.fee = 1;
    assert_eq!(
        EvmZeroSeedLaunchPool::new(key, launch, core, &[key.token1]),
        Err(ZeroSeedLaunchPoolConstructionError::FeeMustBeZero)
    );

    let preview = &vectors["previews"][0];
    let parameters = parameters_of(preview);
    assert_eq!(
        preview_installation(&parameters, 1, &[]),
        Err(ZeroSeedLaunchParameterError::UnsupportedQuoteToken)
    );
    assert!(preview_installation(&parameters, 1, &[parameters.quote_token]).is_ok());
}
