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
                ZeroSeedLaunchInstance, ZeroSeedLaunchLocalPreview, ZeroSeedLaunchParameterError,
                ZeroSeedLaunchParameters, ZeroSeedLaunchPoolConstructionError,
                ZeroSeedLaunchPoolQuoteError, ZeroSeedLaunchPoolState, ZeroSeedLaunchRange,
                check_launch_binding, check_launch_binding_math, preview_installation,
                preview_installation_math, validate_claim_recipient,
            },
        },
        types::{Pool, PoolConfig, PoolKey, QuoteParams, TokenAmount},
    },
};
use serde_json::Value;

const FROZEN: &str = include_str!("vectors/zero-seed-launch.json");
const PARITY: &str = include_str!("vectors/zero-seed-launch-parity.json");
const INDEXER: &str = include_str!("vectors/zero-seed-launch-indexer.json");

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

fn instance(created: &Value) -> ZeroSeedLaunchInstance {
    ZeroSeedLaunchInstance {
        chain_id: 31337,
        extension: address(s(created, "extension")),
        core: address("0x00000000000014aa86c5d3c41765bb24e11bd701"),
        constructor_quote: address(s(created, "constructorQuote")),
        quote_token_getter: address(s(created, "constructorQuote")),
        extension_runtime: U256::from_str(s(created, "extensionCodehash")).unwrap(),
        core_runtime: U256::from_str(s(created, "coreCodehash")).unwrap(),
        quote_runtime: U256::from_str(s(created, "quoteCodehash")).unwrap(),
    }
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
        decay_factor: num(v, "decayFactor"),
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
    let pool = math_pool_from_created(created, state);
    assert!(
        EvmZeroSeedLaunchPool::new(pool.key(), *pool.launch(), state, &instance(created)).is_err()
    );
    pool
}

fn supported_pool_from_created(
    created: &Value,
    state: ZeroSeedLaunchPoolState,
) -> EvmZeroSeedLaunchPool {
    let (key, config) = pool_inputs_from_created(created);
    EvmZeroSeedLaunchPool::new(key, config, state, &instance(created)).unwrap()
}

fn math_pool_from_created(
    created: &Value,
    state: ZeroSeedLaunchPoolState,
) -> EvmZeroSeedLaunchPool {
    let (key, config) = pool_inputs_from_created(created);
    EvmZeroSeedLaunchPool::new_math(key, config, state).unwrap()
}

fn pool_inputs_from_created(created: &Value) -> (EvmZeroSeedLaunchPoolKey, ZeroSeedLaunchConfig) {
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
    (key, config)
}

fn indexer_state(word: &str) -> ZeroSeedLaunchPoolState {
    let word = U256::from_str(word).unwrap();
    let float: U256 = word >> 160usize;
    let mantissa_mask = (U256::from(1) << 94) - U256::from(1);
    let exponent: u8 = (float >> 94usize).try_into().unwrap();
    let tick_bits: u32 = ((word >> 128usize) & U256::from(u32::MAX))
        .try_into()
        .unwrap();
    ZeroSeedLaunchPoolState {
        sqrt_ratio: (float & mantissa_mask) << (2 + 32 * exponent),
        tick: tick_bits as i32,
        liquidity: (word & U256::from(u128::MAX)).try_into().unwrap(),
    }
}

// Decode the actual emitted LaunchCreated ABI and same-block packed Core state, without
// substituting addresses, states or installation math. The original receipt is copied verbatim.
fn indexer_created_vectors() -> Value {
    let fixture: Value = serde_json::from_str(INDEXER).unwrap();
    let topic = ekubo_sdk::alloy_primitives::keccak256(
        "LaunchCreated(bytes32,address,address,(address,address,bytes32),bytes32,uint128,(address,string,string,uint8,uint128,uint128,int32,int32,uint32,uint64,uint32,uint64,uint64,uint64,bytes32))",
    ).to_string();
    let mut scenarios = Vec::new();
    for branch in fixture["branches"].as_object().unwrap().values() {
        for log in branch["logs"].as_array().unwrap() {
            if log["topics"][0].as_str() != Some(topic.as_str()) {
                continue;
            }
            let data = &s(log, "data")[2..];
            let word =
                |i: usize| U256::from_str(&format!("0x{}", &data[i * 64..(i + 1) * 64])).unwrap();
            let addr = |i: usize| format!("0x{}", &data[i * 64 + 24..(i + 1) * 64]);
            let offset: usize = word(5).try_into().unwrap();
            let p = offset / 32;
            let signed = |i| {
                let n: u32 = (word(i) & U256::from(u32::MAX)).try_into().unwrap();
                n as i32
            };
            let emitted_key = format!("0x{}", &data[128..192]);
            let extension = s(log, "address");
            let observed = fixture["instances"]
                .as_array()
                .unwrap()
                .iter()
                .find(|i| s(i, "address").eq_ignore_ascii_case(extension))
                .unwrap();
            assert_eq!(addr(p).to_lowercase(), s(observed, "quote").to_lowercase());
            let args = &s(observed, "constructorArguments")[2..];
            assert_eq!(
                U256::from_str(&format!("0x{}", &args[..64])).unwrap(),
                U256::from_str(s(&fixture["addresses"], "core")).unwrap()
            );
            assert_eq!(
                U256::from_str(&format!("0x{}", &args[64..])).unwrap(),
                word(p)
            );
            assert_eq!(word(4), word(p + 5));
            assert_eq!(format!("0x{}", &data[128..168]), extension.to_lowercase());
            assert_eq!(&data[168..184], "0000000000000000");
            let block = u64::from_str_radix(&s(log, "blockNumber")[2..], 16).unwrap();
            let snapshot = branch["states"]
                .as_array()
                .unwrap()
                .iter()
                .find(|s| s["blockNumber"].as_u64() == Some(block))
                .unwrap();
            let state_word = snapshot["pools"]
                .as_array()
                .unwrap()
                .iter()
                .find(|p| p["poolId"] == log["topics"][1])
                .unwrap();
            let core = indexer_state(s(state_word, "poolStateWord"));
            let is1 = addr(p).eq_ignore_ascii_case(&addr(0));
            let ask = signed(p + 6);
            let upper = signed(p + 7);
            let range = ZeroSeedLaunchRange {
                launch_token_is_token1: is1,
                ask_tick: ask,
                upper_tick: upper,
                tick_spacing: word(p + 8).try_into().unwrap(),
            };
            let (lower, upper_bound) = range.pool_bounds();
            assert_eq!(
                addr(0).to_lowercase(),
                fixture["launches"][s(state_word, "label")]["poolKey"]["token0"]
                    .as_str()
                    .unwrap()
                    .to_lowercase()
            );
            assert_eq!(
                emitted_key.to_lowercase(),
                fixture["launches"][s(state_word, "label")]["poolKey"]["config"]
                    .as_str()
                    .unwrap()
                    .to_lowercase()
            );
            scenarios.push(serde_json::json!({ "create": {
                "extension": extension, "constructorQuote": observed["quote"],
                "extensionCodehash": observed["runtimeKeccak"],
                "coreCodehash": fixture["provenance"]["coreRuntimeKeccak"],
                "quoteCodehash": if observed["scope"].as_str().unwrap().contains("synthetic") { "0x0" } else { s(&fixture["provenance"], "wethRuntimeKeccak") },
                "quoteDecimals": if observed["scope"].as_str().unwrap().contains("synthetic") { "6" } else { "18" },
                "token0": addr(0), "token1": addr(1),
                "token": format!("0x{}", &log["topics"][2].as_str().unwrap()[26..]),
                "fee": "0", "tickSpacing": range.tick_spacing.to_string(),
                "askTick": ask.to_string(), "upperTick": upper.to_string(),
                "tickLower": lower.to_string(), "tickUpper": upper_bound.to_string(),
                "liquidity": word(4).to_string(), "supply": word(p+4).to_string(),
                "tradingStart": word(p+9).to_string(), "feeDuration": word(p+10).to_string(),
                "initialFee": word(p+11).to_string(), "finalFee": word(p+12).to_string(),
                "decayFactor": word(p+13).to_string(),
                "state": { "sqrt_ratio": core.sqrt_ratio.to_string(), "tick": core.tick.to_string(), "liquidity": core.liquidity.to_string() },
                "branch": branch["blocks"][0]["parentHash"], "blockNumber": block,
                "poolStateWord": state_word["poolStateWord"], "poolId": log["topics"][1]
            }}));
        }
    }
    assert_eq!(scenarios.len(), 4);
    serde_json::json!({"scenarios": scenarios})
}

#[test]
fn supported_indexer_same_block_states() {
    let vectors = indexer_created_vectors();
    let fixture: Value = serde_json::from_str(INDEXER).unwrap();
    let mut checked = 0;
    for scenario in vectors["scenarios"].as_array().unwrap() {
        let created = &scenario["create"];
        if num::<u8>(created, "quoteDecimals") != 18 {
            continue;
        }
        let initial = state(&created["state"]);
        let pool = supported_pool_from_created(created, initial);
        assert_eq!(pool.state(), initial);
        for branch in fixture["branches"].as_object().unwrap().values() {
            for snapshot in branch["states"].as_array().unwrap() {
                for observed in snapshot["pools"].as_array().unwrap() {
                    if observed["poolId"] != created["poolId"] {
                        continue;
                    }
                    let recorded = indexer_state(s(observed, "poolStateWord"));
                    let candidate = supported_pool_from_created(created, recorded);
                    assert_eq!(candidate.state(), recorded);
                    assert_eq!(candidate.key(), pool.key());
                    checked += 1;
                }
            }
        }
        // The parity address and the other real extension are not aliases for this tuple.
        for extension in [
            "0x5100000000000000000000000000000000000000",
            if s(created, "constructorQuote") == QUOTE_HIGH {
                "0x51174b5db84c81a906ec55445070fd84c8c8e655"
            } else {
                "0x5142e167b32877ca3cf3060010a0a1418e3ef1b9"
            },
        ] {
            let mut bad = instance(created);
            bad.extension = address(extension);
            assert!(bad.validate().is_err());
        }
    }
    assert_eq!(checked, 19);
}

#[test]
fn supported_indexer_actual_trade_parity() {
    let vectors = indexer_created_vectors();
    let fixture: Value = serde_json::from_str(INDEXER).unwrap();
    let mut prefix_states = HashMap::new();
    let mut checked = 0;
    for branch_name in ["prefix", "alternate", "canonical"] {
        let branch = &fixture["branches"][branch_name];
        let mut states = prefix_states.clone();
        for block in branch["blocks"].as_array().unwrap() {
            let number = block["number"].as_u64().unwrap();
            let logs: Vec<_> = branch["logs"]
                .as_array()
                .unwrap()
                .iter()
                .filter(|l| u64::from_str_radix(&s(l, "blockNumber")[2..], 16).unwrap() == number)
                .collect();
            let mut swaps = logs.iter().filter(|l| {
                l["topics"][0].as_str()
                    == Some("0x3e58795f52a8e88efdec2da89ea3798175f8764145ccd7bf5e40633a7d571f6d")
            });
            for action in block["actions"].as_array().unwrap() {
                let action: Vec<_> = action.as_str().unwrap().split_whitespace().collect();
                if !["buy", "sell"].contains(&action[0]) {
                    continue;
                }
                let event = swaps.next().unwrap();
                if !["l1", "l3"].contains(&action[1]) {
                    continue;
                }
                let created = &vectors["scenarios"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .find(|s| s["create"]["poolId"] == fixture["launches"][action[1]]["poolId"])
                    .unwrap()["create"];
                let before = *states
                    .entry(action[1].to_owned())
                    .or_insert_with(|| state(&created["state"]));
                let pool = supported_pool_from_created(created, before);
                let launch = address(s(created, "token"));
                let quote = instance(created).constructor_quote;
                let token = match (action[0], action[2]) {
                    ("buy", "exact-in") | ("sell", "exact-out") => quote,
                    _ => launch,
                };
                let amount: i128 = action[3].parse().unwrap();
                let q = pool
                    .quote(QuoteParams {
                        token_amount: TokenAmount { token, amount },
                        sqrt_ratio_limit: None,
                        override_state: None,
                        meta: block["timestamp"].as_u64().unwrap(),
                    })
                    .unwrap();
                let core_log = logs.iter().find(|l| {
                    l["transactionHash"] == event["transactionHash"]
                        && l["topics"].as_array().unwrap().is_empty()
                        && s(l, "data").len() == 234
                });
                let recorded = if let Some(core_log) = core_log {
                    let data = &s(core_log, "data")[2..];
                    assert_eq!(format!("0x{}", &data[40..104]), s(created, "poolId"));
                    indexer_state(&format!("0x{}", &data[168..232]))
                } else {
                    before
                }; // No-bid zero fill emits no Core swap, but does emit LaunchSwapped.
                assert_eq!(q.state_after, recorded, "{branch_name} {number}");
                assert!(s(event, "address").eq_ignore_ascii_case(s(created, "extension")));
                let data = &s(event, "data")[2..];
                let word = |i: usize| {
                    U256::from_str(&format!("0x{}", &data[i * 64..(i + 1) * 64])).unwrap()
                };
                let signed = |i| {
                    let n: u128 = (word(i) & U256::from(u128::MAX)).try_into().unwrap();
                    n as i128
                };
                let specified_is1 = token == pool.key().token1;
                assert_eq!(signed(usize::from(specified_is1)), q.consumed_amount);
                let calculated = signed(usize::from(!specified_is1));
                assert_eq!(calculated.unsigned_abs(), q.calculated_amount);
                assert_eq!(word(3), U256::from(q.fees_paid));
                assert_eq!(word(4), U256::from(u8::from(!specified_is1)));
                states.insert(action[1].to_owned(), q.state_after);
                checked += 1;
            }
        }
        if branch_name == "prefix" {
            prefix_states = states;
        }
    }
    assert_eq!(checked, 12);
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
    assert_eq!(scenarios.len(), 9);
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
                assert_eq!(
                    step["pre_balances"], step["post_balances"],
                    "{label}: rollback conservation"
                );
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
                        let token_allowance = U256::from_str(s(step, "token_allowance")).unwrap();
                        let held_quote = U256::from_str(s(step, "held_quote")).unwrap();
                        let core_quote = U256::from_str(s(step, "core_quote")).unwrap();
                        assert!(
                            (token_owed > 0 && token_owed as u128 > held_token)
                                || (token_owed > 0
                                    && U256::from(token_owed as u128) > token_allowance)
                                || (quote_owed > 0 && U256::from(quote_owed as u128) > held_quote)
                                || (quote_owed < 0
                                    && U256::from(quote_owed.unsigned_abs()) > core_quote),
                            "{label}: owes {token_owed}/{quote_owed}, holds {held_token}/{held_quote}"
                        );
                    }
                    other => panic!("{label}: unexpected revert {other}"),
                }
                refused += 1;
                continue;
            }

            let swap = result.unwrap_or_else(|e| panic!("{label}: {e}"));
            for (i, delta) in [swap.delta0, swap.delta1].into_iter().enumerate() {
                let pre =
                    |k: usize| U256::from_str(step["pre_balances"][k].as_str().unwrap()).unwrap();
                let post =
                    |k: usize| U256::from_str(step["post_balances"][k].as_str().unwrap()).unwrap();
                let amount = U256::from(delta.unsigned_abs());
                let expected_core = if delta >= 0 {
                    pre(i).checked_add(amount)
                } else {
                    pre(i).checked_sub(amount)
                }
                .unwrap();
                let expected_holder = if delta >= 0 {
                    pre(i + 2).checked_sub(amount)
                } else {
                    pre(i + 2).checked_add(amount)
                }
                .unwrap();
                assert_eq!(post(i), expected_core, "{label}: Core balance delta");
                assert_eq!(
                    post(i + 2),
                    expected_holder,
                    "{label}: holder balance delta"
                );
                assert_eq!(
                    pre(i).checked_add(pre(i + 2)),
                    post(i).checked_add(post(i + 2)),
                    "{label}: asset conservation"
                );
            }
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
    assert_eq!(claims, 8);
    assert_eq!(compared + refused, 407);
    assert!(compared >= 240, "compared {compared}");

    // Gas: the uncalibrated estimate stays within 40% of the measured in-test gas for every fill except
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
    assert_eq!(cold, 16);
    println!("parity: {compared} executed, {refused} refused, {claims} claims; gas worst={worst}");
    assert!(worst < 0.40, "worst gas estimate error {worst}");
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
        let result = preview_installation_math(&parameters, now);
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
            let error = decode_error(s(preview, "err"));
            if error == ZeroSeedLaunchParameterError::UnsupportedQuoteToken {
                // Pure math intentionally has no constructor/address support policy. The emitted
                // contract refusal is independently asserted: it mismatches BOTH manifest quotes.
                assert!(
                    ![address(QUOTE_HIGH), address(QUOTE_LOW)].contains(&parameters.quote_token)
                );
            } else {
                assert_eq!(result, Err(error), "{label}");
            }
        }
        by_label.insert(label.to_owned(), parameters);
    }
    assert_eq!(previews.len(), 120);
    assert_eq!(ok, 44);

    let bindings = vectors["bindings"].as_array().unwrap();
    assert_eq!(bindings.len(), 4 * ok);
    for binding in bindings {
        let label = s(binding, "label");
        let mut parameters = by_label[label];
        parameters.supply = num(binding, "supply");
        let liquidity: u128 = num(binding, "liquidity");
        // Creation happens in the block after the preview's timestamp in the generator, at the
        // same timestamp.
        let result = check_launch_binding_math(&parameters, liquidity, 1);
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
    let first = preview_installation_math(frozen, 1).unwrap();
    let mut again = *frozen;
    again.supply = first.installed_supply;
    let second = preview_installation_math(&again, 1).unwrap();
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
        decay_factor: num(&fixture["fee_decay_factors_q64"], &duration.to_string()),
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
        let installation = preview_installation_math(&parameters, 1).unwrap();
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
        let pool = EvmZeroSeedLaunchPool::new_math(
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

    // Upper residue is not Core's accumulated unowned dust. Preserve per-asset raw units.
    let residues = vectors["residue_metrics"]["scenarios"].as_array().unwrap();
    assert_eq!(residues.len(), 4);
    for (entry, expected) in residues.iter().zip([89u128, 89, 94, 90]) {
        let residue: u128 = num(entry, "upper_residue_raw_token");
        assert_eq!(residue, expected);
        assert_eq!(
            num::<u128>(entry, "position_token_before_exhaust")
                - num::<u128>(entry, "delivered_raw_token"),
            residue
        );
        let before = &entry["core_dust_before_exhaust"];
        let after = &entry["core_dust_after_exhaust"];
        assert_eq!(
            num::<u128>(after, "raw_token"),
            num::<u128>(before, "raw_token") + residue
        );
        assert!(num::<u128>(after, "raw_quote") >= num::<u128>(before, "raw_quote"));
    }

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
    let vectors = indexer_created_vectors();
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
    let launch = *supported_pool_from_created(created, state(&created["state"])).launch();
    let core = state(&created["state"]);
    let mut observed = instance(created);
    observed.extension_runtime = U256::ZERO;
    assert!(EvmZeroSeedLaunchPool::new(key, launch, core, &observed).is_err());
    observed = instance(created);
    observed.constructor_quote = if key.token0 == observed.constructor_quote {
        key.token1
    } else {
        key.token0
    };
    assert!(EvmZeroSeedLaunchPool::new(key, launch, core, &observed).is_err());
    key.config.fee = 1;
    assert_eq!(
        EvmZeroSeedLaunchPool::new(key, launch, core, &instance(created)),
        Err(ZeroSeedLaunchPoolConstructionError::FeeMustBeZero)
    );
}

#[test]
fn manifest_and_local_producer_negative_controls() {
    let vectors = indexer_created_vectors();
    for scenario in vectors["scenarios"].as_array().unwrap() {
        let created = &scenario["create"];
        let observed = instance(created);
        if num::<u8>(created, "quoteDecimals") == 6 {
            assert_eq!(
                observed.validate(),
                Err(ZeroSeedLaunchParameterError::UnsupportedInstance)
            );
            let (key, config) = pool_inputs_from_created(created);
            assert!(
                EvmZeroSeedLaunchPool::new(key, config, state(&created["state"]), &observed)
                    .is_err()
            );
            continue;
        }
        observed.validate().unwrap();
        let pool = supported_pool_from_created(created, state(&created["state"]));
        let key = pool.key();
        let mut wrong_key = key;
        wrong_key.config.extension = Address::ZERO;
        assert!(
            EvmZeroSeedLaunchPool::new(wrong_key, *pool.launch(), pool.state(), &observed).is_err()
        );
        let mut wrong_key = key;
        if wrong_key.token0 == observed.constructor_quote {
            wrong_key.token0 = Address::ZERO;
        } else {
            wrong_key.token1 = address("0xfffffffffffffffffffffffffffffffffffffffe");
        }
        assert!(
            EvmZeroSeedLaunchPool::new(wrong_key, *pool.launch(), pool.state(), &observed).is_err()
        );
        for (ask, upper) in [(i32::MIN, 0), (0, i32::MAX), (0, i32::MIN)] {
            let mut invalid = *pool.launch();
            invalid.range.ask_tick = ask;
            invalid.range.upper_tick = upper;
            assert_eq!(
                EvmZeroSeedLaunchPool::new(key, invalid, pool.state(), &observed),
                Err(ZeroSeedLaunchPoolConstructionError::InvalidLaunchConfig)
            );
        }
        // Each provenance component is essential, not merely an arbitrary caller allowlist.
        for i in 0..8 {
            let mut bad = observed;
            match i {
                0 => bad.chain_id = 8453,
                1 => bad.extension = Address::ZERO,
                2 => bad.core = Address::ZERO,
                3 => bad.constructor_quote = Address::ZERO,
                4 => bad.quote_token_getter = Address::ZERO,
                5 => bad.extension_runtime = U256::ZERO,
                6 => bad.core_runtime = U256::ZERO,
                _ => bad.quote_runtime = U256::ZERO,
            }
            assert!(bad.validate().is_err());
            assert!(EvmZeroSeedLaunchPool::new(key, *pool.launch(), pool.state(), &bad).is_err());
        }
        let mut bad = observed;
        bad.extension_runtime =
            U256::from_str("0x4d44a77f7e4fcc5f7a321475c1dbfd1e0812ebbe8fc46a5e1973373fb6a9bf87")
                .unwrap();
        assert!(
            bad.validate().is_err(),
            "zero-filled template is not executed provenance"
        );
        for sink in [
            Address::ZERO,
            observed.core,
            observed.extension,
            key.token0,
            key.token1,
        ] {
            assert_eq!(
                validate_claim_recipient(&observed, &key, sink),
                Err(ZeroSeedLaunchParameterError::InvalidRecipient)
            );
        }
        validate_claim_recipient(
            &observed,
            &key,
            address("0x0000000000000000000000000000000000000001"),
        )
        .unwrap();

        let mut parameters = ZeroSeedLaunchParameters {
            quote_token: observed.constructor_quote,
            supply: num(created, "supply"),
            range: pool.launch().range,
            fee: pool.launch().fee,
        };
        parameters.fee.trading_start = 301;
        let mut context = ZeroSeedLaunchLocalPreview {
            instance: &observed,
            name: "éééééééééééééééa",
            symbol: "ZERO",
            predicted_token_has_code: false,
            build_time: 1,
            execution_expiry: 301,
        };
        assert_eq!(context.name.len(), 31);
        let preview = preview_installation(&parameters, 1, &context).unwrap();
        let requested = parameters.supply;
        parameters.supply = preview.installed_supply;
        assert!(parameters.supply <= requested);
        check_launch_binding(&parameters, preview.liquidity, 1, &context).unwrap();
        assert!(check_launch_binding(&parameters, preview.liquidity + 1, 1, &context).is_err());

        context.name = "éééééééééééééééé"; // 16 characters, 32 bytes.
        assert_eq!(
            preview_installation(&parameters, 1, &context),
            Err(ZeroSeedLaunchParameterError::MetadataTooLong)
        );
        context.name = "ZERO";
        context.symbol = "éééééééééééééééé";
        assert_eq!(
            context.validate(&parameters, 1),
            Err(ZeroSeedLaunchParameterError::MetadataTooLong)
        );
        context.symbol = "";
        context.predicted_token_has_code = true;
        assert_eq!(
            context.validate(&parameters, 1),
            Err(ZeroSeedLaunchParameterError::LaunchTokenExists)
        );
        context.predicted_token_has_code = false;
        for start in [1, 300, 86402] {
            parameters.fee.trading_start = start;
            assert_eq!(
                context.validate(&parameters, 1),
                Err(ZeroSeedLaunchParameterError::InvalidLocalTiming)
            );
        }
        for start in [301, 86401] {
            parameters.fee.trading_start = start;
            context.execution_expiry = start;
            context.validate(&parameters, 1).unwrap();
            for expiry in [0, 1, start + 1] {
                context.execution_expiry = expiry;
                assert!(context.validate(&parameters, 1).is_err());
            }
        }
        parameters.fee.trading_start = 301;
        context.execution_expiry = 301;
        assert!(context.validate(&parameters, 0).is_err(), "future build");
        assert!(
            context.validate(&parameters, 2).is_err(),
            "fresh margin must remain"
        );
        assert!(
            context.validate(&parameters, 301).is_err(),
            "expired at equality"
        );
        parameters.fee.trading_start = 86401;
        context.execution_expiry = 2;
        assert!(
            context.validate(&parameters, 2).is_err(),
            "expiry with ample start margin"
        );
        context.build_time = u64::MAX - 299;
        context.execution_expiry = u64::MAX;
        assert_eq!(
            context.validate(&parameters, context.build_time),
            Err(ZeroSeedLaunchParameterError::Overflow)
        );
        context.build_time = 1;
        assert_eq!(
            context.validate(&parameters, u64::MAX),
            Err(ZeroSeedLaunchParameterError::Overflow)
        );
        parameters.quote_token = Address::ZERO;
        assert_eq!(
            context.validate(&parameters, 1),
            Err(ZeroSeedLaunchParameterError::UnsupportedQuoteToken)
        );
    }
}
