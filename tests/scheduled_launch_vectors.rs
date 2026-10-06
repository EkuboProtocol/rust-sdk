//! Reproduces every case of the `ScheduledLaunch` swap conformance vectors, see `tests/vectors`.
#![cfg(any(feature = "evm-alloy-0_6", feature = "evm-alloy-1"))]

use core::str::FromStr;

use ekubo_sdk::{
    U256,
    alloy_primitives::{Address, B256, ruint::Uint},
    chain::evm::{
        EvmPoolConfig, EvmPoolTypeConfig, EvmScheduledLaunchConfig, EvmScheduledLaunchPool,
        EvmScheduledLaunchPoolKey, EvmScheduledLaunchPoolState,
        fixed_sqrt_ratio_to_contract_sqrt_ratio, float_sqrt_ratio_to_fixed,
    },
    quoting::types::{Pool, PoolConfig, PoolKey, QuoteParams, TokenAmount},
};
use serde_json::Value;

const VECTORS: &str = include_str!("vectors/scheduled-launch-swaps.json");
const CASE_COUNT: usize = 23;

fn string<'a>(value: &'a Value, field: &str) -> &'a str {
    value[field]
        .as_str()
        .unwrap_or_else(|| panic!("{field} is not a string"))
}

fn u128_field(value: &Value, field: &str) -> u128 {
    string(value, field).parse().unwrap()
}

fn i128_field(value: &Value, field: &str) -> i128 {
    string(value, field).parse().unwrap()
}

fn i32_field(value: &Value, field: &str) -> i32 {
    value[field].as_i64().unwrap().try_into().unwrap()
}

fn u64_field(value: &Value, field: &str) -> u64 {
    value[field]
        .as_u64()
        .unwrap_or_else(|| string(value, field).parse().unwrap())
}

fn bool_field(value: &Value, field: &str) -> bool {
    value[field].as_bool().unwrap()
}

/// Converts a contract `SqrtRatio` into the SDK's fixed point representation.
fn fixed_sqrt_ratio(value: &Value, field: &str) -> U256 {
    float_sqrt_ratio_to_fixed(Uint::<96, 2>::from_str(string(value, field)).unwrap())
}

fn state(value: &Value) -> EvmScheduledLaunchPoolState {
    EvmScheduledLaunchPoolState {
        deployed: u128_field(value, "deployed"),
        reserve0: u128_field(value, "reserve0"),
        reserve1: u128_field(value, "reserve1"),
        sqrt_ratio: fixed_sqrt_ratio(value, "sqrtRatio"),
        tick: i32_field(value, "tick"),
        liquidity: u128_field(value, "liquidity"),
        position_liquidity: u128_field(value, "positionLiquidity"),
    }
}

fn pool(config: &Value, pre: &Value) -> EvmScheduledLaunchPool {
    let pool_config =
        EvmPoolConfig::try_from(B256::from_str(string(config, "poolConfig")).unwrap()).unwrap();
    let EvmPoolTypeConfig::Concentrated(tick_spacing) = pool_config.pool_type_config else {
        panic!("launch pools are concentrated");
    };
    assert_eq!(tick_spacing.0, u64_field(config, "tickSpacing") as u32);

    let key = EvmScheduledLaunchPoolKey {
        token0: Address::from_str(string(config, "token0")).unwrap(),
        token1: Address::from_str(string(config, "token1")).unwrap(),
        config: PoolConfig {
            extension: pool_config.extension,
            fee: pool_config.fee,
            pool_type_config: tick_spacing,
        },
    };
    let launch = EvmScheduledLaunchConfig {
        launch_token_is_token1: !bool_field(config, "launchTokenIs0"),
        total_supply: u128_field(config, "totalSupply"),
        start_time: u64_field(config, "startTime"),
        end_time: u64_field(config, "endTime"),
        target_tick: i32_field(config, "targetTick"),
        upper_tick: i32_field(config, "upperTick"),
        initial_fee: u64_field(config, "initialFee"),
        final_fee: u64_field(config, "finalFee"),
    };

    let pool = EvmScheduledLaunchPool::new(key, launch, state(pre)).unwrap();
    assert_eq!(pool.pool_target_tick(), i32_field(config, "poolTargetTick"));
    assert_eq!(
        pool.position_bounds(),
        (
            i32_field(config, "positionTickLower"),
            i32_field(config, "positionTickUpper")
        )
    );
    pool
}

/// Runs one case and returns a description of every field that does not match.
fn run_case(case: &Value) -> Vec<String> {
    let (config, params, result, post) = (
        &case["config"],
        &case["params"],
        &case["result"],
        &case["post"],
    );
    let pool = pool(config, &case["pre"]);
    let PoolKey { token0, token1, .. } = pool.key();

    let is_token1 = bool_field(params, "isToken1");
    let amount = i128_field(params, "amount");
    let sqrt_ratio_limit = match string(params, "sqrtRatioLimit") {
        "0" => None,
        _ => Some(fixed_sqrt_ratio(params, "sqrtRatioLimit")),
    };
    assert_eq!(
        params["skipAhead"].as_u64(),
        Some(0),
        "the model quotes skipAhead 0"
    );

    let quote = pool
        .quote(QuoteParams {
            token_amount: TokenAmount {
                token: if is_token1 { token1 } else { token0 },
                amount,
            },
            sqrt_ratio_limit,
            override_state: None,
            meta: u64_field(case, "timestamp"),
        })
        .unwrap();

    // The fee-inclusive pool balance update the extension returns: the calculated side is paid
    // in for exact output and paid out for exact input.
    let calculated = i128::try_from(quote.calculated_amount).unwrap();
    let calculated = if amount < 0 { calculated } else { -calculated };
    let (delta0, delta1) = if is_token1 {
        (calculated, quote.consumed_amount)
    } else {
        (quote.consumed_amount, calculated)
    };

    let after = quote.state_after;
    let actual = [
        ("result.delta0", delta0.to_string()),
        ("result.delta1", delta1.to_string()),
        ("result.feeAmount", quote.fees_paid.to_string()),
        ("result.feeIsToken1", (!is_token1).to_string()),
        ("post.deployed", after.deployed.to_string()),
        ("post.reserve0", after.reserve0.to_string()),
        ("post.reserve1", after.reserve1.to_string()),
        (
            "post.sqrtRatio",
            fixed_sqrt_ratio_to_contract_sqrt_ratio(after.sqrt_ratio).to_string(),
        ),
        ("post.tick", after.tick.to_string()),
        ("post.liquidity", after.liquidity.to_string()),
        (
            "post.positionLiquidity",
            after.position_liquidity.to_string(),
        ),
    ];

    actual
        .into_iter()
        .filter_map(|(path, actual)| {
            let (section, field) = path.split_once('.').unwrap();
            let section = if section == "result" { result } else { post };
            let expected = match &section[field] {
                Value::String(s) => s.clone(),
                other => other.to_string(),
            };
            (expected != actual).then(|| format!("{path}: expected {expected}, got {actual}"))
        })
        .collect()
}

#[test]
fn reproduces_every_scheduled_launch_swap_vector() {
    let vectors: Value = serde_json::from_str(VECTORS).unwrap();
    let cases = vectors["cases"].as_array().unwrap();
    assert_eq!(cases.len(), CASE_COUNT);

    let mut failures = Vec::new();
    for case in cases {
        let name = string(case, "name");
        let mismatches = run_case(case);
        if mismatches.is_empty() {
            println!("ok   {name}");
        } else {
            println!("FAIL {name}");
            for mismatch in &mismatches {
                println!("       {mismatch}");
            }
            failures.push(name);
        }
    }

    assert!(
        failures.is_empty(),
        "{} of {CASE_COUNT} vectors mismatch: {failures:?}",
        failures.len()
    );
}
