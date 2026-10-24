//! The tick-rate fee model (`evm-contracts@3d6378f`, `uint64 decayRateX32`) against the contract's
//! frozen vectors `tests/vectors/v2/zero-seed-launch.json` (version 7, sha256 `4c1245ca…66605`):
//! every `fee` row, the `fee_curve` tables, tick steps, saturation seconds and the five SHA-256
//! chains its Solidity tests and independent Python oracle pin, and the `creator_fee_range`
//! verdicts. The fixed-base model is checked unchanged by `zero_seed_launch_vectors.rs`.
#![cfg(any(feature = "evm-alloy-0_6", feature = "evm-alloy-1"))]

use core::str::FromStr;

use ekubo_sdk::{
    U256,
    quoting::pools::zero_seed_launch::{
        ZERO_SEED_LAUNCH_DEFAULT_DECAY_RATE_X32, ZERO_SEED_LAUNCH_HALF_LIFE_X32_E30,
        ZERO_SEED_LAUNCH_MAX_DECAY_PRODUCT, ZERO_SEED_LAUNCH_MAX_TICK_MAGNITUDE,
        ZeroSeedLaunchFeeDecay, ZeroSeedLaunchFeeModel, ZeroSeedLaunchFeeSchedule,
        ZeroSeedLaunchParameterError, ZeroSeedLaunchParameters, ZeroSeedLaunchRange,
        decay_rate_x32_for_half_life, half_life_micros, preview_installation_math,
        saturation_elapsed_seconds, tick_rate_decayed_fee, tick_rate_factor_q128,
    },
};
use serde_json::Value;
use sha2::{Digest, Sha256};

const FROZEN_V2: &str = include_str!("vectors/v2/zero-seed-launch.json");
const START: u64 = 1_000;

fn frozen() -> Value {
    serde_json::from_str(FROZEN_V2).unwrap()
}

fn s<'a>(v: &'a Value, key: &str) -> &'a str {
    v[key]
        .as_str()
        .unwrap_or_else(|| panic!("{key} is not a string in {v}"))
}

fn u64_of(v: &Value, key: &str) -> u64 {
    u64::from_str(s(v, key)).unwrap()
}

fn schedule(initial_fee: u64, final_fee: u64, decay_rate_x32: u64) -> ZeroSeedLaunchFeeSchedule {
    ZeroSeedLaunchFeeSchedule {
        trading_start: START,
        decay: ZeroSeedLaunchFeeDecay::TickRate { decay_rate_x32 },
        initial_fee,
        final_fee,
    }
}

/// The fee `t` seconds after the start. Elapsed seconds beyond `u64` cannot be a block timestamp
/// difference here; every positive rate saturates long before, so they take `u64::MAX - START`.
fn fee_at_elapsed(fee: &ZeroSeedLaunchFeeSchedule, t: &str) -> u64 {
    if let Some(before) = t.strip_prefix('-') {
        return fee.fee_at(START - u64::from_str(before).unwrap());
    }
    let elapsed = U256::from_str(t).unwrap();
    let max = U256::from(u64::MAX - START);
    fee.fee_at(START + elapsed.min(max).to::<u64>())
}

#[test]
fn constants_match_the_contract() {
    let v = frozen();
    assert_eq!(v["version"].as_u64(), Some(7));
    assert_eq!(ZERO_SEED_LAUNCH_MAX_TICK_MAGNITUDE, 88_722_835);
    assert_eq!(ZERO_SEED_LAUNCH_MAX_DECAY_PRODUCT, 381_061_679_028_371_455);
    assert_eq!(
        ZERO_SEED_LAUNCH_DEFAULT_DECAY_RATE_X32,
        u64_of(&v["fixture"], "fee_decay_rate_x32_default")
    );
    // The helper's range: the last magnitude is supported, one more is InvalidTick.
    assert_eq!(tick_rate_factor_q128(0), Some(U256::from(1) << 128));
    assert_eq!(
        tick_rate_factor_q128(ZERO_SEED_LAUNCH_MAX_TICK_MAGNITUDE),
        Some(U256::from(18_447_191_164_202_170_524_u128))
    );
    assert_eq!(
        tick_rate_factor_q128(ZERO_SEED_LAUNCH_MAX_TICK_MAGNITUDE + 1),
        None
    );
    assert_eq!(
        tick_rate_decayed_fee(u64::MAX, 0, 1, ZERO_SEED_LAUNCH_MAX_DECAY_PRODUCT),
        1
    );
    assert_eq!(
        tick_rate_decayed_fee(u64::MAX, 0, 1, ZERO_SEED_LAUNCH_MAX_DECAY_PRODUCT + 1),
        0
    );
}

#[test]
fn fee_rows() {
    let v = frozen();
    let fx = &v["fixture"];
    let (initial, final_fee) = (u64_of(fx, "fee_initial_q64"), u64_of(fx, "fee_final_q64"));
    let rows = v["fee"].as_array().unwrap();
    assert_eq!(rows.len(), 40);
    for row in rows {
        let rate = u64_of(row, "decayRateX32");
        let fee = schedule(initial, final_fee, rate);
        let t = s(row, "t_minus_start");
        assert_eq!(fee_at_elapsed(&fee, t), u64_of(row, "fee_q64"), "{row}");
        if let Some(m) = row["tick_magnitude"].as_str() {
            let product = U256::from(rate) * U256::from_str(t).unwrap();
            assert_eq!(product >> 32, U256::from_str(m).unwrap(), "{row}");
        }
    }
}

#[test]
fn fee_curve_tables_and_tick_steps() {
    let v = frozen();
    let curve = &v["fee_curve"];
    let rates = &curve["rates_q64"];
    let decay = &curve["decay_rates_x32"];
    let final_03 = u64_of(curve, "final_fee_q64");
    let default = u64_of(decay, "default_one_day");
    let two = u64_of(decay, "two_ticks_per_second");
    let tables = [
        (
            "default_one_day_50_to_0.3",
            u64_of(rates, "50"),
            final_03,
            default,
        ),
        (
            "two_ticks_per_second_50_to_0.3",
            u64_of(rates, "50"),
            final_03,
            two,
        ),
        (
            "two_ticks_per_second_99.9_to_0",
            u64_of(rates, "99.9"),
            0,
            two,
        ),
        ("default_one_day_max_to_0", u64::MAX, 0, default),
        ("min_rate_max_to_0", u64::MAX, 0, 1),
    ];
    let object = curve["tables"].as_object().unwrap();
    assert_eq!(object.len(), tables.len());
    let mut checked = 0;
    for (name, initial, final_fee, rate) in tables {
        let fee = schedule(initial, final_fee, rate);
        for row in object[name].as_array().unwrap() {
            assert_eq!(
                fee_at_elapsed(&fee, s(row, "t")),
                u64_of(row, "fee_q64"),
                "{name} {row}"
            );
            checked += 1;
        }
    }
    for steps in curve["tick_steps"].as_array().unwrap() {
        let rate = u64_of(steps, "decayRateX32");
        let rows = steps["rows"].as_array().unwrap();
        // A one-unit excess over 0.3% starts one raw unit above the floor.
        let initial = if u64_of(&rows[0], "fee_q64") == final_03 + 1 {
            final_03 + 1
        } else {
            u64_of(rates, "50")
        };
        let fee = schedule(initial, final_03, rate);
        for row in rows {
            let t = s(row, "t");
            assert_eq!(fee_at_elapsed(&fee, t), u64_of(row, "fee_q64"), "{row}");
            if let Some(m) = row["tick_magnitude"].as_str() {
                let magnitude = (u128::from(rate) * u128::from_str(t).unwrap()) >> 32;
                assert_eq!(magnitude.to_string(), m, "{row}");
            }
            checked += 1;
        }
    }
    assert!(checked > 40, "{checked}");
}

#[test]
fn saturation_seconds() {
    let v = frozen();
    let curve = &v["fee_curve"];
    let decay = curve["decay_rates_x32"].as_object().unwrap();
    for (name, second) in curve["saturation_second"].as_object().unwrap() {
        let rate = u64::from_str(decay[name].as_str().unwrap()).unwrap();
        let second = u64::from_str(second.as_str().unwrap()).unwrap();
        assert_eq!(saturation_elapsed_seconds(rate), Some(second), "{name}");
        // The last evaluated second can still be above the floor for a full-span excess; the
        // next one is the floor exactly.
        assert_eq!(
            tick_rate_decayed_fee(u64::MAX, 0, rate, second + 1),
            0,
            "{name}"
        );
        assert_eq!(
            tick_rate_decayed_fee(u64::MAX, 7, rate, u64::MAX),
            7,
            "{name}"
        );
    }
    assert_eq!(saturation_elapsed_seconds(0), None);
}

/// `h = sha256(h || fee as 8-byte big-endian)` over `t = 0, step, ..., last`, from the empty
/// state; the contract's tests and the independent Python oracle pin the same digests.
#[test]
fn digest_chains() {
    let v = frozen();
    let chains = v["fee_curve"]["digests_sha256"].as_array().unwrap();
    assert_eq!(chains.len(), 5);
    for chain in chains {
        let fee = schedule(
            u64_of(chain, "initialFee"),
            u64_of(chain, "finalFee"),
            u64_of(chain, "decayRateX32"),
        );
        let (last, step) = (
            chain["last"].as_u64().unwrap(),
            chain["step"].as_u64().unwrap(),
        );
        let mut h = [0u8; 32];
        let mut t = 0;
        while t <= last {
            let mut hasher = Sha256::new();
            hasher.update(h);
            hasher.update(fee.fee_at(START + t).to_be_bytes());
            h = hasher.finalize().into();
            t += step;
        }
        let hex: String = h.iter().map(|b| format!("{b:02x}")).collect();
        assert_eq!(hex, s(chain, "digest"), "{}", s(chain, "label"));
    }
}

/// Monotone and bounded for every rate class: never above the initial fee or below the floor,
/// never rising with time, never faster at a lower rate.
#[test]
fn bounded_and_monotone() {
    let rates = [
        0,
        1,
        429_496_729,
        1_073_741_824,
        ZERO_SEED_LAUNCH_DEFAULT_DECAY_RATE_X32,
        9_923_486_534_471,
        u64::MAX,
    ];
    let pairs = [
        (u64::MAX, 0),
        (9_223_372_036_854_775_808, 55_340_232_221_128_654),
        (55_340_232_221_128_655, 55_340_232_221_128_654),
        (7, 7),
        (0, 0),
    ];
    let times = (0..2_000u64)
        .chain((0..64).map(|i| 1u64 << i))
        .chain([5_529_596, 5_529_597, 5_529_598, 38_399, 38_400]);
    let mut times: Vec<u64> = times.collect();
    times.sort_unstable();
    for (initial, final_fee) in pairs {
        let mut slower: Option<Vec<u64>> = None;
        for rate in rates {
            let curve: Vec<u64> = times
                .iter()
                .map(|&t| tick_rate_decayed_fee(initial, final_fee, rate, t))
                .collect();
            for (i, fee) in curve.iter().enumerate() {
                assert!(final_fee <= *fee && *fee <= initial);
                if i > 0 {
                    assert!(*fee <= curve[i - 1]);
                }
                if let Some(previous) = &slower {
                    assert!(*fee <= previous[i]);
                }
            }
            if rate == 0 {
                assert!(curve.iter().all(|fee| *fee == initial));
            }
            slower = Some(curve);
        }
    }
}

#[test]
fn half_life_conversion() {
    let v = frozen();
    assert_eq!(
        decay_rate_x32_for_half_life(86_400),
        Some(ZERO_SEED_LAUNCH_DEFAULT_DECAY_RATE_X32)
    );
    let fx_rates = v["fixture"]["fee_decay_rates_x32"].as_array().unwrap();
    assert_eq!(
        decay_rate_x32_for_half_life(600).unwrap().to_string(),
        fx_rates[1].as_str().unwrap()
    );
    for (seconds, rate) in [
        (1, 5_954_091_920_683_119),
        (3_600, 1_653_914_422_411),
        (604_800, 9_844_728_704),
    ] {
        assert_eq!(decay_rate_x32_for_half_life(seconds), Some(rate));
    }
    assert_eq!(decay_rate_x32_for_half_life(0), None);
    assert_eq!(decay_rate_x32_for_half_life(u64::MAX), Some(0));
    for (rate, micros) in [
        (68_913_100_933, 86_400_000_001),
        (9_923_486_534_471, 600_000_000),
        (8_589_934_592, 693_147_527_133),
        (1_073_741_824, 5_545_180_217_067),
        (u64::MAX, 322),
    ] {
        assert_eq!(half_life_micros(rate), Some(micros), "{rate}");
    }
    assert_eq!(half_life_micros(1), Some(5_954_091_920_683_119_788_732));
    assert_eq!(half_life_micros(0), None);
    // One day of half-life, in the excess: about 25.15% for 50% -> 0.3%.
    let consumer = &v["creator_fee_range"]["reference_schedules"]["consumer_default"];
    let fee = schedule(
        u64_of(consumer, "initialFee"),
        u64_of(consumer, "finalFee"),
        u64_of(consumer, "decayRateX32"),
    );
    assert_eq!(
        fee.fee_at(START + 86_400),
        u64_of(consumer, "fee_after_one_day_q64")
    );
    assert_eq!(ZERO_SEED_LAUNCH_HALF_LIFE_X32_E30.len(), 46);
}

#[test]
fn creator_fee_range_verdicts() {
    let v = frozen();
    let range = ZeroSeedLaunchRange {
        launch_token_is_token1: false,
        ask_tick: -13_815_500,
        upper_tick: -9_210_300,
        tick_spacing: 100,
    };
    let vectors = v["creator_fee_range"]["vectors"].as_array().unwrap();
    assert_eq!(vectors.len(), 13);
    for vector in vectors {
        let parsed = (
            u64::from_str(s(vector, "initialFee")),
            u64::from_str(s(vector, "finalFee")),
            u64::from_str(s(vector, "decayRateX32")),
        );
        let verdict = s(vector, "verdict");
        if verdict == "abi_decoding_failure" {
            assert!(parsed.0.is_err() || parsed.1.is_err() || parsed.2.is_err());
            #[cfg(feature = "serde")]
            assert!(
                serde_json::from_str::<ZeroSeedLaunchFeeSchedule>(&format!(
                    r#"{{"trading_start":1000,"model":"tick_rate_v2","decay_rate_x32":{},"initial_fee":{},"final_fee":{}}}"#,
                    s(vector, "decayRateX32"),
                    s(vector, "initialFee"),
                    s(vector, "finalFee"),
                ))
                .is_err()
            );
            continue;
        }
        let fee = schedule(parsed.0.unwrap(), parsed.1.unwrap(), parsed.2.unwrap());
        #[cfg(feature = "serde")]
        assert_eq!(
            serde_json::from_str::<ZeroSeedLaunchFeeSchedule>(&format!(
                r#"{{"trading_start":1000,"model":"tick_rate_v2","decay_rate_x32":{},"initial_fee":{},"final_fee":{}}}"#,
                fee.decay_rate_x32().unwrap(),
                fee.initial_fee,
                fee.final_fee
            ))
            .unwrap(),
            fee
        );
        let parameters = ZeroSeedLaunchParameters {
            supply: 1_000_000_000_000_000_000_000_000_000,
            quote_token: Default::default(),
            range,
            fee,
        };
        let result = preview_installation_math(&parameters, START).map(|_| ());
        match verdict {
            "accept" => assert_eq!(result, Ok(()), "{vector}"),
            "InvalidFeeSchedule" => assert_eq!(
                result,
                Err(ZeroSeedLaunchParameterError::InvalidFeeSchedule),
                "{vector}"
            ),
            other => panic!("unknown verdict {other}"),
        }
    }
    assert_eq!(
        schedule(1, 0, 0).decay.model(),
        ZeroSeedLaunchFeeModel::TickRateV2
    );
}

// ---------------------------------------------------------------------------------------------
// Execution parity against the frozen tick-rate contracts: every value below was read from local
// Core, extension, periphery and token state or emitted events of `evm-contracts@3d6378f`
// (`ZeroSeedLaunchSdkParityV2.t.sol`), never recomputed.
// ---------------------------------------------------------------------------------------------

const PARITY_V2: &str = include_str!("vectors/v2/zero-seed-launch-parity.json");
const CORE_RUNTIME: &str = "0xc5f90c9d0dbc5037f8f9e248f4bb292e7c1824f584eb6550cb4cad525b38c71a";
/// Runtime keccak of the frozen extension and periphery (consumer ABI freeze, section 4).
const EXTENSION_RUNTIME_V2: &str =
    "0xe08ad382497fc9825956c2b4e9ccf463014c4ed65baf50c0a59db8d7b7aedfc3";
const PERIPHERY_RUNTIME_V2: &str =
    "0xfa8ef7dfd8f5f7454366b471449f8a771f1cef34c764022c971e9394a05f0444";
const TRANSFER_FROM_FAILED: &str = "0x7939f424";
const TRADING_NOT_STARTED: &str = "0xacf75be8";
const SQRT_RATIO_LIMIT_WRONG_DIRECTION: &str = "0xa574a6b4";
const SAFE_CAST_OVERFLOW: &str = "0x35278d12";

use ekubo_sdk::{
    alloy_primitives::{Address, B256},
    chain::evm::{EvmZeroSeedLaunchPool, EvmZeroSeedLaunchPoolKey},
    quoting::{
        pools::{
            concentrated::TickSpacing,
            zero_seed_launch::{
                ZeroSeedLaunchConfig, ZeroSeedLaunchInstance, ZeroSeedLaunchLocalPreview,
                ZeroSeedLaunchPoolConstructionError, ZeroSeedLaunchPoolQuoteError,
                ZeroSeedLaunchPoolState, ZeroSeedLaunchQuoteObservation, installation_math,
            },
        },
        types::{Pool, PoolConfig, QuoteParams, TokenAmount},
    },
};

fn address(v: &str) -> Address {
    Address::from_str(v).unwrap()
}

fn num<T: FromStr>(v: &Value, key: &str) -> T
where
    T::Err: core::fmt::Debug,
{
    match &v[key] {
        Value::String(x) => x.parse().unwrap(),
        Value::Number(n) => n.to_string().parse().unwrap(),
        other => panic!("{key}: {other}"),
    }
}

fn state(v: &Value) -> ZeroSeedLaunchPoolState {
    ZeroSeedLaunchPoolState {
        sqrt_ratio: U256::from_str(s(v, "sqrt_ratio")).unwrap(),
        tick: num(v, "tick"),
        liquidity: num(v, "liquidity"),
    }
}

fn fee_schedule_v2(v: &Value) -> ZeroSeedLaunchFeeSchedule {
    assert!(
        v.get("feeDuration").is_none(),
        "a v2 vector has no feeDuration"
    );
    ZeroSeedLaunchFeeSchedule {
        trading_start: num(v, "tradingStart"),
        decay: ZeroSeedLaunchFeeDecay::TickRate {
            decay_rate_x32: num(v, "decayRateX32"),
        },
        initial_fee: num(v, "initialFee"),
        final_fee: num(v, "finalFee"),
    }
}

fn v2_instance(v: &Value, fee_model: ZeroSeedLaunchFeeModel) -> ZeroSeedLaunchInstance {
    ZeroSeedLaunchInstance {
        chain_id: 31337,
        extension: address(s(v, "extension")),
        extension_runtime: U256::from_str(EXTENSION_RUNTIME_V2).unwrap(),
        periphery: address(s(v, "periphery")),
        periphery_runtime: U256::from_str(PERIPHERY_RUNTIME_V2).unwrap(),
        core: address("0x00000000000014aa86c5d3c41765bb24e11bd701"),
        core_runtime: U256::from_str(CORE_RUNTIME).unwrap(),
        fee_model,
    }
}

fn pool_inputs(created: &Value) -> (EvmZeroSeedLaunchPoolKey, ZeroSeedLaunchConfig) {
    let token1 = address(s(created, "token1"));
    let tick_spacing: u32 = num(created, "tickSpacing");
    let key = EvmZeroSeedLaunchPoolKey {
        token0: address(s(created, "token0")),
        token1,
        config: PoolConfig {
            extension: address(s(created, "extension")),
            fee: num(created, "fee"),
            pool_type_config: TickSpacing(tick_spacing),
        },
    };
    let config = ZeroSeedLaunchConfig {
        quote_token: address(s(created, "quote")),
        range: ZeroSeedLaunchRange {
            launch_token_is_token1: address(s(created, "token")) == token1,
            ask_tick: num(created, "askTick"),
            upper_tick: num(created, "upperTick"),
            tick_spacing,
        },
        liquidity: num(created, "liquidity"),
        fee: fee_schedule_v2(created),
    };
    (key, config)
}

fn optional_limit(step: &Value) -> Option<U256> {
    let limit = U256::from_str(s(step, "limit")).unwrap();
    (!limit.is_zero()).then_some(limit)
}

fn pair(v: &Value, key: &str) -> [u128; 2] {
    let mut parts = s(v, key).split(',').map(|x| x.parse().unwrap());
    [parts.next().unwrap(), parts.next().unwrap()]
}

#[test]
fn tick_rate_parity_with_frozen_contract_execution() {
    let vectors: Value = serde_json::from_str(PARITY_V2).unwrap();
    assert_eq!(s(&vectors, "fee_model"), "tick_rate_v2");
    let scenarios = vectors["scenarios"].as_array().unwrap();
    assert_eq!(scenarios.len(), 17);
    let (mut compared, mut refused, mut claims, mut native, mut routed) = (0, 0, 0, 0, 0);
    let mut rates_seen = std::collections::BTreeSet::new();
    for scenario in scenarios {
        let name = s(scenario, "name");
        let created = &scenario["create"];
        assert_eq!(s(created, "coreCodehash"), CORE_RUNTIME, "{name}");
        assert_eq!(
            s(created, "extensionCodehash"),
            EXTENSION_RUNTIME_V2,
            "{name}"
        );
        assert_eq!(
            s(created, "peripheryCodehash"),
            PERIPHERY_RUNTIME_V2,
            "{name}"
        );
        let (key, config) = pool_inputs(created);
        rates_seen.insert(config.fee.decay_rate_x32().unwrap());
        let core_state = state(&created["state"]);
        // The harness instance is not a supported local pin, and a v1 instance at the same
        // addresses refuses the v2 launch by fee model before anything else.
        let quote = ZeroSeedLaunchQuoteObservation {
            chain_id: 31337,
            quote: config.quote_token,
            quote_runtime: None,
        };
        assert_eq!(
            EvmZeroSeedLaunchPool::new(
                key,
                config,
                core_state,
                &v2_instance(created, ZeroSeedLaunchFeeModel::TickRateV2),
                &quote
            ),
            Err(ZeroSeedLaunchPoolConstructionError::UnsupportedInstance)
        );
        let pool = EvmZeroSeedLaunchPool::new_math(key, config, core_state).unwrap();
        let installation = installation_math(
            &ZeroSeedLaunchParameters {
                supply: num(created, "requestedSupply"),
                quote_token: config.quote_token,
                range: config.range,
                fee: config.fee,
            },
            num(created, "createTs"),
        )
        .unwrap();
        assert_eq!(installation.liquidity, config.liquidity, "{name}");
        assert_eq!(
            installation.installed_supply,
            num::<u128>(created, "installedSupply"),
            "{name}"
        );
        assert_eq!(installation.sink_supply, num::<u128>(created, "sinkSupply"));
        if s(created, "quoteKind") == "native" {
            native += 1;
        }

        let mut current = pool.state();
        let mut fees = [0u128; 2];
        for step in scenario["steps"].as_array().unwrap() {
            let label = format!("{name} #{} {}", num::<u32>(step, "i"), s(step, "label"));
            routed += usize::from(step["via_router"].as_bool().unwrap());
            if s(step, "label") == "sellClaimedExactIn" {
                let claim = &scenario["claim"];
                assert_eq!(
                    [num::<u128>(claim, "amount0"), num::<u128>(claim, "amount1")],
                    fees,
                    "{name} claimed ledger"
                );
                assert_eq!(pair(claim, "extensionEvent"), fees, "{name}");
                assert_eq!(pair(claim, "peripheryEvent"), fees, "{name}");
                assert_eq!(pair(claim, "returned"), fees, "{name}");
                assert_eq!(pair(claim, "ledgerAfter"), [0, 0], "{name}");
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
                assert_eq!(step["pre_balances"], step["post_balances"], "{label}");
                assert_eq!(state(&step["post"]), current, "{label}");
                match s(step, "error") {
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
                    // Settlement, not pool math: the test account cannot pay.
                    TRANSFER_FROM_FAILED => assert!(result.is_ok(), "{label}"),
                    other => panic!("{label}: unexpected revert {other}"),
                }
                refused += 1;
                continue;
            }
            let swap = result.unwrap_or_else(|e| panic!("{label}: {e}"));
            let event = &step["event"];
            assert_eq!(swap.delta0, num::<i128>(step, "delta0"), "{label}");
            assert_eq!(swap.delta1, num::<i128>(step, "delta1"), "{label}");
            assert_eq!(swap.delta0, num::<i128>(event, "delta0"), "{label}");
            assert_eq!(swap.delta1, num::<i128>(event, "delta1"), "{label}");
            assert_eq!(swap.fee_rate, num::<u64>(event, "fee_rate"), "{label} rate");
            assert_eq!(swap.fee_rate, num::<u64>(step, "fee_at"), "{label} feeAt");
            assert_eq!(swap.fee_rate, pool.fee_at(ts), "{label}");
            assert_eq!(swap.fee_amount, num::<u128>(event, "fee_amount"), "{label}");
            assert_eq!(
                swap.fee_is_token1,
                event["fee_is_token1"].as_bool().unwrap(),
                "{label}"
            );
            let side = usize::from(swap.fee_is_token1);
            let ledger = [
                num::<u128>(step, "ledger_delta0"),
                num::<u128>(step, "ledger_delta1"),
            ];
            assert_eq!(ledger[side], swap.fee_amount, "{label} ledger");
            assert_eq!(ledger[1 - side], 0, "{label}");
            fees[side] += swap.fee_amount;
            assert_eq!(swap.state_after, state(&step["post"]), "{label} post state");
            // Balance deltas: Core and the holder move by exactly the swap deltas.
            for (i, delta) in [swap.delta0, swap.delta1].into_iter().enumerate() {
                let b = |k: &str, j: usize| U256::from_str(step[k][j].as_str().unwrap()).unwrap();
                let d = U256::from(delta.unsigned_abs());
                let (core, holder) = if delta >= 0 {
                    (b("pre_balances", i) + d, b("pre_balances", i + 2) - d)
                } else {
                    (b("pre_balances", i) - d, b("pre_balances", i + 2) + d)
                };
                assert_eq!(b("post_balances", i), core, "{label} Core balance");
                assert_eq!(b("post_balances", i + 2), holder, "{label} holder balance");
            }
            // The Pool interface quotes the same fill.
            let token = if is_token1 { key.token1 } else { key.token0 };
            let quote = pool
                .quote(QuoteParams {
                    token_amount: TokenAmount { token, amount },
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
            assert_eq!(quote.consumed_amount, specified, "{label}");
            assert_eq!(
                quote.calculated_amount,
                calculated.unsigned_abs(),
                "{label}"
            );
            assert_eq!(quote.fees_paid, swap.fee_amount, "{label}");
            current = swap.state_after;
            compared += 1;
        }
    }
    // Rates 0, 1, a quarter tick per second, the default, the 600 s rate and 2**64 - 1.
    assert_eq!(
        rates_seen.into_iter().collect::<Vec<_>>(),
        [
            0,
            1,
            1 << 30,
            ZERO_SEED_LAUNCH_DEFAULT_DECAY_RATE_X32,
            9_923_486_534_471,
            u64::MAX
        ]
    );
    assert_eq!(native, 6);
    assert!(claims >= 14, "{claims}");
    assert!(routed >= 11, "{routed}");
    assert_eq!(compared + refused, 722);
    assert!(compared >= 450, "{compared}");
    println!("tick-rate parity: {compared} executed, {refused} refused, {claims} claims");
}

/// Every v2 periphery `previewInstallation` and the `create` after it: the SDK's contract preview
/// equals the contract's result, including a zero and a maximum decay rate, both accepted.
#[test]
fn tick_rate_preview_and_creation_match_the_contract() {
    let vectors: Value = serde_json::from_str(PARITY_V2).unwrap();
    let previews = vectors["previews"].as_array().unwrap();
    let creations = vectors["creations"].as_array().unwrap();
    assert_eq!(previews.len(), 145);
    let mut ok = 0;
    for (preview, creation) in previews.iter().zip(creations) {
        let label = s(preview, "label");
        assert_eq!(s(creation, "label"), label);
        let quote = address(s(preview, "quote"));
        let predicted = address(s(preview, "predictedToken"));
        let parameters = ZeroSeedLaunchParameters {
            supply: num(preview, "supply"),
            quote_token: quote,
            range: ZeroSeedLaunchRange {
                launch_token_is_token1: quote < predicted,
                ask_tick: num(preview, "askTick"),
                upper_tick: num(preview, "upperTick"),
                tick_spacing: num(preview, "tickSpacing"),
            },
            fee: fee_schedule_v2(preview),
        };
        let quote_runtime = s(preview, "quoteCodehash");
        let context = |instance| ZeroSeedLaunchLocalPreview {
            instance,
            owner: address(s(preview, "owner")),
            salt: B256::from_str(s(preview, "userSalt")).unwrap(),
            name: s(preview, "name"),
            symbol: s(preview, "symbol"),
            decimals: num(preview, "decimals"),
            quote_runtime: (quote_runtime != "none")
                .then(|| U256::from_str(quote_runtime).unwrap()),
            predicted_token_has_code: s(preview, "tokenHasCode") == "1",
            build_time: 0,
            execution_expiry: 0,
        };
        let v2 = v2_instance(preview, ZeroSeedLaunchFeeModel::TickRateV2);
        let v1 = v2_instance(preview, ZeroSeedLaunchFeeModel::FixedBaseDurationV1);
        assert_eq!(context(&v2).predicted_token(), predicted, "{label}");
        let now: u64 = num(preview, "now");
        // A v1 deployment cannot take v2 parameters.
        assert_eq!(
            context(&v1).contract_preview(&parameters, now),
            Err(ZeroSeedLaunchParameterError::FeeModelMismatch),
            "{label}"
        );
        let result = context(&v2).contract_preview(&parameters, now);
        let accepted = preview["ok"].as_bool().unwrap();
        assert_eq!(accepted, creation["ok"].as_bool().unwrap(), "{label}");
        if label.ends_with("_rate0") || label.ends_with("_rateMax") {
            assert!(accepted, "{label}: every uint64 rate is accepted");
        }
        if accepted {
            let installation = result.unwrap_or_else(|e| panic!("{label}: {e}"));
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
            assert_eq!(
                installation.sink_supply,
                num::<u128>(preview, "sinkSupply"),
                "{label}"
            );
            assert_eq!(
                num::<u128>(creation, "liquidity"),
                installation.liquidity,
                "{label}"
            );
            ok += 1;
        } else {
            let err = s(preview, "err");
            assert!(result.is_err(), "{label}: contract refused {err}");
            if &err[..10] == "0xf75a271a" {
                assert_eq!(
                    result,
                    Err(ZeroSeedLaunchParameterError::InvalidFeeSchedule)
                );
            }
        }
    }
    assert!(ok >= 68, "{ok}");
}

/// The indexer's anvil fixture of the tick-rate revision is the only supported v2 instance, and
/// only with the tick-rate model: the same addresses with the fixed-base model are refused.
#[test]
fn local_tick_rate_instance_is_pinned_with_its_model() {
    const INDEXER_V2: &str = include_str!("vectors/v2/zero-seed-launch-indexer.json");
    let fixture: Value = serde_json::from_str(INDEXER_V2).unwrap();
    assert_eq!(s(&fixture, "feeModel"), "tick_rate_v2");
    assert_eq!(
        s(&fixture["provenance"], "evmContractsHead"),
        "3d6378f585591dc7eabeea6976932c30524bb8ea"
    );
    let entry = &fixture["instances"][0];
    let instance = |fee_model| ZeroSeedLaunchInstance {
        chain_id: fixture["chainId"].as_u64().unwrap(),
        extension: address(s(entry, "extension")),
        extension_runtime: U256::from_str(s(entry, "extensionRuntimeKeccak")).unwrap(),
        periphery: address(s(entry, "periphery")),
        periphery_runtime: U256::from_str(s(entry, "peripheryRuntimeKeccak")).unwrap(),
        core: address(s(&fixture["addresses"], "core")),
        core_runtime: U256::from_str(s(&fixture["provenance"], "coreRuntimeKeccak")).unwrap(),
        fee_model,
    };
    assert_eq!(s(entry, "extensionRuntimeKeccak"), EXTENSION_RUNTIME_V2);
    assert_eq!(
        instance(ZeroSeedLaunchFeeModel::TickRateV2).validate(),
        Ok(())
    );
    assert_eq!(
        instance(ZeroSeedLaunchFeeModel::FixedBaseDurationV1).validate(),
        Err(ZeroSeedLaunchParameterError::UnsupportedInstance)
    );
}
