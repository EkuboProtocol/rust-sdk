//! Fixed-base creator-fee schedule and high-rate swap parity.
//!
//! The independent oracle is the protocol generator's 250-digit `Decimal` output: every second of
//! twelve curves (5/50/75/90/99/max% to 0.3% over 600 s and 3,600 s, 25,212 rows) in
//! `tests/vectors/zero-seed-launch-fee-curve-all-seconds.json`, and the table, decay samples and
//! fee rows of `tests/vectors/zero-seed-launch-fee-decay-vectors.json`. Every row is checked
//! against this implementation, and the SHA-256 chains over each curve are checked against the
//! contract's vectors (`tests/vectors/zero-seed-launch.json`).
//!
//! These are unit tests so that the highest encodable rate, `2**64 - 1`, which `create` and
//! `new_math` refuse, can be exercised by overwriting the stored initial fee of a valid pool,
//! the counterpart of the contract test's storage injection. That configuration is research-only
//! and unreachable through any public constructor.

use std::{
    collections::HashMap,
    format,
    string::{String, ToString},
    vec::Vec,
};

use serde_json::Value;
use sha2::{Digest, Sha256};

use super::*;
use crate::quoting::types::TokenAmount;

const VECTORS: &str = include_str!("../../../../tests/vectors/zero-seed-launch.json");
const ROWS: &str = include_str!("../../../../tests/vectors/zero-seed-launch-fee-curve-rows.json");
const ORACLE: &str =
    include_str!("../../../../tests/vectors/zero-seed-launch-fee-curve-all-seconds.json");
const DECAY_VECTORS: &str =
    include_str!("../../../../tests/vectors/zero-seed-launch-fee-decay-vectors.json");

const ORACLE_ROWS: usize = 25_212;

const Q: u128 = ZERO_SEED_LAUNCH_Q64;
const START: u64 = 1000;
const FEE_5: u64 = 922_337_203_685_477_580;
const FEE_03: u64 = 55_340_232_221_128_654;
const RATE_50: u64 = 9_223_372_036_854_775_808;
const RATE_MAX: u64 = u64::MAX;
/// `floor(2**64 * 2**(-1/600))`: the per-second factor of the previous variable-base schedule.
const LEGACY_FACTOR: u64 = 18_425_445_863_997_925_462;
const QUOTE_HIGH: &str = "0xffffffffffffffffffffffffffffffffffffffff";
const QUOTE_LOW: &str = "0x0000000000000000000000000000000000010000";

fn address(s: &str) -> Address {
    Address::from_str(s).unwrap()
}

fn big(v: &Value) -> u128 {
    match v {
        Value::String(s) => s.parse().unwrap(),
        Value::Number(n) => u128::from(n.as_u64().unwrap()),
        _ => panic!("not an integer: {v}"),
    }
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

/// `VEC|kind|a=1|flag|b=2` rows as maps; bare words map to an empty value.
fn rows(kind: &str) -> Vec<HashMap<String, String>> {
    let all: Value = serde_json::from_str(ROWS).unwrap();
    all[kind]
        .as_array()
        .unwrap()
        .iter()
        .map(|row| {
            row["raw"]
                .as_str()
                .unwrap()
                .split('|')
                .skip(2)
                .map(|part| match part.split_once('=') {
                    Some((k, v)) => (k.to_string(), v.to_string()),
                    None => (part.to_string(), String::new()),
                })
                .collect()
        })
        .collect()
}

fn n<T: FromStr>(row: &HashMap<String, String>, key: &str) -> T
where
    T::Err: core::fmt::Debug,
{
    row.get(key)
        .unwrap_or_else(|| panic!("{key} missing in {row:?}"))
        .parse()
        .unwrap()
}

fn rate_of(label: &str) -> u64 {
    match label {
        "5" => FEE_5,
        "50" => RATE_50,
        "75" => 13_835_058_055_282_163_712,
        "90" => 16_602_069_666_338_596_454,
        "99" => ZERO_SEED_LAUNCH_MAX_CREATOR_FEE,
        "max" => RATE_MAX,
        _ => panic!("rate {label}"),
    }
}

/// The previous variable-base schedule (`powQ64` square-and-multiply, floor after every Q64
/// multiply), kept only to reproduce the contract's pinned deviation from it.
fn legacy_fee(initial: u64, final_fee: u64, duration: u32, elapsed: u64) -> u64 {
    let power = |mut exponent: u64| {
        let (mut result, mut base) = (Q, u128::from(LEGACY_FACTOR));
        while exponent != 0 {
            if exponent & 1 != 0 {
                result = (result * base) >> 64;
            }
            exponent >>= 1;
            if exponent != 0 {
                base = (base * base) >> 64;
            }
        }
        result
    };
    if elapsed == 0 {
        return initial;
    }
    if elapsed >= u64::from(duration) {
        return final_fee;
    }
    let end = power(u64::from(duration));
    final_fee + (u128::from(initial - final_fee) * (power(elapsed) - end) / (Q - end)) as u64
}

/// Deterministic xorshift64* so the property sweep is reproducible without a dependency.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0.wrapping_mul(0x2545_f491_4f6c_dd1d)
    }
}

/// The 17-entry table equals the contract's vectors and the generator's, each constant is
/// `decay_q128(2**i)`, and bit 0 equals the contract's single conditional subtraction.
#[test]
fn decay_table_matches_contract_and_generator() {
    let v: Value = serde_json::from_str(VECTORS).unwrap();
    let g: Value = serde_json::from_str(DECAY_VECTORS).unwrap();
    for table in [&v["fixture"]["fee_decay_table_q128"], &g["table_q128"]] {
        let table: Vec<u128> = table.as_array().unwrap().iter().map(big).collect();
        assert_eq!(table, ZERO_SEED_LAUNCH_DECAY_TABLE_Q128);
    }
    assert_eq!(
        big(&v["fixture"]["fee_decay_zero_from_s"]),
        u128::from(ZERO_SEED_LAUNCH_DECAY_ZERO_FROM)
    );
    assert_eq!(
        big(&g["zero_at_or_above"]),
        u128::from(ZERO_SEED_LAUNCH_DECAY_ZERO_FROM)
    );
    assert_eq!(big(&v["fixture"]["fee_half_life_s"]), 600);
    for (bit, constant) in ZERO_SEED_LAUNCH_DECAY_TABLE_Q128.iter().enumerate() {
        assert_eq!(decay_q128(1 << bit), U256::from(*constant), "bit {bit}");
    }
    assert_eq!(
        TWO_POW_128 - U256::from(0x004b_aa9b_e036_97a9_bc38_4a82_1d46_c25f_u128),
        U256::from(ZERO_SEED_LAUNCH_DECAY_TABLE_Q128[0])
    );
    for sample in g["decay_samples"].as_array().unwrap() {
        let t = sample["t"].as_u64().unwrap();
        assert_eq!(
            decay_q128(t),
            U256::from_str(sample["decay_q128"].as_str().unwrap()).unwrap(),
            "t={t}"
        );
    }
    assert_eq!(decay_q128(0), TWO_POW_128);
    assert_eq!(decay_q128(1 << 17), U256::ZERO);
    assert_eq!(
        decay_q128((1 << 17) + 1),
        U256::ZERO,
        "no aliasing to bit 0"
    );
    assert_eq!(decay_q128(u64::MAX), U256::ZERO);
}

/// Non-increasing over the whole nonzero domain; first zero at 76,800 s (600 * 128).
#[test]
fn decay_is_monotone_exhaustively() {
    let mut previous = decay_q128(0);
    let mut first_zero = None;
    for t in 1..=ZERO_SEED_LAUNCH_DECAY_ZERO_FROM {
        let value = decay_q128(t);
        assert!(value <= previous, "t={t}");
        if value.is_zero() && first_zero.is_none() {
            first_zero = Some(t);
        }
        previous = value;
    }
    let v: Value = serde_json::from_str(VECTORS).unwrap();
    assert_eq!(
        first_zero.map(u128::from),
        Some(big(&v["fixture"]["fee_decay_first_zero_s"]))
    );
}

/// Every row of the independent 25,212-row oracle, and the 12 contract-pinned SHA-256 chains
/// recomputed from both the oracle rows and this implementation.
#[test]
fn every_second_of_twelve_curves_matches_the_decimal_oracle() {
    let oracle: Value = serde_json::from_str(ORACLE).unwrap();
    let oracle = oracle.as_array().unwrap();
    assert_eq!(oracle.len(), ORACLE_ROWS);
    // Per (duration, initial): the chain over the oracle's fees, over the SDK's, and the row count.
    type Chains = HashMap<(u32, u64), ([u8; 32], [u8; 32], u64)>;
    let mut chains = Chains::new();
    let mut order = Vec::new();
    for row in oracle {
        let row: Vec<u128> = row.as_array().unwrap().iter().map(big).collect();
        let (initial, final_fee) = (row[0] as u64, row[1] as u64);
        let (duration, elapsed, fee) = (row[2] as u32, row[3] as u64, row[4] as u64);
        assert_eq!(final_fee, FEE_03);
        assert_eq!(
            decayed_fee(initial, final_fee, duration, elapsed),
            fee,
            "{row:?}"
        );
        let schedule = ZeroSeedLaunchFeeSchedule {
            trading_start: START,
            fee_duration: duration,
            initial_fee: initial,
            final_fee,
        };
        assert_eq!(schedule.fee_at(START + elapsed), fee);
        let entry = chains.entry((duration, initial)).or_insert_with(|| {
            order.push((duration, initial));
            ([0u8; 32], [0u8; 32], 0)
        });
        assert_eq!(entry.2, elapsed, "rows are every second in order");
        let mut h = Sha256::new();
        h.update(entry.0);
        h.update(fee.to_be_bytes());
        entry.0 = h.finalize().into();
        let mut h = Sha256::new();
        h.update(entry.1);
        h.update(schedule.fee_at(START + elapsed).to_be_bytes());
        entry.1 = h.finalize().into();
        entry.2 += 1;
    }
    let v: Value = serde_json::from_str(VECTORS).unwrap();
    let g: Value = serde_json::from_str(DECAY_VECTORS).unwrap();
    let curve = &v["fee_curve"];
    assert_eq!(big(&curve["final_fee_q64"]) as u64, FEE_03);
    let mut digests = 0;
    for duration in [600u32, 3600] {
        for label in ["5", "50", "75", "90", "99", "max"] {
            let initial = big(&curve["rates_q64"][label]) as u64;
            assert_eq!(initial, rate_of(label));
            let (from_oracle, from_sdk, count) = chains[&(duration, initial)];
            assert_eq!(count, u64::from(duration) + 1);
            let pinned = curve["all_second_digests_sha256"][duration.to_string()][label]
                .as_str()
                .unwrap();
            assert_eq!(hex(&from_oracle), pinned, "{duration} {label}");
            assert_eq!(hex(&from_sdk), pinned, "{duration} {label}");
            if let Some(generator) =
                g["all_second_digests_sha256"][duration.to_string()][label].as_str()
            {
                assert_eq!(generator, pinned);
            }
            digests += 1;
        }
    }
    assert_eq!(digests, 12);
    assert_eq!(chains.len(), 12);
    assert_eq!(order.len(), 12);
}

#[test]
fn generator_fee_rows_and_contract_fee_rows() {
    let g: Value = serde_json::from_str(DECAY_VECTORS).unwrap();
    let fee_rows = g["fee_rows"].as_array().unwrap();
    assert_eq!(fee_rows.len(), 200);
    for row in fee_rows {
        assert_eq!(
            decayed_fee(
                big(&row["initial"]) as u64,
                big(&row["final"]) as u64,
                big(&row["duration"]) as u32,
                big(&row["elapsed"]) as u64,
            ),
            big(&row["fee"]) as u64,
            "{row}"
        );
    }
    let v: Value = serde_json::from_str(VECTORS).unwrap();
    let fixture = &v["fixture"];
    for row in v["fee"].as_array().unwrap() {
        let schedule = ZeroSeedLaunchFeeSchedule {
            trading_start: big(&fixture["trading_start"]) as u64,
            fee_duration: big(&row["duration"]) as u32,
            initial_fee: big(&fixture["fee_initial_q64"]) as u64,
            final_fee: big(&fixture["fee_final_q64"]) as u64,
        };
        let offset = row["t_minus_start"].as_i64().map_or_else(
            || i128::from(row["t_minus_start"].as_u64().unwrap()),
            i128::from,
        );
        // The largest offset is u64::MAX - start: no narrowing of the elapsed time.
        let timestamp = u64::try_from(i128::from(schedule.trading_start) + offset).unwrap();
        assert_eq!(
            schedule.fee_at(timestamp),
            big(&row["fee_q64"]) as u64,
            "{row}"
        );
    }
    // The canonical 50% -> 0.3% over 3,600 s midpoint, pinned by the contract from Python.
    assert_eq!(
        decayed_fee(RATE_50, FEE_03, 3600, 1800),
        1_074_010_432_735_978_337
    );
}

/// The contract's pinned deviation from the previous variable-base schedule at the canonical
/// 50% -> 0.3% parameters: same half-life, at most 133 Q64 units apart.
#[test]
fn deviation_from_the_legacy_schedule() {
    let v: Value = serde_json::from_str(VECTORS).unwrap();
    let legacy = &v["fee_curve"]["legacy_comparison"];
    assert_eq!(big(&legacy["legacy_factor_q64"]) as u64, LEGACY_FACTOR);
    for (duration, expected) in legacy["max_abs_diff_q64_by_duration"].as_object().unwrap() {
        let duration: u32 = duration.parse().unwrap();
        let mut worst = 0;
        let mut previous = RATE_50;
        for t in 0..=u64::from(duration) {
            let fee = decayed_fee(RATE_50, FEE_03, duration, t);
            assert!(fee <= previous);
            previous = fee;
            worst = worst.max(fee.abs_diff(legacy_fee(RATE_50, FEE_03, duration, t)));
        }
        assert_eq!(u128::from(worst), big(expected), "D={duration}");
    }
}

/// Seeded sweep over the whole `u32` duration domain, including rates the contract refuses:
/// endpoints, boundedness and monotonicity in the elapsed time.
#[test]
fn seeded_domain_sweep_bounded_monotone_endpoints() {
    let mut rng = Rng(0x9e37_79b9_7f4a_7c15);
    let edge_durations = [
        1u32,
        2,
        3,
        600,
        3600,
        131_071,
        131_072,
        u32::MAX - 1,
        u32::MAX,
    ];
    for i in 0..20_000 {
        let duration = if i % 3 == 0 {
            edge_durations[(rng.next() % 9) as usize]
        } else {
            (rng.next() as u32).max(1)
        };
        let (a, b) = (rng.next(), rng.next());
        let (initial, final_fee) = (a.max(b), a.min(b));
        let elapsed = match i % 4 {
            0 => rng.next() % u64::from(duration),
            1 => u64::from(duration) - 1,
            2 => 1,
            _ => rng.next() % (u64::from(duration) + 2),
        };
        let fee = decayed_fee(initial, final_fee, duration, elapsed);
        assert!(final_fee <= fee && fee <= initial);
        assert!(decayed_fee(initial, final_fee, duration, elapsed + 1) <= fee);
        assert_eq!(decayed_fee(initial, final_fee, duration, 0), initial);
        assert_eq!(
            decayed_fee(initial, final_fee, duration, u64::from(duration)),
            final_fee
        );
    }
}

/// Validation: the 99% cap accepted, one above and the highest encodable rate refused with
/// `FeeTooHigh`; zero duration and a rising schedule refused with `InvalidFeeSchedule`.
#[test]
fn validation_cap_and_schedule() {
    type E = ZeroSeedLaunchParameterError;
    assert_eq!(ZERO_SEED_LAUNCH_MAX_CREATOR_FEE as u128, 99 * Q / 100);
    let mut p = ZeroSeedLaunchParameters {
        supply: 1_000_000_000_000_000_000_000_000_000,
        range: ZeroSeedLaunchRange {
            launch_token_is_token1: false,
            ask_tick: -13_815_500,
            upper_tick: -13_815_500 + 4_605_200,
            tick_spacing: 100,
        },
        fee: ZeroSeedLaunchFeeSchedule {
            trading_start: START,
            fee_duration: 3600,
            initial_fee: ZERO_SEED_LAUNCH_MAX_CREATOR_FEE,
            final_fee: FEE_03,
        },
    };
    assert!(validate_launch_parameters_math(&p, START).is_ok());
    p.fee.fee_duration = u32::MAX;
    assert!(validate_launch_parameters_math(&p, START).is_ok());
    p.fee.fee_duration = 0;
    assert_eq!(
        validate_launch_parameters_math(&p, START),
        Err(E::InvalidFeeSchedule)
    );
    p.fee.fee_duration = 3600;
    p.fee.final_fee = p.fee.initial_fee + 1;
    assert_eq!(
        validate_launch_parameters_math(&p, START),
        Err(E::InvalidFeeSchedule)
    );
    p.fee.final_fee = FEE_03;
    for rate in [ZERO_SEED_LAUNCH_MAX_CREATOR_FEE + 1, RATE_MAX] {
        p.fee.initial_fee = rate;
        assert_eq!(
            validate_launch_parameters_math(&p, START),
            Err(E::FeeTooHigh)
        );
    }
}

struct Fixture {
    pool: ZeroSeedLaunchPool,
    token: Address,
    quote: Address,
}

/// The contract fixture's launch: 1e9 tokens requested over 100x from 1e-6 (18/18) or 1e-18 raw
/// (18/6) quote per token, spacing 100. Token0 launches quote WETH at the top of the address
/// space; token1 launches quote native ETH (18/18) or a six-decimal token at 0x10000.
fn fixture(order: &str, decimals: &str, duration: u32, initial: u64) -> Fixture {
    let is1 = order == "t1";
    let ask = if decimals == "18/6" {
        -41_446_500
    } else {
        -13_815_500
    };
    let quote = match (is1, decimals) {
        (false, _) => address(QUOTE_HIGH),
        (true, "18/18") => Address::ZERO,
        (true, _) => address(QUOTE_LOW),
    };
    let token = address(if is1 {
        "0x00000000000000000000000000000000000f0000"
    } else {
        "0x00000000000000000000000000000000000a0000"
    });
    let range = ZeroSeedLaunchRange {
        launch_token_is_token1: is1,
        ask_tick: ask,
        upper_tick: ask + 4_605_200,
        tick_spacing: 100,
    };
    // Valid configuration at the cap; the research-only maximum is injected below.
    let fee = ZeroSeedLaunchFeeSchedule {
        trading_start: START,
        fee_duration: duration,
        initial_fee: initial.min(ZERO_SEED_LAUNCH_MAX_CREATOR_FEE),
        final_fee: FEE_03,
    };
    let parameters = ZeroSeedLaunchParameters {
        supply: 1_000_000_000_000_000_000_000_000_000,
        range,
        fee,
    };
    let installation = preview_installation_math(&parameters, START).unwrap();
    let (token0, token1) = if is1 { (quote, token) } else { (token, quote) };
    let tick = range.initial_tick();
    let (lower, upper) = range.pool_bounds();
    let mut pool = ZeroSeedLaunchPool::new_math(
        PoolKey {
            token0,
            token1,
            config: PoolConfig {
                extension: address("0x5100000000000000000000000000000000000000"),
                fee: 0,
                pool_type_config: TickSpacing(100),
            },
        },
        ZeroSeedLaunchConfig {
            range,
            liquidity: installation.liquidity,
            fee,
        },
        ZeroSeedLaunchPoolState {
            sqrt_ratio: to_sqrt_ratio::<Evm>(tick).unwrap(),
            tick,
            liquidity: if tick >= lower && tick < upper {
                installation.liquidity
            } else {
                0
            },
        },
    )
    .unwrap();
    if initial > ZERO_SEED_LAUNCH_MAX_CREATOR_FEE {
        // Research-only injection, as `_injectInitialFee` in the contract study: unreachable via
        // `new`/`new_math`, which refuse it.
        let mut refused = *pool.launch();
        refused.fee.initial_fee = initial;
        assert_eq!(
            ZeroSeedLaunchPool::new_math(pool.key(), refused, pool.state()),
            Err(ZeroSeedLaunchPoolConstructionError::InvalidLaunchConfig)
        );
        pool.launch.fee.initial_fee = initial;
    }
    Fixture { pool, token, quote }
}

struct Fill {
    consumed: i128,
    calculated: u128,
    fee: u128,
    state: ZeroSeedLaunchPoolState,
}

fn swap(
    f: &Fixture,
    state: ZeroSeedLaunchPoolState,
    token: Address,
    amount: i128,
    at: u64,
) -> Result<Fill, ZeroSeedLaunchPoolQuoteError> {
    f.pool
        .quote(QuoteParams {
            token_amount: TokenAmount { token, amount },
            sqrt_ratio_limit: None,
            override_state: Some(state),
            meta: at,
        })
        .map(|q| Fill {
            consumed: q.consumed_amount,
            calculated: q.calculated_amount,
            fee: q.fees_paid,
            state: q.state_after,
        })
}

/// The contract's executed 50/75/90/99/max matrix, both orders (WETH and native ETH at 18/18),
/// 18/6: one raw unit, one whole unit exact-in, exact-out of that net, then selling everything
/// held.
#[test]
fn high_rate_matrix_matches_executed_rows() {
    let rows = rows("highRate");
    assert_eq!(rows.len(), 100);
    let mut checked = 0;
    for chunk in rows.chunks(5) {
        let head = &chunk[0];
        let (label, order, dec) = (&head["rate"], &head["order"], &head["dec"]);
        let rate = rate_of(label);
        let f = fixture(order, dec, 3600, rate);
        assert_eq!(f.pool.fee_at(START), rate);
        let unit: i128 = if dec == "18/6" {
            1_000_000
        } else {
            1_000_000_000_000_000_000
        };
        let mut state = f.pool.state();
        let mut held: u128 = 0;
        for row in chunk {
            assert_eq!(
                (&row["rate"], &row["order"], &row["dec"]),
                (label, order, dec)
            );
            if row.contains_key("oneUnit") {
                let q = swap(&f, state, f.quote, 1, START).unwrap();
                assert_eq!(q.calculated, n::<u128>(row, "net"), "{row:?}");
                assert_eq!(q.fee, n::<u128>(row, "fee"));
                assert_eq!(q.calculated + q.fee, n::<u128>(row, "gross"));
                if rate == RATE_MAX {
                    assert_eq!(q.calculated, 0, "max rate: one unit buys nothing");
                }
                held += q.calculated;
                state = q.state;
            } else if row.contains_key("buyExactIn") {
                assert_eq!(n::<i128>(row, "quoteIn"), unit);
                let q = swap(&f, state, f.quote, unit, START).unwrap();
                assert_eq!(q.calculated, n::<u128>(row, "net"), "{row:?}");
                assert_eq!(q.fee, n::<u128>(row, "fee"));
                assert_eq!(q.calculated + q.fee, n::<u128>(row, "gross"));
                held += q.calculated;
                state = q.state;
            } else if row.contains_key("buyExactOut") {
                let out: u128 = n(row, "tokenOut");
                let q = swap(&f, state, f.token, -(out as i128), START).unwrap();
                assert_eq!(q.consumed, -(out as i128));
                assert_eq!(q.calculated, n::<u128>(row, "paid"), "{row:?}");
                assert_eq!(q.fee, n::<u128>(row, "fee"));
                assert_eq!(q.calculated - q.fee, n::<u128>(row, "calcQuote"));
                held += out;
                state = q.state;
            } else if row.contains_key("sellAll") {
                assert_eq!(n::<u128>(row, "tokenIn"), held);
                let q = swap(&f, state, f.token, held as i128, START).unwrap();
                assert_eq!(q.calculated, n::<u128>(row, "quoteOut"), "{row:?}");
                assert_eq!(q.fee, n::<u128>(row, "fee"));
                assert_eq!(q.calculated + q.fee, n::<u128>(row, "grossQuote"));
            } else {
                assert!(row.contains_key("dust"));
                continue;
            }
            checked += 1;
        }
    }
    assert_eq!(checked, 80);
}

/// Exact-output representation limits at the injected maximum rate, as the contract's executed
/// bounds test: one unit grosses up to 2**64; along increasing outputs the swap executes with
/// `paid = calc * 2**64`, then fails the signed int128 conversion, then the uint128 helper.
#[test]
fn exact_output_helper_and_signed_bounds() {
    assert_eq!(amount_before_fee::<Evm>(1, RATE_MAX), Some(Q));
    assert_eq!(amount_before_fee::<Evm>(Q, RATE_MAX), None);

    let f = fixture("t0", "18/18", 3600, RATE_MAX);
    let state = f.pool.state();
    let probe = |out: u128| swap(&f, state, f.token, -(out as i128), START);
    let supply = preview_installation_math(
        &ZeroSeedLaunchParameters {
            supply: 1_000_000_000_000_000_000_000_000_000,
            range: f.pool.launch().range,
            fee: ZeroSeedLaunchFeeSchedule {
                initial_fee: ZERO_SEED_LAUNCH_MAX_CREATOR_FEE,
                ..f.pool.launch().fee
            },
        },
        START,
    )
    .unwrap()
    .installed_supply;
    let (mut lo, mut hi) = (1u128, supply);
    while lo < hi {
        let mid = lo + (hi - lo).div_ceil(2);
        if probe(mid).is_ok() {
            lo = mid;
        } else {
            hi = mid - 1;
        }
    }
    let last = probe(lo).unwrap();
    assert_eq!(last.calculated, (last.calculated - last.fee) << 64);
    assert!(last.calculated - last.fee <= (i128::MAX as u128) >> 64);
    assert_eq!(
        probe(lo + 1).err(),
        Some(ZeroSeedLaunchPoolQuoteError::Overflow)
    );
    let (mut lo, mut hi) = (lo + 1, supply);
    while lo < hi {
        let mid = lo + (hi - lo).div_ceil(2);
        if probe(mid).err() == Some(ZeroSeedLaunchPoolQuoteError::Overflow) {
            lo = mid;
        } else {
            hi = mid - 1;
        }
    }
    assert_eq!(
        probe(lo + 1).err(),
        Some(ZeroSeedLaunchPoolQuoteError::AmountBeforeFeeOverflow)
    );
}

/// At the injected maximum rate one wei quotes and fills zero, which full-fill quoting refuses;
/// a whole unit fills positively; a buy far beyond inventory fills partially to the bound.
#[test]
fn max_rate_zero_and_partial_fills() {
    for order in ["t0", "t1"] {
        let f = fixture(order, "18/18", 3600, RATE_MAX);
        let wei = swap(&f, f.pool.state(), f.quote, 1, START).unwrap();
        assert_eq!((wei.consumed, wei.calculated), (1, 0));
        assert_eq!(
            f.pool
                .quote_full_fill(QuoteParams {
                    token_amount: TokenAmount {
                        token: f.quote,
                        amount: 1
                    },
                    sqrt_ratio_limit: None,
                    override_state: Some(f.pool.state()),
                    meta: START,
                })
                .err(),
            Some(ZeroSeedLaunchFullFillError::ZeroOutput)
        );
        let unit = swap(&f, wei.state, f.quote, 1_000_000_000_000_000_000, START).unwrap();
        assert!(unit.calculated > 0);
        let huge = 1_000_000_000_000_000_000_000_000_000_000;
        let partial = swap(&f, unit.state, f.quote, huge, START).unwrap();
        assert!(partial.consumed < huge);
        let (lower, upper) = f.pool.launch().range.pool_bounds();
        let bound = if order == "t1" { lower } else { upper };
        assert_eq!(
            partial.state.sqrt_ratio,
            to_sqrt_ratio::<Evm>(bound).unwrap()
        );
    }
}
