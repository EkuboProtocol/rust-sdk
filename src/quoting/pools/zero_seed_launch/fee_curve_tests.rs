//! Exponential creator-fee schedule and high-rate swap parity against the contract's draft
//! vectors (`tests/vectors/zero-seed-launch.json` and the executed `VEC|` rows of its fee-curve
//! study in `tests/vectors/zero-seed-launch-fee-curve-rows.json`).
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

/// SHA-256 of the contract reference's `--export` file: every second of both study schedules at
/// all six rates, `[initial, final, duration, factor, elapsed, fee]` as decimal strings.
const PYTHON_EXPORT_SHA256: &str =
    "cf6950db88ede4fff87a011b902c4d9d18f878a8b1eacbe622bea32e953f1502";
const PYTHON_EXPORT_ROWS: usize = 25_212;

const Q: u128 = ZERO_SEED_LAUNCH_Q64;
const START: u64 = 1000;
const FEE_5: u64 = 922_337_203_685_477_580;
const FEE_03: u64 = 55_340_232_221_128_654;
const FACTOR_600: u64 = 18_319_323_104_848_571_946;
const FACTOR_3600: u64 = 18_425_445_863_997_925_462;
const FACTOR_HALF_1800: u64 = 18_439_641_936_446_208_053;
const RATE_50: u64 = 9_223_372_036_854_775_808;
const RATE_MAX: u64 = u64::MAX;
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

fn linear(initial: u64, final_fee: u64, duration: u32, elapsed: u64) -> u64 {
    if elapsed == 0 {
        return initial;
    }
    if elapsed >= u64::from(duration) {
        return final_fee;
    }
    initial - (u128::from(initial - final_fee) * u128::from(elapsed) / u128::from(duration)) as u64
}

/// Independent widened reference: the same normative order in 256-bit arithmetic, so a `u128`
/// wrap in the production path would show up as a mismatch.
fn reference_fee(initial: u64, final_fee: u64, factor: u64, duration: u32, elapsed: u64) -> u64 {
    let q: U256 = U256::from(1u8) << 64;
    let power = |mut exponent: u64| {
        let (mut result, mut base): (U256, U256) = (q, U256::from(factor));
        while exponent != 0 {
            if exponent & 1 != 0 {
                result = result * base / q;
            }
            exponent >>= 1;
            if exponent != 0 {
                base = base * base / q;
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
    let excess = U256::from(initial - final_fee) * (power(elapsed) - end) / (q - end);
    final_fee + excess.to::<u64>()
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

#[test]
fn power_identities() {
    for factor in [0, 1, 2, FACTOR_600, FACTOR_3600, u64::MAX - 7, u64::MAX] {
        assert_eq!(pow_q64(factor, 0), Q);
        assert_eq!(pow_q64(factor, 1), u128::from(factor));
        assert_eq!(
            pow_q64(factor, 2),
            (u128::from(factor) * u128::from(factor)) >> 64
        );
    }
    // 0b101: result*b, then b^2, b^4, result*b^4; the last square is skipped.
    let b = u128::from(FACTOR_3600);
    let b2 = (b * b) >> 64;
    let b4 = (b2 * b2) >> 64;
    assert_eq!(pow_q64(FACTOR_3600, 5), (((Q * b) >> 64) * b4) >> 64);
    assert_eq!(pow_q64(0, 1 << 40), 0);
    assert!(pow_q64(u64::MAX, u64::from(u32::MAX)) < Q);
}

/// Every second of both study schedules at 5/50/75/90/99/max: the contract's pinned SHA-256
/// chains, and the contract's Python export reproduced byte for byte.
#[test]
fn all_seconds_match_contract_digests_and_python_export() {
    let v: Value = serde_json::from_str(VECTORS).unwrap();
    let curve = &v["fee_curve"];
    let factors = &v["fixture"]["fee_decay_factors_q64"];
    let final_fee = big(&curve["final_fee_q64"]) as u64;
    assert_eq!(final_fee, FEE_03);
    assert_eq!(big(&factors["600"]) as u64, FACTOR_600);
    assert_eq!(big(&factors["3600"]) as u64, FACTOR_3600);

    let mut export = String::from("[");
    let mut count = 0usize;
    let mut digests = 0;
    // Python iterates the digest object in file order: 600, then 3600; rates 5..max.
    for duration in [600u32, 3600] {
        let factor = big(&factors[duration.to_string()]) as u64;
        for label in ["5", "50", "75", "90", "99", "max"] {
            let initial = big(&curve["rates_q64"][label]) as u64;
            assert_eq!(initial, rate_of(label));
            let schedule = ZeroSeedLaunchFeeSchedule {
                trading_start: START,
                fee_duration: duration,
                initial_fee: initial,
                final_fee,
                decay_factor: factor,
            };
            let mut chain = [0u8; 32];
            let mut previous = initial;
            for t in 0..=u64::from(duration) {
                let fee = schedule.fee_at(START + t);
                assert_eq!(fee, decayed_fee(initial, final_fee, factor, duration, t));
                assert_eq!(fee, reference_fee(initial, final_fee, factor, duration, t));
                assert!(
                    final_fee <= fee && fee <= previous,
                    "{label} {duration} {t}"
                );
                // Chord dominance holds for these two study factors only.
                assert!(fee <= linear(initial, final_fee, duration, t));
                previous = fee;
                let mut h = Sha256::new();
                h.update(chain);
                h.update(fee.to_be_bytes());
                chain = h.finalize().into();
                if count > 0 {
                    export.push_str(", ");
                }
                export.push_str(&format!(
                    "[\"{initial}\", \"{final_fee}\", \"{duration}\", \"{factor}\", \"{t}\", \"{fee}\"]"
                ));
                count += 1;
            }
            assert_eq!(previous, final_fee);
            let pinned = curve["all_second_digests_sha256"][duration.to_string()][label]
                .as_str()
                .unwrap();
            assert_eq!(hex(&chain), pinned, "{duration} {label}");
            digests += 1;
        }
    }
    export.push_str("]\n");
    assert_eq!(digests, 12);
    assert_eq!(count, PYTHON_EXPORT_ROWS);
    assert_eq!(
        hex(&Sha256::digest(export.as_bytes())),
        PYTHON_EXPORT_SHA256
    );
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

#[test]
fn fee_rows_half_life_fixture_and_saturation() {
    let v: Value = serde_json::from_str(VECTORS).unwrap();
    let fixture = &v["fixture"];
    for row in v["fee"].as_array().unwrap() {
        let duration = big(&row["duration"]) as u32;
        let schedule = ZeroSeedLaunchFeeSchedule {
            trading_start: big(&fixture["trading_start"]) as u64,
            fee_duration: duration,
            initial_fee: big(&fixture["fee_initial_q64"]) as u64,
            final_fee: big(&fixture["fee_final_q64"]) as u64,
            decay_factor: big(&row["decay_factor_q64"]) as u64,
        };
        let offset = row["t_minus_start"].as_i64().map_or_else(
            || i128::from(row["t_minus_start"].as_u64().unwrap()),
            i128::from,
        );
        // The largest offset is u64::MAX - start: elapsed saturates at the duration.
        let timestamp = u64::try_from(i128::from(schedule.trading_start) + offset).unwrap();
        assert_eq!(
            schedule.fee_at(timestamp),
            big(&row["fee_q64"]) as u64,
            "{row}"
        );
    }
    let half = &v["fee_curve"]["half_life_fixture"];
    let schedule = ZeroSeedLaunchFeeSchedule {
        trading_start: 0,
        fee_duration: big(&half["duration"]) as u32,
        initial_fee: big(&half["initial_q64"]) as u64,
        final_fee: big(&half["final_q64"]) as u64,
        decay_factor: big(&half["factor_q64"]) as u64,
    };
    assert_eq!(schedule.decay_factor, FACTOR_HALF_1800);
    assert_eq!(schedule.fee_duration, u32::MAX);
    for row in half["values"].as_array().unwrap() {
        assert_eq!(
            schedule.fee_at(big(&row["t"]) as u64),
            big(&row["fee_q64"]) as u64
        );
    }
    assert_eq!(schedule.fee_at(u64::MAX), schedule.final_fee);
}

/// Nearly flat factors where floor-rpow normalization lies above the integer linear chord. The
/// SDK must reproduce them, not "fix" them.
#[test]
fn documented_chord_counterexamples_reproduce() {
    let v: Value = serde_json::from_str(VECTORS).unwrap();
    let mut largest = 0;
    for row in v["fee_curve"]["integer_chord_exceptions"]["rows"]
        .as_array()
        .unwrap()
    {
        let (initial, final_fee) = (big(&row["initial"]) as u64, big(&row["final"]) as u64);
        let factor = big(&row["factor"]) as u64;
        let duration = big(&row["duration"]) as u32;
        let elapsed = big(&row["elapsed"]) as u64;
        let fee = decayed_fee(initial, final_fee, factor, duration, elapsed);
        let chord = linear(initial, final_fee, duration, elapsed);
        assert_eq!(fee, big(&row["exponential"]) as u64);
        assert_eq!(chord, big(&row["linear"]) as u64);
        assert_eq!(u128::from(fee - chord), big(&row["excess_q64"]));
        assert!(final_fee <= fee && fee <= initial);
        assert!(decayed_fee(initial, final_fee, factor, duration, elapsed + 1) <= fee);
        largest = largest.max(fee - chord);
    }
    assert_eq!(largest, 60_738_877);
}

/// Seeded sweep over the whole factor and `u32` duration domains, including values the contract
/// refuses (factor 0, rates above the cap): endpoints, boundedness and monotonicity, and the
/// widened reference. Chord dominance is deliberately not asserted here.
#[test]
fn seeded_domain_sweep_bounded_monotone_endpoints() {
    let mut rng = Rng(0x9e37_79b9_7f4a_7c15);
    let edge_factors = [0, 1, 2, 1 << 63, u64::MAX - 8, u64::MAX - 1, u64::MAX];
    let edge_durations = [1u32, 2, 3, 600, 3600, u32::MAX - 1, u32::MAX];
    for i in 0..20_000 {
        let factor = if i % 5 == 0 {
            edge_factors[(rng.next() % 7) as usize]
        } else {
            rng.next()
        };
        let duration = if i % 3 == 0 {
            edge_durations[(rng.next() % 7) as usize]
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
        let fee = decayed_fee(initial, final_fee, factor, duration, elapsed);
        assert_eq!(
            fee,
            reference_fee(initial, final_fee, factor, duration, elapsed)
        );
        assert!(final_fee <= fee && fee <= initial);
        assert!(decayed_fee(initial, final_fee, factor, duration, elapsed + 1) <= fee);
        assert_eq!(
            decayed_fee(initial, final_fee, factor, duration, 0),
            initial
        );
        assert_eq!(
            decayed_fee(initial, final_fee, factor, duration, u64::from(duration)),
            final_fee
        );
        let (x, y) = (
            rng.next() % (u64::from(u32::MAX) + 1),
            rng.next() % (u64::from(u32::MAX) + 1),
        );
        assert!(pow_q64(factor, x.max(y)) <= pow_q64(factor, x.min(y)));
        assert!(pow_q64(factor, x.max(1)) < Q);
    }
}

/// Validation: zero factor refused with `InvalidFeeSchedule`, the 99% cap accepted, one above and
/// the highest encodable rate refused with `FeeTooHigh`, the highest encodable factor accepted.
#[test]
fn validation_cap_and_zero_factor() {
    type E = ZeroSeedLaunchParameterError;
    assert_eq!(ZERO_SEED_LAUNCH_MAX_CREATOR_FEE as u128, 99 * Q / 100);
    let mut p = ZeroSeedLaunchParameters {
        quote_token: address(QUOTE_HIGH),
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
            decay_factor: FACTOR_3600,
        },
    };
    assert!(validate_launch_parameters_math(&p, START).is_ok());
    p.fee.decay_factor = u64::MAX;
    assert!(validate_launch_parameters_math(&p, START).is_ok());
    p.fee.decay_factor = 0;
    assert_eq!(
        validate_launch_parameters_math(&p, START),
        Err(E::InvalidFeeSchedule)
    );
    p.fee.decay_factor = FACTOR_3600;
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
/// (18/6) quote per token, spacing 100, both orders.
fn fixture(order: &str, decimals: &str, duration: u32, initial: u64, factor: u64) -> Fixture {
    let is1 = order == "t1";
    let ask = if decimals == "18/6" {
        -41_446_500
    } else {
        -13_815_500
    };
    let quote = address(if is1 { QUOTE_LOW } else { QUOTE_HIGH });
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
        decay_factor: factor,
    };
    let parameters = ZeroSeedLaunchParameters {
        quote_token: quote,
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

/// The contract's executed 50/75/90/99/max matrix, both orders, 18/18 and 18/6: one raw unit,
/// one whole unit exact-in, exact-out of that net, then selling everything held.
#[test]
fn high_rate_matrix_matches_executed_rows() {
    let rows = rows("highRate");
    assert_eq!(rows.len(), 100);
    let mut checked = 0;
    for chunk in rows.chunks(5) {
        let head = &chunk[0];
        let (label, order, dec) = (&head["rate"], &head["order"], &head["dec"]);
        let rate = rate_of(label);
        let f = fixture(order, dec, 3600, rate, FACTOR_3600);
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

/// Immediate 1e18 round trips at t = 0/1/10/60/600/3600, both curves at identical states. The
/// exponential rows use the SDK schedule; the linear comparator rows are quoted at their logged
/// rate, which the local linear formula reproduces.
#[test]
fn round_trips_match_executed_rows() {
    let rows = rows("roundTrip");
    assert_eq!(rows.len(), 36);
    for row in &rows {
        let t: u64 = n(row, "t");
        let rate: u64 = n(row, "rateQ64");
        let (initial, linear_duration, exp_duration, factor) = match row["pair"].as_str() {
            "I5-F03-D3600" => (FEE_5, 3600, 3600, FACTOR_3600),
            "I50-F03-D3600" => (RATE_50, 3600, 3600, FACTOR_3600),
            "I5-F03-halfLife1800" => (FEE_5, 3600, u32::MAX, FACTOR_HALF_1800),
            other => panic!("{other}"),
        };
        let f = if row["curve"] == "exponential" {
            let f = fixture("t0", "18/18", exp_duration, initial, factor);
            assert_eq!(f.pool.fee_at(START + t), rate, "{row:?}");
            f
        } else {
            assert_eq!(linear(initial, FEE_03, linear_duration, t), rate);
            fixture("t0", "18/18", 3600, rate, FACTOR_3600)
        };
        let at = if row["curve"] == "exponential" {
            START + t
        } else {
            START
        };
        let buy = swap(&f, f.pool.state(), f.quote, n(row, "quoteIn"), at).unwrap();
        assert_eq!(buy.calculated, n::<u128>(row, "net"), "{row:?}");
        assert_eq!(buy.fee, n::<u128>(row, "creatorTokenFee"));
        let sell = swap(&f, buy.state, f.token, buy.calculated as i128, at).unwrap();
        assert_eq!(sell.calculated, n::<u128>(row, "quoteOut"), "{row:?}");
        assert_eq!(sell.fee, n::<u128>(row, "creatorQuoteFee"));
        assert_eq!(
            1_000_000_000_000_000_000 - sell.calculated,
            n::<u128>(row, "loss")
        );
    }
}

/// Creator buying through a proxy and claiming versus an outsider: separate token and quote
/// ledgers, gross access, and a free round trip to one wei.
#[test]
fn creator_access_matches_executed_rows() {
    let rows = rows("creatorAccess");
    assert_eq!(rows.len(), 24);
    for row in &rows {
        let t: u64 = n(row, "t");
        let initial = if row["pair"] == "I50-F03-D3600" {
            RATE_50
        } else {
            FEE_5
        };
        let rate: u64 = n(row, "rateQ64");
        let (f, at) = if row["curve"] == "exponential" {
            let f = fixture("t0", "18/18", 3600, initial, FACTOR_3600);
            assert_eq!(f.pool.fee_at(START + t), rate);
            (f, START + t)
        } else {
            assert_eq!(linear(initial, FEE_03, 3600, t), rate);
            (fixture("t0", "18/18", 3600, rate, FACTOR_3600), START)
        };
        let unit = 1_000_000_000_000_000_000i128;
        let buy = swap(&f, f.pool.state(), f.quote, unit, at).unwrap();
        assert_eq!(buy.calculated, n::<u128>(row, "outsiderNet"));
        let outsider = swap(&f, buy.state, f.token, buy.calculated as i128, at).unwrap();
        assert_eq!(outsider.calculated, n::<u128>(row, "outsiderQuoteOut"));
        assert_eq!(buy.fee, n::<u128>(row, "creatorClaimedToken"));
        let gross = buy.calculated + buy.fee;
        assert_eq!(gross, n::<u128>(row, "creatorGross"));
        let creator = swap(&f, buy.state, f.token, gross as i128, at).unwrap();
        assert_eq!(creator.calculated, n::<u128>(row, "creatorQuoteOut"));
        assert_eq!(creator.fee, n::<u128>(row, "creatorClaimedQuote"));
        assert_eq!(
            creator.calculated + creator.fee,
            n::<u128>(row, "creatorQuoteTotal")
        );
    }
}

/// Exact-output representation limits: the uint128 helper bound and the signed int128 delta
/// bound per rate (pure), and both executed at the injected maximum rate with distinct errors.
#[test]
fn exact_output_helper_and_signed_bounds() {
    for row in rows("bounds") {
        let rate = rate_of(&row["rate"]);
        let helper: u128 = n(&row, "helperLastValid");
        let signed: u128 = n(&row, "signedLastValid");
        assert!(amount_before_fee::<Evm>(helper, rate).is_some());
        assert_eq!(amount_before_fee::<Evm>(helper + 1, rate), None);
        assert!(amount_before_fee::<Evm>(signed, rate).unwrap() <= i128::MAX as u128);
        assert!(amount_before_fee::<Evm>(signed + 1, rate).unwrap() > i128::MAX as u128);
    }

    let rows = rows("exactOutBounds");
    let f = fixture("t0", "18/18", 3600, RATE_MAX, FACTOR_3600);
    let state = f.pool.state();
    let signed = rows.iter().find(|r| r.contains_key("signed")).unwrap();
    let last: u128 = n(signed, "lastValidTokenOut");
    let q = swap(&f, state, f.token, -(last as i128), START).unwrap();
    assert_eq!(q.calculated, n::<u128>(signed, "paid"));
    assert_eq!(q.calculated - q.fee, n::<u128>(signed, "calcQuote"));
    assert_eq!(q.calculated, (q.calculated - q.fee) << 64);
    let first: u128 = n(signed, "firstInvalidTokenOut");
    assert_eq!(first, last + 1);
    assert_eq!(
        swap(&f, state, f.token, -(first as i128), START).err(),
        Some(ZeroSeedLaunchPoolQuoteError::Overflow)
    );
    let helper = rows.iter().find(|r| r.contains_key("helper")).unwrap();
    let last: u128 = n(helper, "lastSignedOverflowTokenOut");
    assert_eq!(
        swap(&f, state, f.token, -(last as i128), START).err(),
        Some(ZeroSeedLaunchPoolQuoteError::Overflow)
    );
    assert_eq!(
        swap(&f, state, f.token, -(last as i128) - 1, START).err(),
        Some(ZeroSeedLaunchPoolQuoteError::AmountBeforeFeeOverflow)
    );

    let whole = rows.iter().find(|r| r.contains_key("wholeSupply")).unwrap();
    let f = fixture(
        "t0",
        "18/18",
        3600,
        ZERO_SEED_LAUNCH_MAX_CREATOR_FEE,
        FACTOR_3600,
    );
    let supply = preview_installation_math(
        &ZeroSeedLaunchParameters {
            quote_token: f.quote,
            supply: 1_000_000_000_000_000_000_000_000_000,
            range: f.pool.launch().range,
            fee: f.pool.launch().fee,
        },
        START,
    )
    .unwrap()
    .installed_supply;
    let q = swap(&f, f.pool.state(), f.token, -(supply as i128), START).unwrap();
    assert_eq!(q.calculated, n::<u128>(whole, "paid"));
    assert_eq!(q.calculated - q.fee, n::<u128>(whole, "calcQuote"));
}

/// The deployed Yul router at the injected maximum rate: one wei quotes and fills zero (full-fill
/// quoting refuses it), one unit, a second unit, then a partial fill to the bound.
#[test]
fn router_max_rate_rows() {
    let rows = rows("routerMax");
    assert_eq!(rows.len(), 6);
    for order in ["t0", "t1"] {
        let f = fixture(order, "18/18", 3600, RATE_MAX, FACTOR_3600);
        let mine: Vec<_> = rows.iter().filter(|r| r["order"] == order).collect();
        let wei = swap(&f, f.pool.state(), f.quote, 1, START).unwrap();
        assert_eq!((wei.consumed, wei.calculated), (1, 0));
        assert_eq!(wei.fee, n::<u128>(mine[0], "creatorTokenFee"));
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
        let unit = swap(&f, wei.state, f.quote, n(mine[1], "paid"), START).unwrap();
        assert_eq!(unit.calculated, n::<u128>(mine[1], "got"));
        let second = swap(&f, unit.state, f.quote, n(mine[1], "paid"), START).unwrap();
        assert!(second.calculated < unit.calculated);
        let partial = swap(
            &f,
            second.state,
            f.quote,
            1_000_000_000_000_000_000_000_000_000_000,
            START,
        )
        .unwrap();
        assert_eq!(partial.consumed, n::<i128>(mine[2], "paid"));
        assert_eq!(partial.calculated, n::<u128>(mine[2], "got"));
    }
}
