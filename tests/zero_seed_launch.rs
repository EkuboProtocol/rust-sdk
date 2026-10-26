//! The final `ZeroSeedLaunch` (`evm-contracts@853b608`) against its frozen vectors, copied
//! verbatim into `tests/vectors/zero-seed-launch/` (see the README there for provenance).
#![cfg(any(feature = "evm-alloy-0_6", feature = "evm-alloy-1"))]

use core::str::FromStr;

use ekubo_sdk::{
    U256,
    alloy_primitives::{Address, B256, keccak256},
    chain::evm::Evm,
    math::{delta::amount0_delta, delta::amount1_delta, tick::to_sqrt_ratio},
    quoting::{
        pools::{
            concentrated::TickSpacing,
            zero_seed_launch::{
                LAUNCH_TOKEN_CREATION_CODE, LAUNCH_TOKEN_CREATION_CODE_KECCAK,
                ZERO_SEED_LAUNCH_DEFAULT_DECAY_RATE_X32, ZERO_SEED_LAUNCH_DEFAULT_FINAL_FEE,
                ZERO_SEED_LAUNCH_DEFAULT_INITIAL_FEE, ZERO_SEED_LAUNCH_MAX_CREATOR_FEE,
                ZERO_SEED_LAUNCH_MAX_DECAY_PRODUCT, ZERO_SEED_LAUNCH_MAX_SUPPLY,
                ZERO_SEED_LAUNCH_MAX_TICK_MAGNITUDE, ZERO_SEED_LAUNCH_MAX_TICK_SPACING,
                ZERO_SEED_LAUNCH_SKIP_AHEAD, ZeroSeedLaunchChainObservation, ZeroSeedLaunchConfig,
                ZeroSeedLaunchFeeSchedule, ZeroSeedLaunchInstance, ZeroSeedLaunchParameterError,
                ZeroSeedLaunchParameters, ZeroSeedLaunchPool, ZeroSeedLaunchPoolConstructionError,
                ZeroSeedLaunchPoolKey, ZeroSeedLaunchPoolQuoteError, ZeroSeedLaunchPoolState,
                ZeroSeedLaunchQuoteKind, ZeroSeedLaunchQuoteObservation, ZeroSeedLaunchRange,
                ZeroSeedLaunchReviewedQuote, align_launch_range, decay_rate_x32_for_half_life,
                decayed_fee, install_supply, is_canonical_launch_metadata, launch_token_address,
                launch_token_debit, max_liquidity_per_tick, pack_launch_metadata,
                preview_installation, saturation_elapsed_seconds, tick_rate_factor_q128,
                unpack_launch_metadata, validate_claim_recipient,
            },
        },
        types::{Pool, PoolConfig},
    },
};
use serde_json::Value;
use sha2::{Digest, Sha256};

const VECTORS: &str = include_str!("vectors/zero-seed-launch/zero-seed-launch.json");
const INSTALLATION: &str =
    include_str!("vectors/zero-seed-launch/zero-seed-launch-installation.json");
const EVENTS: &str = include_str!("vectors/zero-seed-launch/zero-seed-launch-events.json");

/// `tradingStart` of the contract fixture; its trades run at this timestamp.
const START: u64 = 1_000;
/// 5%: `fixture.fee_initial_q64`.
const FEE_5: u64 = 922_337_203_685_477_580;
const FEE_03: u64 = 55_340_232_221_128_654;

fn json(source: &str) -> Value {
    serde_json::from_str(source).unwrap()
}

fn s<'a>(v: &'a Value, key: &str) -> &'a str {
    v[key]
        .as_str()
        .unwrap_or_else(|| panic!("{key} is not a string in {v}"))
}

fn u128_of(v: &Value, key: &str) -> u128 {
    u128::from_str(s(v, key)).unwrap()
}

fn u64_of(v: &Value, key: &str) -> u64 {
    u64::from_str(s(v, key)).unwrap()
}

fn i32_of(v: &Value, key: &str) -> i32 {
    match &v[key] {
        Value::String(text) => i32::from_str(text).unwrap(),
        number => i32::try_from(number.as_i64().unwrap()).unwrap(),
    }
}

fn u256_of(v: &Value, key: &str) -> U256 {
    U256::from_str(s(v, key)).unwrap()
}

fn sha256_hex(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect()
}

#[test]
fn vendored_vectors_and_creation_code_match_their_pins() {
    for (bytes, digest) in [
        (
            VECTORS.as_bytes(),
            "e5444bf6b1f7e422238331b50b64cf0400597bd13421e281615735511274190b",
        ),
        (
            INSTALLATION.as_bytes(),
            "5cf44854cbf00abb700936b2e22782c27dac5e68cf892edc8f5aa7090067a555",
        ),
        (
            EVENTS.as_bytes(),
            "24dd5883ce242ec523517c9f38cfd5e8ca29740974aeded5740ac3608e1e7066",
        ),
    ] {
        assert_eq!(sha256_hex(bytes), digest);
    }
    let v = json(VECTORS);
    assert_eq!(v["version"], 8);
    let pin = &v["pins"]["creationCode"]["LaunchToken"];
    assert_eq!(pin["bytes"], LAUNCH_TOKEN_CREATION_CODE.len());
    let keccak = format!("{:#x}", keccak256(LAUNCH_TOKEN_CREATION_CODE));
    assert_eq!(keccak, s(pin, "keccak256"));
    assert_eq!(keccak, LAUNCH_TOKEN_CREATION_CODE_KECCAK);
    assert_eq!(
        json(INSTALLATION)["pins"]["creationCode"]["LaunchToken"],
        *pin
    );
}

// ---------------------------------------------------------------------------------------------
// Fees
// ---------------------------------------------------------------------------------------------

fn schedule(initial_fee: u64, final_fee: u64, decay_rate_x32: u64) -> ZeroSeedLaunchFeeSchedule {
    ZeroSeedLaunchFeeSchedule {
        trading_start: START,
        decay_rate_x32,
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
    fee.fee_at(START + elapsed.min(U256::from(u64::MAX - START)).to::<u64>())
}

fn assert_magnitude(rate: u64, row: &Value) {
    let t = s(row, "t").trim_start_matches('-');
    if let Some(m) = row["tick_magnitude"].as_str() {
        let t = u64::from_str(t).unwrap();
        assert_eq!(
            (u128::from(rate) * u128::from(t)) >> 32,
            u128::from_str(m).unwrap(),
            "{row}"
        );
        assert!(t <= ZERO_SEED_LAUNCH_MAX_DECAY_PRODUCT / rate);
    }
}

#[test]
fn fee_rows_match_the_contract() {
    let v = json(VECTORS);
    let rows = v["fee"].as_array().unwrap();
    assert_eq!(rows.len(), 40);
    for row in rows {
        let rate = u64_of(row, "decayRateX32");
        let fee = schedule(FEE_5, FEE_03, rate);
        let t = s(row, "t_minus_start");
        assert_eq!(fee_at_elapsed(&fee, t), u64_of(row, "fee_q64"), "{row}");
        let mut with_t = row.clone();
        with_t["t"] = Value::String(t.to_owned());
        if !t.starts_with('-') && t != "0" {
            assert_magnitude(rate, &with_t);
        }
        if row["tick_magnitude"].is_null() && !t.starts_with('-') && t != "0" {
            assert_eq!(fee_at_elapsed(&fee, t), FEE_03, "saturated: {row}");
        }
    }
}

#[test]
fn fee_curve_tables_digests_and_steps() {
    let v = json(VECTORS);
    let curve = &v["fee_curve"];
    let rate = |name: &str| u64_of(&curve["decay_rates_x32"], name);
    let fee_of = |name: &str| u64_of(&curve["rates_q64"], name);
    assert_eq!(
        u64_of(curve, "final_fee_q64"),
        ZERO_SEED_LAUNCH_DEFAULT_FINAL_FEE
    );
    let tables = [
        (
            "default_one_day_50_to_0.3",
            fee_of("50"),
            FEE_03,
            rate("default_one_day"),
        ),
        (
            "two_ticks_per_second_50_to_0.3",
            fee_of("50"),
            FEE_03,
            rate("two_ticks_per_second"),
        ),
        (
            "two_ticks_per_second_99.9_to_0",
            fee_of("99.9"),
            0,
            rate("two_ticks_per_second"),
        ),
        (
            "default_one_day_max_to_0",
            fee_of("max"),
            0,
            rate("default_one_day"),
        ),
        ("min_rate_max_to_0", fee_of("max"), 0, rate("min")),
    ];
    assert_eq!(tables.len(), curve["tables"].as_object().unwrap().len());
    for (name, initial, final_fee, decay) in tables {
        let fee = schedule(initial, final_fee, decay);
        for row in curve["tables"][name].as_array().unwrap() {
            assert_eq!(
                fee_at_elapsed(&fee, s(row, "t")),
                u64_of(row, "fee_q64"),
                "{name} {row}"
            );
            if s(row, "t") != "0" {
                assert_magnitude(decay, row);
            }
        }
    }

    for digest in curve["digests_sha256"].as_array().unwrap() {
        let fee = schedule(
            u64_of(digest, "initialFee"),
            u64_of(digest, "finalFee"),
            u64_of(digest, "decayRateX32"),
        );
        let last = digest["last"].as_u64().unwrap();
        let step = digest["step"].as_u64().unwrap();
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
        assert_eq!(hex, s(digest, "digest"), "{}", s(digest, "label"));
    }

    for group in curve["tick_steps"].as_array().unwrap() {
        let decay = u64_of(group, "decayRateX32");
        let rows = group["rows"].as_array().unwrap();
        // The one-unit-excess group starts at t = 0 with the floor plus one.
        let initial = rows
            .iter()
            .find(|row| s(row, "t") == "0")
            .map_or(ZERO_SEED_LAUNCH_DEFAULT_INITIAL_FEE, |row| {
                u64_of(row, "fee_q64")
            });
        let fee = schedule(initial, FEE_03, decay);
        for row in rows {
            assert_eq!(
                fee_at_elapsed(&fee, s(row, "t")),
                u64_of(row, "fee_q64"),
                "{row}"
            );
            if s(row, "t") != "0" {
                assert_magnitude(decay, row);
            }
        }
    }

    for (name, second) in curve["saturation_second"].as_object().unwrap() {
        let decay = rate(name);
        let second = u64::from_str(second.as_str().unwrap()).unwrap();
        assert_eq!(saturation_elapsed_seconds(decay), Some(second), "{name}");
        // From the next second the fee is exactly the floor, even for a full-span excess.
        assert_eq!(
            decayed_fee(u64::MAX, 0, decay, second + 1),
            0,
            "{name} saturates"
        );
    }
    // The slowest rate leaves one raw unit at the last evaluated second.
    assert_eq!(
        decayed_fee(u64::MAX, 0, 1, ZERO_SEED_LAUNCH_MAX_DECAY_PRODUCT),
        1
    );
    assert_eq!(ZERO_SEED_LAUNCH_MAX_DECAY_PRODUCT, 381_061_679_028_371_455);
    assert_eq!(saturation_elapsed_seconds(0), None);
    assert_eq!(tick_rate_factor_q128(0), Some(U256::from(1) << 128));
    assert_eq!(
        tick_rate_factor_q128(ZERO_SEED_LAUNCH_MAX_TICK_MAGNITUDE + 1),
        None
    );

    assert_eq!(
        decay_rate_x32_for_half_life(86_400),
        Some(rate("default_one_day"))
    );
    assert_eq!(
        rate("default_one_day"),
        ZERO_SEED_LAUNCH_DEFAULT_DECAY_RATE_X32
    );
    assert_eq!(decay_rate_x32_for_half_life(600), Some(rate("600s")));
    assert_eq!(decay_rate_x32_for_half_life(0), None);

    let consumer = &v["creator_fee_range"]["reference_schedules"]["consumer_default"];
    let fee = schedule(
        u64_of(consumer, "initialFee"),
        u64_of(consumer, "finalFee"),
        u64_of(consumer, "decayRateX32"),
    );
    assert_eq!(fee.initial_fee, ZERO_SEED_LAUNCH_DEFAULT_INITIAL_FEE);
    assert_eq!(fee.final_fee, ZERO_SEED_LAUNCH_DEFAULT_FINAL_FEE);
    assert_eq!(fee.decay_rate_x32, ZERO_SEED_LAUNCH_DEFAULT_DECAY_RATE_X32);
    assert_eq!(
        fee.fee_at(START + 86_400),
        u64_of(consumer, "fee_after_one_day_q64")
    );
}

#[test]
fn creator_fee_range_verdicts() {
    let v = json(VECTORS);
    let range = &v["creator_fee_range"];
    assert_eq!(u64_of(range, "max_q64"), ZERO_SEED_LAUNCH_MAX_CREATOR_FEE);
    let vectors = range["vectors"].as_array().unwrap();
    assert_eq!(vectors.len(), 13);
    for row in vectors {
        let parsed = (
            u64::from_str(s(row, "initialFee")),
            u64::from_str(s(row, "finalFee")),
            u64::from_str(s(row, "decayRateX32")),
        );
        match (s(row, "verdict"), parsed) {
            ("abi_decoding_failure", parsed) => {
                assert!(
                    parsed.0.is_err() || parsed.1.is_err() || parsed.2.is_err(),
                    "{row}"
                );
            }
            (verdict, (Ok(initial), Ok(final_fee), Ok(decay))) => {
                let parameters = parameters_for(initial, final_fee, decay);
                let expected = match verdict {
                    "accept" => Ok(()),
                    "InvalidFeeSchedule" => Err(ZeroSeedLaunchParameterError::InvalidFeeSchedule),
                    other => panic!("unknown verdict {other}"),
                };
                assert_eq!(parameters.validate(START), expected, "{row}");
            }
            _ => panic!("{row}"),
        }
    }
    for value in [
        s(&range["unencodable"], "value"),
        s(&range["unencodable"]["dirty_high_bits"], "value"),
    ] {
        assert!(u64::from_str(value).is_err());
    }
}

fn parameters_for(
    initial_fee: u64,
    final_fee: u64,
    decay_rate_x32: u64,
) -> ZeroSeedLaunchParameters {
    ZeroSeedLaunchParameters {
        name: pack_launch_metadata(b"Zero Seed").unwrap(),
        symbol: pack_launch_metadata(b"ZERO").unwrap(),
        supply: 1_000_000_000_000_000_000_000_000_000,
        quote_token: Address::ZERO,
        ask_tick: -13_815_500,
        upper_tick: -9_210_300,
        trading_start: START,
        decay_rate_x32,
        initial_fee,
        final_fee,
        salt: B256::ZERO,
    }
}

// ---------------------------------------------------------------------------------------------
// Spacing and installation
// ---------------------------------------------------------------------------------------------

#[test]
fn spacing_table_of_the_specification() {
    for (ask, upper, spacing, aligned_ask, aligned_upper) in [
        (-13_815_500, -9_210_300, 17_990, -13_798_330, -9_210_880),
        (-41_446_500, -36_841_300, 17_990, -41_430_970, -36_843_520),
        (-88_722_835, 88_722_835, 693_148, -88_029_796, 88_029_796),
        (-88_722_835, -88_722_834, 1, -88_722_835, -88_722_834),
        (60_000_000, 70_000_000, 39_063, 60_000_768, 69_961_833),
        (-70_000_000, -60_000_000, 39_063, -69_961_833, -60_000_768),
        (-5_000_001, 4_999_999, 39_063, -4_961_001, 4_961_001),
    ] {
        assert_eq!(
            align_launch_range(ask, upper),
            Ok((spacing, aligned_ask, aligned_upper)),
            "{ask} -> {upper}"
        );
    }
    let v = json(VECTORS);
    assert_eq!(
        v["spacing"]["max"].as_u64().unwrap(),
        u64::from(ZERO_SEED_LAUNCH_MAX_TICK_SPACING)
    );
    assert_eq!(
        v["spacing"]["skipAhead"].as_u64().unwrap(),
        u64::from(ZERO_SEED_LAUNCH_SKIP_AHEAD)
    );
    assert_eq!(u128_of(&v["supply"], "max"), ZERO_SEED_LAUNCH_MAX_SUPPLY);
    for (ask, upper) in [
        (0, 0),
        (1, 0),
        (-88_722_836, 0),
        (0, 88_722_836),
        (i32::MIN, i32::MAX),
    ] {
        assert_eq!(
            align_launch_range(ask, upper),
            Err(ZeroSeedLaunchParameterError::InvalidTicks)
        );
    }
    // Every width keeps the aligned range inside the request, within 256 steps.
    for (ask, upper) in [
        (-1, 0),
        (-257, 0),
        (255, 512),
        (-88_722_835, 88_722_835),
        (7, 7_000_007),
    ] {
        let (spacing, a, u) = align_launch_range(ask, upper).unwrap();
        assert!(ask <= a && a < u && u <= upper);
        assert!(i64::from(u - a) / i64::from(spacing) <= 256);
        assert!(a - ask < spacing as i32 && upper - u < spacing as i32);
    }
}

fn order_is_token1(row: &Value) -> bool {
    match s(row, "order") {
        "t0" => false,
        "t1" => true,
        other => panic!("unknown order {other}"),
    }
}

fn refusal(name: &str) -> fn(&ZeroSeedLaunchParameterError) -> bool {
    match name {
        "InvalidSupply" => |e| *e == ZeroSeedLaunchParameterError::InvalidSupply,
        "InvalidTicks" => |e| *e == ZeroSeedLaunchParameterError::InvalidTicks,
        "ZeroLiquidity" => |e| *e == ZeroSeedLaunchParameterError::ZeroLiquidity,
        "LiquidityAboveTickCap" => |e| {
            matches!(
                e,
                ZeroSeedLaunchParameterError::LiquidityAboveTickCap { .. }
            )
        },
        other => panic!("unknown refusal {other}"),
    }
}

#[test]
fn installation_rows_match_the_oracle() {
    let v = json(INSTALLATION);
    let rows = v["vectors"].as_array().unwrap();
    assert_eq!(rows.len(), 64);
    let mut refused = 0;
    for row in rows {
        let token1 = order_is_token1(row);
        let (ask, upper) = (i32_of(row, "askTick"), i32_of(row, "upperTick"));
        // The supply is the contract's uint128; above it the row would fail ABI decoding.
        let supply = u128_of(row, "supply");
        let ranged = ZeroSeedLaunchRange::from_requested(token1, ask, upper);
        let error = row["error"].as_str();
        if row.get("tickSpacing").is_none() {
            // Refused before the geometry: supply or ticks, in the contract's order.
            let is = refusal(error.unwrap());
            let result = if supply == 0 || supply > ZERO_SEED_LAUNCH_MAX_SUPPLY {
                Err(ZeroSeedLaunchParameterError::InvalidSupply)
            } else {
                ranged.map(|_| ())
            };
            assert!(result.as_ref().is_err_and(is), "{row}: {result:?}");
            refused += 1;
            continue;
        }
        let range = ranged.unwrap();
        assert_eq!(
            range.tick_spacing,
            row["tickSpacing"].as_u64().unwrap() as u32
        );
        assert_eq!(range.ask_tick, i32_of(row, "alignedAskTick"));
        assert_eq!(range.upper_tick, i32_of(row, "alignedUpperTick"));
        assert_eq!(range.validate(), Ok(()));
        let spacing = i64::from(range.tick_spacing);
        assert_eq!(
            (i64::from(range.upper_tick) - i64::from(range.ask_tick)) / spacing,
            row["steps"].as_i64().unwrap()
        );
        let (lower, upper_tick) = range.pool_bounds();
        assert_eq!(
            (lower, upper_tick),
            (i32_of(row, "tickLower"), i32_of(row, "tickUpper"))
        );
        assert_eq!(range.initial_tick(), i32_of(row, "initialTick"));
        let word = |tick: i32| (i64::from(tick).div_euclid(spacing) + 89_421_695) >> 8;
        assert_eq!(
            1 + (word(upper_tick) - word(lower)),
            row["bitmapWords"].as_i64().unwrap()
        );
        assert_eq!(
            to_sqrt_ratio::<Evm>(lower).unwrap(),
            u256_of(row, "lowerFixed")
        );
        assert_eq!(
            to_sqrt_ratio::<Evm>(upper_tick).unwrap(),
            u256_of(row, "upperFixed")
        );
        let cap = max_liquidity_per_tick(range.tick_spacing);
        assert_eq!(cap, u128_of(row, "tickCap"));
        let envelope = &row["supplyEnvelope"];
        let minimum = launch_token_debit(&range, U256::from(1));
        assert_eq!(minimum.to_string(), s(envelope, "minimum"));
        let above_cap = launch_token_debit(&range, U256::from(cap) + U256::from(1));
        let maximum = (above_cap - ruint::aliases::U512::from(1))
            .min(ruint::aliases::U512::from(ZERO_SEED_LAUNCH_MAX_SUPPLY));
        assert_eq!(maximum.to_string(), s(envelope, "maximum"));
        assert_eq!(envelope["nonempty"].as_bool().unwrap(), minimum <= maximum);

        let result = install_supply(&range, supply);
        if let Some(error) = error {
            assert!(
                result.as_ref().is_err_and(refusal(error)),
                "{row}: {result:?}"
            );
            if let (
                Err(ZeroSeedLaunchParameterError::LiquidityAboveTickCap { liquidity, cap: c }),
                Some(_),
            ) = (result, row.get("liquidity"))
            {
                assert_eq!(liquidity, u128_of(row, "liquidity"));
                assert_eq!(c, cap);
            }
            refused += 1;
            continue;
        }
        let installation = result.unwrap();
        assert_eq!(installation.liquidity, u128_of(row, "liquidity"), "{row}");
        assert_eq!(
            installation.installed_supply,
            u128_of(row, "installedSupply")
        );
        assert_eq!(installation.sink_supply, u128_of(row, "sink"));
        assert_eq!(
            U256::from(installation.installed_supply),
            launch_token_debit(&range, U256::from(installation.liquidity)).to::<U256>()
        );
        let next = launch_token_debit(&range, U256::from(installation.liquidity) + U256::from(1));
        assert_eq!(next.to_string(), s(row, "debitAtLiquidityPlusOne"));
        assert!(next > ruint::aliases::U512::from(supply));
    }
    assert_eq!(refused, 27);
}

/// The four creations of the trade fixture: requested 1e27 at the default range (18/18) and its
/// 6-decimal-quote counterpart (18/6), in both token orders.
#[test]
fn create_rows_match_the_contract() {
    let v = json(VECTORS);
    for row in v["create"].as_array().unwrap() {
        let range = ZeroSeedLaunchRange::from_requested(
            order_is_token1(row),
            i32_of(row, "ask"),
            i32_of(row, "upper"),
        )
        .unwrap();
        assert_eq!(range.tick_spacing.to_string(), s(row, "spacing"));
        assert_eq!(range.ask_tick, i32_of(row, "alignedAsk"));
        assert_eq!(range.upper_tick, i32_of(row, "alignedUpper"));
        let installation = install_supply(&range, u128_of(row, "requested")).unwrap();
        assert_eq!(installation.installed_supply, u128_of(row, "installed"));
        assert_eq!(installation.liquidity, u128_of(row, "liquidity"));
        assert_eq!(installation.tick_lower, i32_of(row, "tickLower"));
        assert_eq!(installation.tick_upper, i32_of(row, "tickUpper"));
        assert_eq!(installation.initial_tick, i32_of(row, "initialTick"));
        // The position's own withdrawable amount rounds down: one unit below the debit.
        let pool = launch(&range, installation.liquidity, FEE_5, 0);
        let (token, _) = principal(&pool.pool, pool.pool.state());
        assert_eq!(token, u128_of(row, "withdrawable"));
    }
}

// ---------------------------------------------------------------------------------------------
// Trades
// ---------------------------------------------------------------------------------------------

struct Launch {
    pool: ZeroSeedLaunchPool,
    /// Quote address of the synthetic pool key.
    quote: Address,
}

const LAUNCH_TOKEN: Address = Address::repeat_byte(0x11);

/// A launch at its installed state, with the fixture's ordering: a token0 launch quotes an ERC-20
/// above it, a token1 launch native ETH.
fn launch(
    range: &ZeroSeedLaunchRange,
    liquidity: u128,
    initial_fee: u64,
    final_fee: u64,
) -> Launch {
    let (token, quote) = if range.launch_token_is_token1 {
        (LAUNCH_TOKEN, Address::ZERO)
    } else {
        (LAUNCH_TOKEN, Address::repeat_byte(0xff))
    };
    let (token0, token1) = if range.launch_token_is_token1 {
        (quote, token)
    } else {
        (token, quote)
    };
    let tick = range.initial_tick();
    let in_range = !range.launch_token_is_token1;
    let pool = ZeroSeedLaunchPool::new_math(
        ZeroSeedLaunchPoolKey {
            token0,
            token1,
            config: PoolConfig {
                extension: Address::repeat_byte(0x51),
                fee: 0,
                pool_type_config: TickSpacing(range.tick_spacing),
            },
        },
        ZeroSeedLaunchConfig {
            quote_token: quote,
            range: *range,
            liquidity,
            fee: ZeroSeedLaunchFeeSchedule {
                trading_start: START,
                decay_rate_x32: ZERO_SEED_LAUNCH_DEFAULT_DECAY_RATE_X32,
                initial_fee,
                final_fee,
            },
        },
        ZeroSeedLaunchPoolState {
            sqrt_ratio: to_sqrt_ratio::<Evm>(tick).unwrap(),
            tick,
            liquidity: if in_range { liquidity } else { 0 },
        },
    )
    .unwrap();
    Launch { pool, quote }
}

/// The position's principal at `state`, rounded down as a withdrawal would: (launch token, quote).
fn principal(pool: &ZeroSeedLaunchPool, state: ZeroSeedLaunchPoolState) -> (u128, u128) {
    let range = pool.launch().range;
    let liquidity = pool.launch().liquidity;
    let (lower, upper) = range.pool_bounds();
    let (lower, upper) = (
        to_sqrt_ratio::<Evm>(lower).unwrap(),
        to_sqrt_ratio::<Evm>(upper).unwrap(),
    );
    let price = state.sqrt_ratio.clamp(lower, upper);
    let amount0 = amount0_delta(price, upper, liquidity, false).unwrap();
    let amount1 = amount1_delta(lower, price, liquidity, false).unwrap();
    if range.launch_token_is_token1 {
        (amount1, amount0)
    } else {
        (amount0, amount1)
    }
}

/// A trading account replaying forwarded swaps against one launch at block timestamp `START`.
struct Trader<'a> {
    launch: &'a Launch,
    state: ZeroSeedLaunchPoolState,
    held: u128,
    quote_in: u128,
    quote_out: u128,
    fee_token: u128,
    fee_quote: u128,
}

/// One swap's launch-token and quote deltas from the pool's side and its creator fee.
struct Fill {
    token: i128,
    quote: i128,
    fee: u128,
}

impl<'a> Trader<'a> {
    fn new(launch: &'a Launch) -> Self {
        Self {
            launch,
            state: launch.pool.state(),
            held: 0,
            quote_in: 0,
            quote_out: 0,
            fee_token: 0,
            fee_quote: 0,
        }
    }

    fn try_swap(
        &mut self,
        specified_is_token: bool,
        amount: i128,
    ) -> Result<Fill, ZeroSeedLaunchPoolQuoteError> {
        let token_is_token1 = self.launch.pool.launch().range.launch_token_is_token1;
        let is_token1 = specified_is_token == token_is_token1;
        let swap = self
            .launch
            .pool
            .simulate_swap(self.state, amount, is_token1, None, START)?;
        self.state = swap.state_after;
        let (token, quote) = if token_is_token1 {
            (swap.delta1, swap.delta0)
        } else {
            (swap.delta0, swap.delta1)
        };
        if swap.fee_is_token1 == token_is_token1 {
            self.fee_token += swap.fee_amount;
        } else {
            self.fee_quote += swap.fee_amount;
        }
        self.held = (self.held as i128 - token) as u128;
        if quote > 0 {
            self.quote_in += quote as u128;
        } else {
            self.quote_out += quote.unsigned_abs();
        }
        Ok(Fill {
            token,
            quote,
            fee: swap.fee_amount,
        })
    }

    fn swap(&mut self, specified_is_token: bool, amount: i128) -> Fill {
        self.try_swap(specified_is_token, amount).unwrap()
    }

    fn principal(&self) -> (u128, u128) {
        principal(&self.launch.pool, self.state)
    }

    /// Core's unbooked rounding dust: Core's balances minus the position and the fee ledger.
    fn dust(&self, installed: u128) -> (u128, u128) {
        let (token, quote) = self.principal();
        (
            installed - self.held - token - self.fee_token,
            self.quote_in - self.quote_out - quote - self.fee_quote,
        )
    }
}

fn step<'a>(rows: &'a [Value], order: &str, dec: &str, name: &str) -> &'a Value {
    rows.iter()
        .find(|row| s(row, "order") == order && s(row, "dec") == dec && s(row, "step") == name)
        .unwrap_or_else(|| panic!("no {order} {dec} {name}"))
}

fn fixture_launch(
    v: &Value,
    order: &str,
    dec: &str,
    initial_fee: u64,
    final_fee: u64,
) -> (Launch, u128) {
    let row = v["create"]
        .as_array()
        .unwrap()
        .iter()
        .find(|row| s(row, "order") == order && s(row, "dec") == dec)
        .unwrap();
    let range = ZeroSeedLaunchRange::from_requested(
        order_is_token1(row),
        i32_of(row, "ask"),
        i32_of(row, "upper"),
    )
    .unwrap();
    let installation = install_supply(&range, u128_of(row, "requested")).unwrap();
    (
        launch(&range, installation.liquidity, initial_fee, final_fee),
        installation.installed_supply,
    )
}

const ORDERS: [(&str, &str, u32); 4] = [
    ("t0", "18/18", 18),
    ("t0", "18/6", 6),
    ("t1", "18/18", 18),
    ("t1", "18/6", 6),
];

#[test]
fn trade_programs_replay_swap_by_swap() {
    let v = json(VECTORS);
    let rows = v["trade"].as_array().unwrap();
    assert_eq!(rows.len(), 32);
    for (order, dec, decimals) in ORDERS {
        let (launch, installed) = fixture_launch(&v, order, dec, FEE_5, FEE_03);
        let mut trader = Trader::new(&launch);
        let unit = 10i128.pow(decimals);

        // Sell before any buy: no bid, zero fill, no fee, nothing moves.
        let before = trader.state;
        let fill = trader.swap(true, 1);
        assert_eq!((fill.token, fill.quote, fill.fee), (0, 0, 0));
        assert_eq!(trader.state, before);

        let row = step(rows, order, dec, "buyExactIn");
        let fill = trader.swap(false, unit);
        assert_eq!(fill.quote, unit);
        let net = fill.token.unsigned_abs();
        assert_eq!(net, u128_of(row, "net"), "{row}");
        assert_eq!(fill.fee, u128_of(row, "fee"));
        assert_eq!(net + fill.fee, u128_of(row, "gross"));

        let row = step(rows, order, dec, "buyExactOut");
        let fill = trader.swap(true, -(u128_of(row, "tokenOut") as i128));
        assert_eq!(fill.token, -(u128_of(row, "tokenOut") as i128));
        assert_eq!(fill.quote as u128, u128_of(row, "paid"), "{row}");
        assert_eq!(fill.fee, u128_of(row, "fee"));
        assert_eq!(fill.quote as u128 - fill.fee, u128_of(row, "calcQuote"));

        let row = step(rows, order, dec, "sellExactIn");
        let half = trader.held / 2;
        assert_eq!(half, u128_of(row, "tokenIn"));
        let fill = trader.swap(true, half as i128);
        assert_eq!(fill.quote.unsigned_abs(), u128_of(row, "quoteOut"), "{row}");

        // Reverse to the ask: everything held is sold, the rest fills nothing.
        let row = step(rows, order, dec, "reverse");
        let held = trader.held;
        trader.swap(true, held as i128);
        if trader.held > 0 {
            let left = trader.held;
            trader.swap(true, left as i128);
        }
        assert_eq!(trader.held, u128_of(row, "leftHeld"));
        let (token, quote) = trader.principal();
        assert_eq!(token, u128_of(row, "principalToken"), "{row}");
        assert_eq!(quote, u128_of(row, "principalQuote"));
        let row = step(rows, order, dec, "dust");
        assert_eq!(
            trader.dust(installed),
            (u128_of(row, "token"), u128_of(row, "quote")),
            "{row}"
        );

        // Upper exhaustion: an exact-output buy above the inventory fills to the upper bound.
        let row = step(rows, order, dec, "exhaust");
        let remaining = trader.principal().0;
        let requested = remaining + 1_000_000_000_000_000_000;
        assert_eq!(requested, u128_of(row, "requested"));
        let fill = trader.swap(true, -(requested as i128));
        assert_eq!(fill.token.unsigned_abs(), u128_of(row, "got"), "{row}");
        let range = launch.pool.launch().range;
        let (lower, upper) = range.pool_bounds();
        let bound = if range.launch_token_is_token1 {
            lower
        } else {
            upper
        };
        assert_eq!(
            trader.state.sqrt_ratio,
            to_sqrt_ratio::<Evm>(bound).unwrap()
        );
        // Further buys fill nothing and pay nothing.
        let fill = trader.swap(false, unit);
        assert_eq!((fill.token, fill.quote, fill.fee), (0, 0, 0));
        let (token, quote) = trader.principal();
        assert_eq!(token, u128_of(row, "principalToken"));
        assert_eq!(quote, u128_of(row, "principalQuote"));

        let row = step(rows, order, dec, "upperResidue");
        assert_eq!(remaining, u128_of(row, "positionTokenBefore"));
        assert_eq!(
            remaining - u128_of(row, "delivered"),
            u128_of(row, "residueToken")
        );
        let row = step(rows, order, dec, "dustExhausted");
        assert_eq!(
            trader.dust(installed),
            (u128_of(row, "token"), u128_of(row, "quote"))
        );
    }

    for row in v["router"].as_array().unwrap() {
        let (launch, _) = fixture_launch(&v, s(row, "order"), "18/18", FEE_5, FEE_03);
        let mut trader = Trader::new(&launch);
        let fill = trader.swap(false, u128_of(row, "paid") as i128);
        assert_eq!(fill.token.unsigned_abs(), u128_of(row, "got"));
    }

    // `VEC|dust|t0|quoteIn=1|net=933793|fee=49148`.
    let (launch, _) = fixture_launch(&v, "t0", "18/18", FEE_5, FEE_03);
    let mut trader = Trader::new(&launch);
    let fill = trader.swap(false, 1);
    assert_eq!((fill.token.unsigned_abs(), fill.fee), (933_793, 49_148));
    assert!(
        v["other"]
            .as_array()
            .unwrap()
            .iter()
            .any(|o| s(o, "raw") == "VEC|dust|t0|quoteIn=1|net=933793|fee=49148")
    );
}

#[test]
fn maximum_rate_trades_and_exact_output_bounds() {
    let v = json(VECTORS);
    let max_rate = &v["max_rate"];
    let rows = max_rate["trades"].as_array().unwrap();
    assert_eq!(rows.len(), 16);
    for (order, dec, decimals) in ORDERS {
        let (launch, _) = fixture_launch(&v, order, dec, u64::MAX, FEE_03);
        let mut trader = Trader::new(&launch);

        let row = step(rows, order, dec, "oneUnit");
        let fill = trader.swap(false, 1);
        assert_eq!(fill.token, 0, "{row}");
        assert_eq!(fill.fee, u128_of(row, "fee"));
        assert_eq!(fill.fee, u128_of(row, "gross"));

        let row = step(rows, order, dec, "buyExactIn");
        let fill = trader.swap(false, 10i128.pow(decimals));
        let net = fill.token.unsigned_abs();
        assert_eq!(net, u128_of(row, "net"), "{row}");
        assert_eq!(fill.fee, u128_of(row, "fee"));
        assert_eq!(net + fill.fee, u128_of(row, "gross"));

        let row = step(rows, order, dec, "buyExactOut");
        let fill = trader.swap(true, -(net as i128));
        assert_eq!(fill.quote as u128, u128_of(row, "paid"), "{row}");
        assert_eq!(fill.fee, u128_of(row, "fee"));
        assert_eq!(fill.quote as u128 - fill.fee, u128_of(row, "calcQuote"));

        let row = step(rows, order, dec, "sellAll");
        let held = trader.held;
        assert_eq!(held, u128_of(row, "tokenIn"));
        let fill = trader.swap(true, held as i128);
        assert_eq!(fill.quote.unsigned_abs(), u128_of(row, "quoteOut"), "{row}");
        assert_eq!(fill.fee, u128_of(row, "fee"));
        assert_eq!(
            trader.quote_in - trader.quote_out,
            u128_of(row, "roundTripLoss")
        );
    }

    let bounds = &max_rate["exact_output_bounds"];
    let signed = u128_of(bounds, "signed_bound_calc");
    assert_eq!(signed, (i128::MAX as u128) >> 64);
    for row in bounds["vectors"].as_array().unwrap() {
        let order = if s(row, "order") == "t0" { "t0" } else { "t1" };
        let (launch, _) = fixture_launch(&v, order, "18/18", u64::MAX, FEE_03);
        let probe = |out: u128| Trader::new(&launch).try_swap(true, -(out as i128));
        let fill = probe(u128_of(row, "lastValidTokenOut")).unwrap();
        assert_eq!(fill.quote as u128, u128_of(row, "paid"), "{row}");
        assert_eq!(fill.quote as u128 - fill.fee, u128_of(row, "calc"));
        assert_eq!(u128_of(row, "calc"), signed);
        for out in ["firstSignedOverflowTokenOut", "lastSignedOverflowTokenOut"] {
            assert_eq!(
                probe(u128_of(row, out)).err(),
                Some(ZeroSeedLaunchPoolQuoteError::Overflow),
                "{out}"
            );
        }
        assert_eq!(
            probe(u128_of(row, "firstHelperOverflowTokenOut")).err(),
            Some(ZeroSeedLaunchPoolQuoteError::AmountBeforeFeeOverflow)
        );
    }
}

#[test]
fn trading_start_rule() {
    let v = json(VECTORS);
    let block_time = 5_000;
    for row in v["start"]["contract"].as_array().unwrap() {
        let start = u64_of(row, "tradingStart");
        let mut parameters = parameters_for(FEE_5, FEE_03, ZERO_SEED_LAUNCH_DEFAULT_DECAY_RATE_X32);
        parameters.trading_start = start;
        let created = parameters.validate(block_time);
        if s(row, "create").starts_with("InvalidTradingStart") {
            assert_eq!(
                created,
                Err(ZeroSeedLaunchParameterError::InvalidTradingStart)
            );
            continue;
        }
        assert_eq!(created, Ok(()));
        let range = ZeroSeedLaunchRange::from_requested(true, -13_815_500, -9_210_300).unwrap();
        let installation = install_supply(&range, parameters.supply).unwrap();
        let mut launch = launch(&range, installation.liquidity, FEE_5, FEE_03);
        let mut config = *launch.pool.launch();
        config.fee.trading_start = start;
        launch.pool =
            ZeroSeedLaunchPool::new_math(launch.pool.key(), config, launch.pool.state()).unwrap();
        let buy = |timestamp| {
            launch
                .pool
                .simulate_swap(launch.pool.state(), 1_000_000, false, None, timestamp)
        };
        match s(row, "trade_at_block_time") {
            "ok" => assert!(buy(block_time).is_ok()),
            "TradingNotStarted" => assert_eq!(
                buy(block_time).err(),
                Some(ZeroSeedLaunchPoolQuoteError::TradingNotStarted)
            ),
            other => panic!("{other}"),
        }
        if s(row, "trade_at_start") == "ok" {
            assert!(buy(start).is_ok());
            assert_eq!(buy(start).unwrap().fee_rate, FEE_5);
        }
    }
    // Mined one second after a start equal to the preview time.
    let mined_late = &v["start"]["contract_mined_late"];
    let mut parameters = parameters_for(FEE_5, FEE_03, ZERO_SEED_LAUNCH_DEFAULT_DECAY_RATE_X32);
    parameters.trading_start = mined_late["tradingStart"].as_u64().unwrap();
    assert_eq!(
        parameters.validate(mined_late["previewed_at"].as_u64().unwrap()),
        Ok(())
    );
    assert_eq!(
        parameters.validate(mined_late["mined_at"].as_u64().unwrap()),
        Err(ZeroSeedLaunchParameterError::InvalidTradingStart)
    );
}

#[test]
fn metadata_examples_and_refusals() {
    let v = json(VECTORS);
    let metadata = &v["metadata"];
    assert_eq!(metadata["decimals"], 18);
    for (text, word) in metadata["examples"].as_object().unwrap() {
        let word = B256::from_str(word.as_str().unwrap()).unwrap();
        assert_eq!(pack_launch_metadata(text.as_bytes()).unwrap(), word);
        assert_eq!(unpack_launch_metadata(&word), Some(text.as_bytes()));
    }
    let mut parameters = parameters_for(FEE_5, FEE_03, ZERO_SEED_LAUNCH_DEFAULT_DECAY_RATE_X32);
    let mut tail = parameters.symbol;
    tail[31] = 1;
    let mut long = [0u8; 32];
    long[0] = 32;
    for word in [B256::ZERO, B256::from(long), tail] {
        assert!(!is_canonical_launch_metadata(&word));
        parameters.name = word;
        assert_eq!(
            parameters.validate(START),
            Err(ZeroSeedLaunchParameterError::InvalidMetadata)
        );
    }
}

#[test]
fn claim_recipients_and_quote_support() {
    let instance = ZeroSeedLaunchInstance {
        chain_id: 31337,
        core: Address::repeat_byte(0xc0),
        extension: Address::repeat_byte(0x51),
        periphery: Address::repeat_byte(0x9e),
    };
    let range = ZeroSeedLaunchRange::from_requested(false, -13_815_500, -9_210_300).unwrap();
    let launch = launch(&range, 1_000_000, FEE_5, FEE_03);
    let key = launch.pool.key();
    for recipient in [
        Address::ZERO,
        instance.core,
        instance.extension,
        instance.periphery,
        key.token0,
        key.token1,
    ] {
        assert_eq!(
            validate_claim_recipient(&instance, &key, recipient),
            Err(ZeroSeedLaunchParameterError::InvalidRecipient)
        );
    }
    assert_eq!(
        validate_claim_recipient(&instance, &key, Address::repeat_byte(0xbe)),
        Ok(())
    );
    let other = ZeroSeedLaunchInstance {
        extension: Address::repeat_byte(0x52),
        ..instance
    };
    assert_eq!(
        validate_claim_recipient(&other, &key, Address::repeat_byte(0xbe)),
        Err(ZeroSeedLaunchParameterError::InstanceMismatch)
    );

    // Quote support is the caller's list; the SDK reviews no ERC-20 itself.
    let observation = ZeroSeedLaunchQuoteObservation {
        chain_id: instance.chain_id,
        quote: launch.quote,
        quote_runtime: Some(U256::from(7)),
    };
    let reviewed = [ZeroSeedLaunchReviewedQuote {
        chain_id: instance.chain_id,
        quote: launch.quote,
        runtime: U256::from(7),
    }];
    assert_eq!(
        observation.supported_kind(&[]),
        Err(ZeroSeedLaunchParameterError::QuoteNotReviewed)
    );
    assert_eq!(
        observation.supported_kind(&reviewed),
        Ok(ZeroSeedLaunchQuoteKind::Erc20 {
            quote_runtime: U256::from(7)
        })
    );
    let codeless = ZeroSeedLaunchQuoteObservation {
        quote_runtime: None,
        ..observation
    };
    assert_eq!(
        codeless.supported_kind(&reviewed),
        Err(ZeroSeedLaunchParameterError::UnsupportedQuoteToken)
    );
    let pool = |instance: &ZeroSeedLaunchInstance,
                observation: &ZeroSeedLaunchQuoteObservation,
                reviewed: &[ZeroSeedLaunchReviewedQuote]| {
        ZeroSeedLaunchPool::new(
            key,
            *launch.pool.launch(),
            launch.pool.state(),
            instance,
            observation,
            reviewed,
        )
    };
    assert!(pool(&instance, &observation, &reviewed).is_ok());
    assert_eq!(
        pool(&instance, &observation, &[]).err(),
        Some(ZeroSeedLaunchPoolConstructionError::UnsupportedQuoteToken)
    );
    assert_eq!(
        pool(&other, &observation, &reviewed).err(),
        Some(ZeroSeedLaunchPoolConstructionError::InstanceMismatch)
    );
    let elsewhere = ZeroSeedLaunchQuoteObservation {
        chain_id: 1,
        ..observation
    };
    assert_eq!(
        pool(&instance, &elsewhere, &reviewed).err(),
        Some(ZeroSeedLaunchPoolConstructionError::InstanceMismatch)
    );
}

// ---------------------------------------------------------------------------------------------
// Raw receipt
// ---------------------------------------------------------------------------------------------

fn words(data: &str) -> Vec<B256> {
    let bytes = const_hex(data);
    bytes.chunks(32).map(B256::from_slice).collect()
}

fn const_hex(data: &str) -> Vec<u8> {
    let data = data.strip_prefix("0x").unwrap();
    (0..data.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&data[i..i + 2], 16).unwrap())
        .collect()
}

fn word_address(word: &B256) -> Address {
    Address::from_slice(&word[12..])
}

fn word_i128(word: &B256) -> i128 {
    i128::from_be_bytes(word[16..].try_into().unwrap())
}

fn word_u128(word: &B256) -> u128 {
    u128::from_be_bytes(word[16..].try_into().unwrap())
}

fn word_u64(word: &B256) -> u64 {
    u64::from_be_bytes(word[24..].try_into().unwrap())
}

fn word_i32(word: &B256) -> i32 {
    i32::from_be_bytes(word[28..].try_into().unwrap())
}

fn topic(row: &Value, i: usize) -> B256 {
    B256::from_str(row["topics"][i].as_str().unwrap()).unwrap()
}

/// `LaunchCreated(poolId, token, controller, poolKey, positionId, liquidity, parameters,
/// logoUrl)` of the receipt: the SDK predicts its token, pool key and position from the emitted
/// parameters, and its liquidity, installed and sink supply from the requested supply.
#[test]
fn receipt_creation_swap_and_claim_match_the_sdk() {
    let v = json(EVENTS);
    let receipt = v["receipt"].as_array().unwrap();
    let created = &receipt[2];
    assert_eq!(
        format!("{:#x}", topic(created, 0)),
        "0x0a54c7540832cb23832d30bbf27c5597cfb779d070a1c253a7aee90571c2da4c"
    );
    let extension = Address::from_str(s(created, "emitter")).unwrap();
    let token = word_address(&topic(created, 2));
    let controller = word_address(&topic(created, 3));
    let w = words(s(created, "data"));
    let parameters = ZeroSeedLaunchParameters {
        name: w[5],
        symbol: w[6],
        supply: word_u128(&w[7]),
        quote_token: word_address(&w[8]),
        ask_tick: word_i32(&w[9]),
        upper_tick: word_i32(&w[10]),
        trading_start: word_u64(&w[11]),
        decay_rate_x32: word_u64(&w[12]),
        initial_fee: word_u64(&w[13]),
        final_fee: word_u64(&w[14]),
        salt: w[15],
    };
    assert_eq!(
        unpack_launch_metadata(&parameters.name),
        Some(&b"Zero Seed"[..])
    );
    assert_eq!(
        unpack_launch_metadata(&parameters.symbol),
        Some(&b"ZERO"[..])
    );
    assert_eq!(
        launch_token_address(
            extension,
            controller,
            parameters.salt,
            parameters.name,
            parameters.symbol
        ),
        token
    );
    let preview = preview_installation(
        extension,
        controller,
        &parameters,
        parameters.trading_start,
        ZeroSeedLaunchChainObservation {
            quote_has_code: false,
            predicted_token_has_code: false,
        },
    )
    .unwrap();
    assert_eq!(preview.token, token);
    assert_eq!(preview.pool_key.token0, word_address(&w[0]));
    assert_eq!(preview.pool_key.token1, word_address(&w[1]));
    // Concentrated pool config: extension, zero fee, then the flag bit and the spacing.
    let mut config = [0u8; 32];
    config[..20].copy_from_slice(extension.as_slice());
    config[28..]
        .copy_from_slice(&(0x8000_0000u32 | preview.installation.range.tick_spacing).to_be_bytes());
    assert_eq!(w[2], B256::from(config));
    assert_eq!(preview.position_id, w[3]);
    assert_eq!(preview.installation.liquidity, word_u128(&w[4]));
    // The emitted parameters keep the requested bounds.
    assert_eq!(
        (parameters.ask_tick, parameters.upper_tick),
        (-13_815_500, -9_210_300)
    );
    // The logo is the last field: an empty string here.
    assert_eq!(w[16], B256::from(U256::from(0x220).to_be_bytes::<32>()));
    assert_eq!(w[17], B256::ZERO);
    // Both LaunchCreated fixtures share everything before the logo.
    for (fixture, logo) in v["LaunchCreated"]
        .as_array()
        .unwrap()
        .iter()
        .zip(["", "https://example.invalid/logo.svg"])
    {
        assert_eq!(s(fixture, "logo"), logo);
        let fw = words(s(fixture, "data"));
        assert_eq!(fw[..17], w[..17]);
        assert_eq!(word_u128(&fw[17]), logo.len() as u128);
        assert_eq!(
            &const_hex(s(fixture, "data"))[18 * 32..18 * 32 + logo.len()],
            logo.as_bytes()
        );
    }

    // The single mint: installed supply into Core, the sink to address(0), not a burn.
    let mint = &receipt[0];
    assert_eq!(word_address(&topic(mint, 1)), Address::ZERO);
    assert_eq!(
        word_u128(&words(s(mint, "data"))[0]),
        preview.installation.installed_supply
    );
    let sink = &receipt[1];
    assert_eq!(word_address(&topic(sink, 2)), Address::ZERO);
    assert_eq!(
        word_u128(&words(s(sink, "data"))[0]),
        preview.installation.sink_supply
    );
    assert_eq!(
        preview.installation.installed_supply + preview.installation.sink_supply,
        parameters.supply
    );

    // LaunchSwapped(poolId, locker, delta0, delta1, rate, fee, feeIsToken1): an exact-input buy
    // with native ETH at the start.
    let swapped = &receipt[5];
    assert_eq!(topic(swapped, 1), topic(created, 1));
    let sw = words(s(swapped, "data"));
    let pool = ZeroSeedLaunchPool::new_math(
        preview.pool_key,
        ZeroSeedLaunchConfig {
            quote_token: parameters.quote_token,
            range: preview.installation.range,
            liquidity: preview.installation.liquidity,
            fee: parameters.fee_schedule(),
        },
        ZeroSeedLaunchPoolState {
            sqrt_ratio: to_sqrt_ratio::<Evm>(preview.installation.initial_tick).unwrap(),
            tick: preview.installation.initial_tick,
            liquidity: 0,
        },
    )
    .unwrap();
    let swap = pool
        .simulate_swap(
            pool.state(),
            word_i128(&sw[0]),
            false,
            None,
            parameters.trading_start,
        )
        .unwrap();
    assert_eq!(swap.delta0, word_i128(&sw[0]));
    assert_eq!(swap.delta1, word_i128(&sw[1]));
    assert_eq!(swap.fee_rate, word_u64(&sw[2]));
    assert_eq!(swap.fee_amount, word_u128(&sw[3]));
    assert_eq!(swap.fee_is_token1, word_u128(&sw[4]) == 1);
    // CreatorFeesClaimed(poolId, controller, amount0, amount1) moves exactly that fee.
    let claimed = &receipt[7];
    let cw = words(s(claimed, "data"));
    assert_eq!(word_address(&topic(claimed, 2)), controller);
    assert_eq!((word_u128(&cw[0]), word_u128(&cw[1])), (0, swap.fee_amount));
    // LaunchFeesClaimed of the periphery reports the same claim, not a second one.
    let paid = &receipt[9];
    let pw = words(s(paid, "data"));
    assert_eq!((word_u128(&pw[0]), word_u128(&pw[1])), (0, swap.fee_amount));
}

#[test]
fn preview_refusal_order() {
    let extension = Address::repeat_byte(0x51);
    let controller = Address::repeat_byte(0x9e);
    let observed = ZeroSeedLaunchChainObservation {
        quote_has_code: true,
        predicted_token_has_code: false,
    };
    let base = parameters_for(FEE_5, FEE_03, ZERO_SEED_LAUNCH_DEFAULT_DECAY_RATE_X32);
    let erc20 = ZeroSeedLaunchParameters {
        quote_token: Address::repeat_byte(0xff),
        ..base
    };
    let preview = preview_installation(extension, controller, &erc20, START, observed).unwrap();
    assert!(!preview.installation.range.launch_token_is_token1);
    assert_eq!(preview.pool_key.token1, erc20.quote_token);
    // A codeless ERC-20 quote is refused before everything else.
    let codeless = ZeroSeedLaunchChainObservation {
        quote_has_code: false,
        ..observed
    };
    let bad = ZeroSeedLaunchParameters {
        supply: 0,
        name: B256::ZERO,
        ..erc20
    };
    assert_eq!(
        preview_installation(extension, controller, &bad, START, codeless).err(),
        Some(ZeroSeedLaunchParameterError::UnsupportedQuoteToken)
    );
    assert_eq!(
        preview_installation(extension, controller, &bad, START, observed).err(),
        Some(ZeroSeedLaunchParameterError::InvalidMetadata)
    );
    let bad = ZeroSeedLaunchParameters {
        supply: 0,
        ask_tick: 0,
        upper_tick: 0,
        ..erc20
    };
    assert_eq!(
        preview_installation(extension, controller, &bad, START, observed).err(),
        Some(ZeroSeedLaunchParameterError::InvalidSupply)
    );
    let bad = ZeroSeedLaunchParameters {
        ask_tick: 0,
        upper_tick: 0,
        initial_fee: 0,
        ..erc20
    };
    assert_eq!(
        preview_installation(extension, controller, &bad, START, observed).err(),
        Some(ZeroSeedLaunchParameterError::InvalidTicks)
    );
    let bad = ZeroSeedLaunchParameters {
        initial_fee: 0,
        trading_start: 0,
        ..erc20
    };
    assert_eq!(
        preview_installation(extension, controller, &bad, START, observed).err(),
        Some(ZeroSeedLaunchParameterError::InvalidFeeSchedule)
    );
    assert_eq!(
        preview_installation(extension, controller, &erc20, START + 1, observed).err(),
        Some(ZeroSeedLaunchParameterError::InvalidTradingStart)
    );
    let collision = ZeroSeedLaunchChainObservation {
        predicted_token_has_code: true,
        ..observed
    };
    assert_eq!(
        preview_installation(extension, controller, &erc20, START, collision).err(),
        Some(ZeroSeedLaunchParameterError::LaunchTokenExists)
    );
    let one = ZeroSeedLaunchParameters { supply: 1, ..erc20 };
    assert_eq!(
        preview_installation(extension, controller, &one, START, observed).err(),
        Some(ZeroSeedLaunchParameterError::ZeroLiquidity)
    );
    // The token address does not depend on the quote, supply, range or fees.
    let other = ZeroSeedLaunchParameters {
        supply: 7,
        ask_tick: 0,
        upper_tick: 100,
        initial_fee: 0,
        final_fee: 0,
        ..base
    };
    assert_eq!(
        launch_token_address(extension, controller, other.salt, other.name, other.symbol),
        preview.token
    );
}
