//! The exact installation of `ZeroSeedLaunch.previewInstallation`: the protocol's integer vectors
//! (`tests/vectors/zero-seed-launch-installation.json`, verbatim) and a property check against an
//! independent oracle that searches Core's own rounded debit for the largest affordable liquidity.
#![cfg(any(feature = "evm-alloy-0_6", feature = "evm-alloy-1"))]

use ekubo_sdk::{
    U256,
    alloy_primitives::Address,
    chain::{
        Chain,
        evm::{EVM_MAX_TICK_SPACING, Evm},
    },
    math::{
        delta::{amount0_delta, amount1_delta},
        tick::to_sqrt_ratio,
    },
    quoting::pools::zero_seed_launch::{
        ZeroSeedLaunchFeeSchedule, ZeroSeedLaunchInstallation, ZeroSeedLaunchParameterError,
        ZeroSeedLaunchParameters, ZeroSeedLaunchRange, installation_math, max_liquidity_per_tick,
        preview_installation_math,
    },
};
use serde_json::Value;

const VECTORS: &str = include_str!("vectors/zero-seed-launch-installation.json");

const CANONICAL_FEE: ZeroSeedLaunchFeeSchedule = ZeroSeedLaunchFeeSchedule {
    trading_start: 1_000,
    fee_duration: 3_600,
    initial_fee: 9_223_372_036_854_775_808,
    final_fee: 55_340_232_221_128_654,
};

fn parameters(supply: u128, range: ZeroSeedLaunchRange) -> ZeroSeedLaunchParameters {
    ZeroSeedLaunchParameters {
        supply,
        // The installation does not depend on the quote, only on the token order in `range`.
        quote_token: Address::ZERO,
        range,
        fee: CANONICAL_FEE,
    }
}

fn bounds(range: &ZeroSeedLaunchRange) -> (U256, U256) {
    let (lower, upper) = range.pool_bounds();
    (
        to_sqrt_ratio::<Evm>(lower).unwrap(),
        to_sqrt_ratio::<Evm>(upper).unwrap(),
    )
}

/// Core's debit of the launch token for `liquidity`, rounded up; `None` above `u128`.
fn debit(range: &ZeroSeedLaunchRange, liquidity: u128) -> Option<u128> {
    let (lower, upper) = bounds(range);
    if range.launch_token_is_token1 {
        amount1_delta(lower, upper, liquidity, true).ok()
    } else {
        amount0_delta(lower, upper, liquidity, true).ok()
    }
}

/// The largest `u128` liquidity whose debit fits `supply`, by binary search on the debit itself
/// (monotone in liquidity). Shares nothing with the SDK's closed form.
fn oracle_max_liquidity(range: &ZeroSeedLaunchRange, supply: u128) -> u128 {
    let affordable = |l: u128| debit(range, l).is_some_and(|d| d <= supply);
    if affordable(u128::MAX) {
        return u128::MAX;
    }
    let (mut lo, mut hi) = (0u128, u128::MAX);
    while hi - lo > 1 {
        let mid = lo + (hi - lo) / 2;
        if affordable(mid) {
            lo = mid;
        } else {
            hi = mid;
        }
    }
    lo
}

/// The shared `maxLiquidityForToken0` helper the extension used before: it floors
/// `lower * upper / 2**128` before multiplying by the supply.
fn previous_token0_liquidity(range: &ZeroSeedLaunchRange, supply: u128) -> U256 {
    let (lower, upper) = bounds(range);
    let product = (ruint::aliases::U512::from(lower) * ruint::aliases::U512::from(upper)) >> 128;
    let liquidity =
        ruint::aliases::U512::from(supply) * product / ruint::aliases::U512::from(upper - lower);
    U256::from(liquidity)
}

/// The verdict the oracle predicts: the contract saturates at `u128::MAX`, refuses zero and
/// refuses above the per-tick cap; otherwise it installs the debit of the maximum.
fn expected(
    range: &ZeroSeedLaunchRange,
    supply: u128,
) -> Result<(u128, u128), ZeroSeedLaunchParameterError> {
    let liquidity = oracle_max_liquidity(range, supply);
    let cap = max_liquidity_per_tick(range.tick_spacing);
    if liquidity == 0 {
        return Err(ZeroSeedLaunchParameterError::ZeroLiquidity);
    }
    if liquidity > cap {
        return Err(ZeroSeedLaunchParameterError::LiquidityAboveTickCap { liquidity, cap });
    }
    Ok((liquidity, debit(range, liquidity).unwrap()))
}

fn check(range: ZeroSeedLaunchRange, supply: u128) -> Result<ZeroSeedLaunchInstallation, ()> {
    let p = parameters(supply, range);
    let got = preview_installation_math(&p, 0);
    assert_eq!(got, installation_math(&p, 0), "{range:?} {supply}");
    match (expected(&range, supply), got) {
        (Ok((liquidity, installed)), Ok(i)) => {
            assert_eq!(
                (i.liquidity, i.installed_supply, i.sink_supply),
                (liquidity, installed, supply - installed),
                "{range:?} {supply}"
            );
            // maximal: one more unit is unaffordable
            assert!(
                liquidity == u128::MAX || debit(&range, liquidity + 1).is_none_or(|d| d > supply),
                "{range:?} {supply}"
            );
            Ok(i)
        }
        (Err(e), Err(g)) => {
            assert_eq!(e, g, "{range:?} {supply}");
            Err(())
        }
        (e, g) => panic!("{range:?} {supply}: oracle {e:?}, sdk {g:?}"),
    }
}

fn s<'a>(v: &'a Value, field: &str) -> &'a str {
    v[field].as_str().unwrap_or_else(|| panic!("{field}"))
}

fn n(v: &Value, field: &str) -> u128 {
    s(v, field).parse().unwrap()
}

fn range_of(v: &Value) -> ZeroSeedLaunchRange {
    ZeroSeedLaunchRange {
        launch_token_is_token1: s(v, "order") == "t1",
        ask_tick: v["askTick"].as_i64().unwrap() as i32,
        upper_tick: v["upperTick"].as_i64().unwrap() as i32,
        tick_spacing: v["tickSpacing"].as_u64().unwrap() as u32,
    }
}

#[test]
fn protocol_installation_vectors() {
    let vectors: Value = serde_json::from_str(VECTORS).unwrap();
    assert_eq!(vectors["version"], 1);
    let rows = vectors["vectors"].as_array().unwrap();
    assert_eq!(rows.len(), 41);
    let mut improved = vec![];
    for v in rows {
        let label = format!("{} {}", s(v, "label"), s(v, "order"));
        let range = range_of(v);
        let supply = n(v, "supply");
        let (lower, upper) = bounds(&range);
        assert_eq!(
            (
                range.pool_bounds(),
                range.initial_tick(),
                lower,
                upper,
                max_liquidity_per_tick(range.tick_spacing),
            ),
            (
                (
                    v["tickLower"].as_i64().unwrap() as i32,
                    v["tickUpper"].as_i64().unwrap() as i32
                ),
                v["initialTick"].as_i64().unwrap() as i32,
                U256::from_str_radix(s(v, "lowerFixed"), 10).unwrap(),
                U256::from_str_radix(s(v, "upperFixed"), 10).unwrap(),
                n(v, "tickCap"),
            ),
            "{label}"
        );
        let got = preview_installation_math(&parameters(supply, range), 0);
        match v.get("error").and_then(Value::as_str) {
            None => {
                let i = got.unwrap_or_else(|e| panic!("{label}: {e:?}"));
                assert_eq!(
                    (
                        i.liquidity,
                        i.installed_supply,
                        i.sink_supply,
                        i.installed_supply + i.sink_supply,
                    ),
                    (
                        n(v, "liquidity"),
                        n(v, "installedSupply"),
                        n(v, "sink"),
                        supply
                    ),
                    "{label}"
                );
                // Core's debit one unit above the installed liquidity exceeds the supply.
                assert_eq!(
                    debit(&range, i.liquidity + 1),
                    Some(n(v, "debitAtLiquidityPlusOne")),
                    "{label}"
                );
                assert!(n(v, "debitAtLiquidityPlusOne") > supply, "{label}");
                if s(v, "previousLiquidity") != s(v, "liquidity") {
                    improved.push(label.clone());
                }
            }
            Some("ZeroLiquidity") => {
                assert_eq!(
                    got,
                    Err(ZeroSeedLaunchParameterError::ZeroLiquidity),
                    "{label}"
                );
            }
            Some("LiquidityAboveTickCap") => assert_eq!(
                got,
                Err(ZeroSeedLaunchParameterError::LiquidityAboveTickCap {
                    liquidity: n(v, "liquidity"),
                    cap: n(v, "tickCap"),
                }),
                "{label}"
            ),
            Some(other) => panic!("{label}: unexpected error {other}"),
        }
        // the oracle agrees with every row, and the previous helper's value is what it was
        let _ = check(range, supply);
        // (compared saturated at `u128::MAX`: the vectors record the helper's token0 value
        // after its `uint128` saturation)
        if !range.launch_token_is_token1 {
            let saturated = |x: U256| x.min(U256::from(u128::MAX));
            assert_eq!(
                saturated(previous_token0_liquidity(&range, supply)),
                saturated(U256::from_str_radix(s(v, "previousLiquidity"), 10).unwrap()),
                "{label}"
            );
        }
    }
    // The original low-price vector and both counterexamples install more than the helper did.
    for label in [
        "low price, 1e30 t0",
        "low price, two liquidity units t0",
        "full width, int128 budget t0",
    ] {
        assert!(improved.iter().any(|l| l == label), "{label}");
    }
}

/// The original vector and both counterexamples, spelled out.
#[test]
fn original_vector_and_counterexamples() {
    let original = ZeroSeedLaunchRange {
        launch_token_is_token1: false,
        ask_tick: -88_080_384,
        upper_tick: -85_983_232,
        tick_spacing: 524_288,
    };
    let full = ZeroSeedLaunchRange {
        launch_token_is_token1: false,
        ask_tick: -88_722_835,
        upper_tick: 88_722_835,
        tick_spacing: 1,
    };
    let cases: [(ZeroSeedLaunchRange, u128, u128, u128, u128, u128); 3] = [
        (
            original,
            10u128.pow(30),
            106_052_588_672,
            115_073_586_432,
            999_999_999_991_410_763_432_286_846_442,
            8_589_236_567_713_153_558,
        ),
        (
            original,
            17_380_183_081_064_167_375,
            1,
            2,
            17_380_183_081_064_167_375,
            0,
        ),
        (
            full,
            170_141_183_460_469_231_694_794_709_727_778_658_247,
            9_223_595_582_101_085_259,
            9_223_595_582_101_085_260,
            170_141_183_460_469_231_694_794_709_727_778_658_247,
            0,
        ),
    ];
    for (range, supply, previous, liquidity, installed, sink) in cases {
        assert_eq!(
            previous_token0_liquidity(&range, supply),
            U256::from(previous)
        );
        let i = check(range, supply).unwrap();
        assert_eq!(
            (i.liquidity, i.installed_supply, i.sink_supply),
            (liquidity, installed, sink)
        );
    }
    // A: three units cost more than the supply.
    assert_eq!(debit(&original, 3), Some(26_070_274_621_596_251_062));
    // B: one more unit costs more than the supply.
    assert_eq!(
        debit(&full, 9_223_595_582_101_085_261),
        Some(170_141_183_460_469_231_713_241_006_721_831_381_988)
    );
}

/// Deterministic splitmix64: no dependency, reproducible failures.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }

    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }

    fn u128(&mut self) -> u128 {
        (u128::from(self.next()) << 64) | u128::from(self.next())
    }
}

fn spacing(rng: &mut Rng) -> u32 {
    match rng.below(4) {
        0 => 1,
        1 => 1 + rng.below(1_000) as u32,
        2 => [100, 524_288, EVM_MAX_TICK_SPACING.0][rng.below(3) as usize],
        _ => 1 + rng.below(u64::from(EVM_MAX_TICK_SPACING.0)) as u32,
    }
}

/// An aligned position near `anchor` (random over the whole range, at a compact-ratio region
/// boundary, or at an end of the tick range), returned as a launch range of either order.
fn range(rng: &mut Rng) -> Option<ZeroSeedLaunchRange> {
    let spacing = spacing(rng);
    let s = i64::from(spacing);
    let (min, max) = (i64::from(Evm::min_tick()), i64::from(Evm::max_tick()));
    let anchor: i64 = match rng.below(4) {
        0 => min + rng.below((max - min) as u64) as i64,
        // compact sqrt-ratio region transitions
        1 => [-44_361_441, 0, 44_361_442][rng.below(3) as usize],
        2 => min,
        _ => max,
    };
    // narrow (1 to 4 spacings) or anywhere up to the full width
    let widths = if rng.below(2) == 0 {
        4
    } else {
        1 + (max - min) as u64 / u64::from(spacing)
    };
    let width = s * (1 + rng.below(widths) as i64);
    let lower = (anchor - width / 2).div_euclid(s) * s;
    let upper = lower + width;
    if lower < min || upper > max {
        return None;
    }
    let launch_token_is_token1 = rng.below(2) == 0;
    let (ask_tick, upper_tick) = if launch_token_is_token1 {
        (-upper as i32, -lower as i32)
    } else {
        (lower as i32, upper as i32)
    };
    Some(ZeroSeedLaunchRange {
        launch_token_is_token1,
        ask_tick,
        upper_tick,
        tick_spacing: spacing,
    })
}

fn supply(rng: &mut Rng, range: &ZeroSeedLaunchRange) -> u128 {
    const MAX: u128 = i128::MAX as u128;
    match rng.below(5) {
        0 => 1 + rng.u128() % MAX,
        1 => 1 + rng.u128() % (1u128 << (1 + rng.below(127))),
        2 => [1, 2, 10u128.pow(18), 10u128.pow(27), 10u128.pow(30), MAX][rng.below(6) as usize],
        // liquidity-quantization boundaries: exactly the debit of some liquidity, or one less
        _ => {
            let liquidity = 1 + rng.u128() % (1u128 << rng.below(128));
            match debit(range, liquidity) {
                Some(d) if (1..=MAX).contains(&d) => {
                    if rng.below(2) == 0 {
                        d
                    } else {
                        d.max(2) - 1
                    }
                }
                _ => 1 + rng.u128() % MAX,
            }
        }
    }
}

/// Full-domain property: for every aligned range, order and supply up to `int128.max`, the SDK
/// installs `L` with `debit(L) <= supply < debit(L + 1)` and refuses exactly when the oracle's
/// maximum is zero or above the per-tick cap. The previous helper fails it on a fraction of the
/// token0 cases, so the property detects the early-product floor.
#[test]
fn installation_is_the_largest_affordable_liquidity() {
    let mut rng = Rng(0x2d4a_ebc1_9920_1991);
    let (mut cases, mut installed, mut refused, mut helper_short) = (0, 0, 0, 0);
    while cases < 6_000 {
        let Some(range) = range(&mut rng) else {
            continue;
        };
        let supply = supply(&mut rng, &range);
        cases += 1;
        match check(range, supply) {
            Ok(i) => {
                installed += 1;
                if !range.launch_token_is_token1
                    && previous_token0_liquidity(&range, supply) < U256::from(i.liquidity)
                {
                    helper_short += 1;
                }
            }
            Err(()) => refused += 1,
        }
    }
    assert!(installed > 2_000 && refused > 100, "{installed} {refused}");
    assert!(helper_short > 50, "{helper_short}");
    println!("cases {cases} installed {installed} refused {refused} helper short {helper_short}");
}
