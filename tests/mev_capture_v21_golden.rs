#![cfg(feature = "evm")]
use ekubo_sdk::quoting::pools::mev_capture_v21::*;
use serde_json::Value;
use std::str::FromStr;

fn n<T: FromStr>(v: &Value, key: &str) -> T
where
    T::Err: std::fmt::Debug,
{
    v[key].as_str().unwrap().parse().unwrap()
}
fn model(v: &Value) -> MevCaptureV21Model {
    let c = &v["config"];
    MevCaptureV21Model::new(MevCaptureV21Config {
        half_life: n(c, "halfLife"),
        slope_k: n(c, "slopeK"),
        segment_exp: n(c, "segmentExp"),
        j_lin: n(c, "jLin"),
        max_fee: n(c, "maxFee"),
        clamp_ticks: n(c, "clampTicks"),
        m_gate: n(c, "mGate"),
        max_segments: n(c, "maxSegments"),
    })
    .unwrap()
}
fn anchor(v: &Value) -> MevCaptureV21Anchor {
    MevCaptureV21Anchor {
        last_update_time: n(v, "lastUpdateTime"),
        l_ref_time: n(v, "lRefTime"),
        last_pos_time: n(v, "lastPosTime"),
        l_ref_bits: n(v, "lRefBits"),
        snap_bits: n(v, "snapBits"),
        l_ref_raise_time: n(v, "lRefRaiseTime"),
        anchor_x16: n(v, "anchorX16"),
    }
}
#[test]
fn golden_anchor_updates_all_seven_fields() {
    let v: Value =
        serde_json::from_str(include_str!("data/mevcapture-v21/anchorUpdates.json")).unwrap();
    let m = model(&v);
    let cases = v["anchorUpdates"].as_array().unwrap();
    assert_eq!(cases.len(), 120);
    for (i, c) in cases.iter().enumerate() {
        let mut state = anchor(&c["stateIn"]);
        let gate = m
            .before_swap(
                &mut state,
                n(c, "tick"),
                n(c, "liquidity"),
                n(c, "timestamp"),
            )
            .unwrap();
        assert_eq!(gate.passed, c["passed"].as_bool().unwrap(), "case {i}");
        assert_eq!(gate.l_obs, n::<u8>(c, "lObs"), "case {i}");
        assert_eq!(gate.e_ref, n::<u8>(c, "eRef"), "case {i}");
        assert_eq!(state, anchor(&c["expected"]), "case {i}");
    }
}
#[test]
fn golden_gate_scenarios_all_steps() {
    let v: Value =
        serde_json::from_str(include_str!("data/mevcapture-v21/gateScenarios.json")).unwrap();
    let m = model(&v);
    let cases = v["gateScenarios"].as_array().unwrap();
    assert_eq!(cases.len(), 24);
    let mut count = 0;
    for c in cases {
        let mut state = anchor(&c["initial"]);
        for (i, s) in c["steps"].as_array().unwrap().iter().enumerate() {
            let now = n(s, "timestamp");
            if s["op"] == "position" {
                m.before_position(&mut state, n(s, "activeLiquidity"), now);
            } else {
                let gate = m.before_swap(&mut state, n(s, "tick"), n(s, "liquidity"), now);
                assert_eq!(gate.is_some(), s["first"].as_bool().unwrap());
                if let Some(g) = gate {
                    assert_eq!(g.passed, s["passed"].as_bool().unwrap());
                    assert_eq!(g.l_obs, n::<u8>(s, "lObs"));
                    assert_eq!(g.e_ref, n::<u8>(s, "eRef"));
                }
                m.after_swap(&mut state, n(s, "liquidityAfter"), now);
            }
            assert_eq!(state, anchor(&s["expected"]), "{} step {i}", c["name"]);
            count += 1;
        }
    }
    assert_eq!(count, 1785);
}

#[test]
fn nondefault_config_wrap_snapshot_and_validation() {
    let config = MevCaptureV21Config {
        half_life: 7,
        slope_k: 16,
        segment_exp: 8,
        j_lin: 1,
        max_fee: 1000,
        clamp_ticks: 1,
        m_gate: 0,
        max_segments: 25,
    };
    let m = MevCaptureV21Model::new(config).unwrap();
    let mut s = m.initialize(10, u32::MAX - 2);
    assert_eq!(s.l_ref_raise_time, u32::MAX - 9);
    let g = m.before_swap(&mut s, 20, 8, 4).unwrap();
    assert!(g.passed);
    assert_eq!(s.anchor_x16, 11 << 16); // 7 elapsed seconds, clamp is 1 tick.
    assert_eq!(s.l_ref_bits, 1);
    m.before_position(&mut s, 8, 4);
    m.before_position(&mut s, 1024, 4);
    assert_eq!(s.snap_bits, 4); // first snapshot wins
    m.after_swap(&mut s, u128::MAX, 4);
    assert_eq!(s.l_ref_bits, 1); // position timestamp suppresses refresh
    assert!(m.before_swap(&mut s, 30, 0, 4).is_none());
    assert!(
        MevCaptureV21Model::new(MevCaptureV21Config {
            max_segments: 24,
            ..config
        })
        .is_err()
    );
    assert!(
        MevCaptureV21Model::new(MevCaptureV21Config {
            half_life: 0,
            ..config
        })
        .is_err()
    );
}

#[test]
fn golden_schedules_all_boundaries_fees_and_toward_rounding() {
    let v: Value =
        serde_json::from_str(include_str!("data/mevcapture-v21/schedules.json")).unwrap();
    let base = model(&v).config();
    let cases = v["schedules"].as_array().unwrap();
    assert_eq!(cases.len(), 288);
    for (i, c) in cases.iter().enumerate() {
        let j_lin = n::<u8>(c, "jLin");
        let m = MevCaptureV21Model::new(MevCaptureV21Config {
            j_lin,
            max_segments: j_lin + 24,
            ..base
        })
        .unwrap();
        let increasing = c["increasing"].as_bool().unwrap();
        let a = n(c, "anchorX16");
        assert_eq!(
            m.toward_tick(a, increasing),
            n::<i32>(c, "towardTick"),
            "schedule {i}"
        );
        let actual: Vec<_> = m
            .away_schedule(
                a,
                n(c, "coreTick"),
                increasing,
                n(c, "poolFee"),
                n(c, "spacingExp"),
            )
            .unwrap()
            .collect();
        let expected = c["segments"].as_array().unwrap();
        assert_eq!(actual.len(), expected.len(), "schedule {i}");
        let direction = if increasing { 1 } else { -1 };
        for (s, e) in actual.iter().zip(expected) {
            assert_eq!(s.k, n::<u32>(e, "k"), "schedule {i}");
            assert_eq!(direction * s.lo_x16, n::<i128>(e, "loX16"), "schedule {i}");
            assert_eq!(direction * s.hi_x16, n::<i128>(e, "hiX16"), "schedule {i}");
            assert_eq!(
                direction * (s.hi_x16 >> 16),
                n::<i128>(e, "hiTick"),
                "schedule {i}"
            );
            assert_eq!(s.fee, n::<u16>(e, "fee"), "schedule {i}");
        }
    }
}

mod swaps {
    use super::*;
    use ekubo_sdk::U256;
    use ekubo_sdk::alloy_primitives::Address;
    use ekubo_sdk::chain::evm::fixed_sqrt_ratio_to_contract_sqrt_ratio;
    use ekubo_sdk::math::tick::to_sqrt_ratio;
    use ekubo_sdk::quoting::types::{Pool, PoolConfig, PoolKey, QuoteParams, Tick, TokenAmount};
    use std::collections::BTreeMap;

    /// `toFixed` of `src/types/sqrtRatio.sol`: compressed 96-bit value to 64.128 fixed point.
    fn to_fixed(raw: U256) -> U256 {
        let mask: U256 = U256::from(3u8) << 94usize;
        let bits: U256 = (raw & mask) >> 89usize;
        let shift = 2 + bits.to::<usize>();
        (raw & !mask) << shift
    }

    fn compressed(fixed: U256) -> U256 {
        let raw = fixed_sqrt_ratio_to_contract_sqrt_ratio(fixed);
        assert_eq!(
            to_fixed(raw),
            fixed,
            "fixed value must be exactly representable"
        );
        raw
    }

    fn core_state(v: &Value) -> (U256, i32, u128) {
        (n(v, "sqrtRatio"), n(v, "tick"), n(v, "liquidity"))
    }

    fn actual(s: &MevCaptureV21CoreState) -> (U256, i32, u128) {
        (compressed(s.sqrt_ratio), s.tick, s.liquidity)
    }

    /// Replays a contract vector file from its inputs only (positions and swap parameters) and
    /// returns (swaps, recorded Core calls, Pool::quote checks).
    fn replay(json: &str) -> (usize, usize, usize) {
        let v: Value = serde_json::from_str(json).unwrap();
        let m = model(&v);
        let config = m.config();
        let (mut swaps, mut calls, mut quotes) = (0, 0, 0);
        for s in v["scenarios"].as_array().unwrap() {
            let name = s["name"].as_str().unwrap();
            let key = PoolKey {
                token0: Address::with_last_byte(1),
                token1: Address::with_last_byte(2),
                config: PoolConfig {
                    extension: Address::with_last_byte(3),
                    fee: n::<u16>(s, "poolFee"),
                    pool_type_config: MevCaptureV21PoolTypeConfig {
                        tick_spacing_exp: n(s, "spacingExp"),
                    },
                },
            };
            let initial_tick: i32 = n(s, "initialTick");
            let mut state = MevCaptureV21PoolState {
                core: MevCaptureV21CoreState {
                    sqrt_ratio: to_sqrt_ratio::<ekubo_sdk::chain::evm::Evm>(initial_tick).unwrap(),
                    tick: initial_tick,
                    liquidity: 0,
                },
                anchor: m.initialize(initial_tick, n(s, "initTimestamp")),
            };
            // tick -> (net liquidity delta, referencing positions)
            let mut ticks: BTreeMap<i32, (i128, u32)> = BTreeMap::new();

            for (i, e) in s["events"].as_array().unwrap().iter().enumerate() {
                let now: u32 = n(e, "timestamp");
                let ctx = format!("{name} event {i}");
                if e["type"] == "position" {
                    let (lower, upper): (i32, i32) = (n(e, "tickLower"), n(e, "tickUpper"));
                    let delta: i128 = n(e, "liquidityDelta");
                    m.before_position(&mut state.anchor, state.core.liquidity, now);
                    for (t, d) in [(lower, delta), (upper, -delta)] {
                        let entry = ticks.entry(t).or_default();
                        entry.0 += d;
                        entry.1 += 1;
                    }
                    if lower <= state.core.tick && state.core.tick < upper {
                        state.core.liquidity =
                            state.core.liquidity.checked_add_signed(delta).unwrap();
                    }
                    continue;
                }

                let sorted: Vec<Tick> = ticks
                    .iter()
                    .map(|(&index, &(liquidity_delta, _))| Tick {
                        index,
                        liquidity_delta,
                    })
                    .collect();
                let pool = MevCaptureV21Pool::new(key, config, state, sorted).unwrap();

                assert_eq!(
                    actual(&state.core),
                    core_state(&e["poolBefore"]),
                    "{ctx} poolBefore"
                );
                assert_eq!(state.anchor, anchor(&e["stateBefore"]), "{ctx} stateBefore");

                let raw_limit: U256 = n(e, "sqrtRatioLimit");
                let params = MevCaptureV21SwapParams {
                    is_token1: e["isToken1"] == "true",
                    amount: n(e, "amount"),
                    sqrt_ratio_limit: (!raw_limit.is_zero()).then(|| to_fixed(raw_limit)),
                    min_fee: n(e, "minFee"),
                    skip_ahead: 0,
                };
                let swap = pool.simulate_swap(state, params, now).unwrap();

                assert_eq!(
                    swap.gate.is_some(),
                    e["firstOfTimestamp"] == "true",
                    "{ctx} first"
                );
                assert_eq!(
                    swap.gate.is_some_and(|g| !g.passed),
                    e["gateFailed"] == "true",
                    "{ctx} gate"
                );
                let expected_calls = e["coreCalls"].as_array().unwrap();
                // The vector generator's reference model omits the no-op pass-through call that the
                // contract still makes when the amount is zero or the price is at the user limit.
                let recorded: Vec<_> = swap
                    .calls
                    .iter()
                    .filter(|c| c.kind != MevCaptureV21CallKind::PassThrough)
                    .collect();
                if recorded.len() != swap.calls.len() {
                    assert_eq!(swap.calls.len(), 1, "{ctx} pass-through");
                    assert_eq!(
                        (swap.calls[0].delta0, swap.calls[0].delta1),
                        (0, 0),
                        "{ctx}"
                    );
                }
                assert_eq!(recorded.len(), expected_calls.len(), "{ctx} call count");
                for (j, (c, x)) in recorded.iter().zip(expected_calls).enumerate() {
                    assert_eq!(
                        compressed(c.sqrt_ratio_limit),
                        n::<U256>(x, "sqrtRatioLimit"),
                        "{ctx} call {j} limit"
                    );
                    assert_eq!(c.min_fee, n::<u16>(x, "minFee"), "{ctx} call {j} minFee");
                    assert_eq!(c.amount, n::<i128>(x, "amount"), "{ctx} call {j} amount");
                }
                assert_eq!(swap.delta0, n::<i128>(e, "delta0"), "{ctx} delta0");
                assert_eq!(swap.delta1, n::<i128>(e, "delta1"), "{ctx} delta1");
                assert_eq!(
                    actual(&swap.state_after.core),
                    core_state(&e["poolAfter"]),
                    "{ctx} poolAfter"
                );
                assert_eq!(
                    swap.state_after.anchor,
                    anchor(&e["stateAfter"]),
                    "{ctx} stateAfter"
                );
                assert_eq!(swap.resources.core_calls as usize, swap.calls.len());

                if params.min_fee == 0 {
                    let token = if params.is_token1 {
                        key.token1
                    } else {
                        key.token0
                    };
                    let quote = pool
                        .quote(QuoteParams {
                            token_amount: TokenAmount {
                                token,
                                amount: params.amount,
                            },
                            sqrt_ratio_limit: params.sqrt_ratio_limit,
                            override_state: None,
                            meta: u64::from(now),
                        })
                        .unwrap();
                    let (specified, calculated) = if params.is_token1 {
                        (swap.delta1, swap.delta0)
                    } else {
                        (swap.delta0, swap.delta1)
                    };
                    assert_eq!(quote.consumed_amount, specified, "{ctx} quote");
                    assert_eq!(
                        quote.calculated_amount,
                        calculated.unsigned_abs(),
                        "{ctx} quote"
                    );
                    assert_eq!(quote.state_after, swap.state_after, "{ctx} quote");
                    assert_eq!(quote.execution_resources, swap.resources, "{ctx} quote");
                    quotes += 1;
                }

                state = swap.state_after;
                swaps += 1;
                calls += expected_calls.len();
            }
        }
        (swaps, calls, quotes)
    }

    #[test]
    fn golden_swaps_all_calls_deltas_pool_and_anchor() {
        let r = replay(include_str!("data/mevcapture-v21/swaps.json"));
        assert_eq!(r, (32, 152, 31));
    }

    /// Word-boundary step splits with liquidity, user minFee on away segments, refresh raise and
    /// its same-timestamp position suppression.
    #[test]
    fn supplement_swaps_word_splits_min_fee_refresh() {
        let r = replay(include_str!("data/mevcapture-v21/swapsSupplement.json"));
        assert_eq!(r, (9, 61, 7));
    }

    /// A nondefault getConfig tuple, decay clamp, capped segments and a pass-through swap.
    #[test]
    fn supplement_swaps_nondefault_config() {
        let r = replay(include_str!("data/mevcapture-v21/swapsNondefault.json"));
        assert_eq!(r, (6, 10, 5));
    }

    #[test]
    fn construction_and_core_revert_conditions() {
        use ekubo_sdk::chain::Chain;
        use ekubo_sdk::chain::evm::Evm;
        let config = MevCaptureV21Config {
            half_life: 120,
            slope_k: 4,
            segment_exp: 0,
            j_lin: 16,
            max_fee: 32768,
            clamp_ticks: 2500,
            m_gate: 3,
            max_segments: 40,
        };
        let key = |fee: u16, extension: u8| PoolKey {
            token0: Address::with_last_byte(1),
            token1: Address::with_last_byte(2),
            config: PoolConfig {
                extension: Address::with_last_byte(extension),
                fee,
                pool_type_config: MevCaptureV21PoolTypeConfig {
                    tick_spacing_exp: 12,
                },
            },
        };
        let liquidity = 1u128 << 66;
        let ticks = vec![
            Tick {
                index: -163840,
                liquidity_delta: liquidity as i128,
            },
            Tick {
                index: 163840,
                liquidity_delta: -(liquidity as i128),
            },
        ];
        let state = MevCaptureV21PoolState {
            core: MevCaptureV21CoreState {
                sqrt_ratio: to_sqrt_ratio::<Evm>(0).unwrap(),
                tick: 0,
                liquidity,
            },
            anchor: MevCaptureV21Model::new(config).unwrap().initialize(0, 1),
        };
        type E = MevCaptureV21PoolConstructionError;
        let new = |k, s, t| MevCaptureV21Pool::new(k, config, s, t);
        assert_eq!(
            new(key(32768, 3), state, ticks.clone()),
            Err(E::InvalidPoolFee)
        );
        assert_eq!(new(key(0, 3), state, ticks.clone()), Err(E::InvalidPoolFee));
        assert_eq!(
            new(key(196, 0), state, ticks.clone()),
            Err(E::MissingExtension)
        );
        let mut bad = state;
        bad.core.liquidity -= 1;
        assert_eq!(
            new(key(196, 3), bad, ticks.clone()),
            Err(E::ActiveLiquidityMismatch)
        );
        bad = state;
        bad.core.tick = 1;
        assert_eq!(new(key(196, 3), bad, ticks.clone()), Err(E::InvalidPrice));
        let misaligned = vec![Tick {
            index: 1,
            liquidity_delta: 0,
        }];
        assert_eq!(new(key(196, 3), state, misaligned), Err(E::InvalidTicks));

        let pool = new(key(196, 3), state, ticks).unwrap();
        let swap = |amount, limit, is_token1| {
            pool.simulate_swap(
                state,
                MevCaptureV21SwapParams {
                    is_token1,
                    amount,
                    sqrt_ratio_limit: limit,
                    min_fee: 0,
                    skip_ahead: 0,
                },
                1,
            )
        };
        // a limit not representable as a compressed SqrtRatio reverts InvalidSqrtRatioLimit
        let unrepresentable = to_sqrt_ratio::<Evm>(100).unwrap() + U256::from(1u8);
        assert_eq!(
            swap(1000, Some(unrepresentable), true),
            Err(MevCaptureV21QuoteError::InvalidSqrtRatioLimit)
        );
        assert_eq!(
            swap(1000, Some(Evm::min_sqrt_ratio()), true),
            Err(MevCaptureV21QuoteError::SqrtRatioLimitWrongDirection)
        );
        // zero amount: one no-op pass-through call, no state write apart from the clocks
        let zero = swap(0, None, true).unwrap();
        assert_eq!(zero.calls.len(), 1);
        assert_eq!(zero.calls[0].kind, MevCaptureV21CallKind::PassThrough);
        assert_eq!((zero.delta0, zero.delta1), (0, 0));
        assert_eq!(fee_q16_to_q64(196), 196u64 << 48);
    }
}
