#![cfg(feature = "evm")]
//! Differential replay of the MEVCapture v2.1 `main` contract traces (EKU-1582 criterion 4
//! handoff). Every Core call, surcharge, total and final state must match with no tolerance.
use ekubo_sdk::alloy_primitives::Address;
use ekubo_sdk::quoting::pools::concentrated::TickSpacing;
use ekubo_sdk::quoting::pools::mev_capture_v21_main::*;
use ekubo_sdk::quoting::types::{PoolConfig, PoolKey, Tick};
use ruint::aliases::U256;
use serde_json::Value;
use std::collections::BTreeMap;
use std::str::FromStr;

const S: i32 = 4096;
const L66: i128 = 1 << 66;

fn s<T: FromStr>(v: &Value) -> T
where
    T::Err: std::fmt::Debug,
{
    match v {
        Value::String(x) => x.parse().unwrap(),
        x => x.to_string().parse().unwrap(),
    }
}

/// Positions minted by the contract test that produced each vector
/// (`test_vectors_*` in `test/extensions/MEVCaptureV21Rules.t.sol`).
fn positions(name: &str) -> Vec<(i32, i32, i128)> {
    let wide = (-40 * S, 40 * S, L66);
    match name {
        "inc_exact_in_cut_bridge_rate"
        | "dec_toward_then_away_exact_in"
        | "inc_exact_out_after_anchor_update"
        | "dec_exact_out_partial"
        | "inc_exact_in_partial_mid_segment" => {
            vec![wide, (3 * S, 7 * S, L66), (-7 * S, -3 * S, L66)]
        }
        "exact_tick_state_dec_from_tick_T"
        | "inc_through_T_toward_uncut"
        | "dec_onto_T_tick_T_minus_1"
        | "exact_tick_state_inc_from_tick_T_minus_1"
        | "dec_onto_T_again"
        | "fee_only_1_wei_exact_in_at_T" => vec![wide, (3 * S, 7 * S, L66)],
        "bridge_25pct_exact_in" | "bridge_25pct_exact_out_dec" | "bridge_1ulp_exact_in" => {
            vec![wide, (2 * S, 3 * S, L66)]
        }
        "empty_words_skip0" | "return_toward_skip0" | "empty_words_skip3" => {
            vec![(-S, S, L66), (1000 * S, 1001 * S, L66)]
        }
        "cap_tail_to_max" => vec![
            (-20_000 * S, 20_000 * S, 1 << 40),
            (3000 * S, 3001 * S, 1_000_000_000),
        ],
        "segexp2_offgrid_ticks_inc" => {
            vec![wide, (3 * S, 7 * S, L66 * 2), (8 * S, 9 * S, L66)]
        }
        "spacing3000_negative_anchor_dec" | "spacing3000_negative_anchor_inc" => {
            vec![
                (-200 * 3000, 100 * 3000, L66),
                (-50 * 3000, -30 * 3000, L66),
            ]
        }
        _ => panic!("no position layout for {name}"),
    }
}

fn ticks(name: &str) -> Vec<Tick> {
    let mut net = BTreeMap::new();
    for (lo, hi, l) in positions(name) {
        *net.entry(lo).or_insert(0i128) += l;
        *net.entry(hi).or_insert(0i128) -= l;
    }
    net.into_iter()
        .map(|(index, liquidity_delta)| Tick {
            index,
            liquidity_delta,
        })
        .collect()
}

fn core_state(v: &Value) -> MevCaptureV21MainCoreState {
    MevCaptureV21MainCoreState {
        sqrt_ratio: sqrt_ratio_from_raw(s(&v["sqrtRatio"])),
        tick: s(&v["tick"]),
        liquidity: s(&v["liquidity"]),
    }
}

fn config(v: &Value) -> MevCaptureV21MainConfig {
    let c = &v["cfg"];
    MevCaptureV21MainConfig {
        half_life: s(&c["tau"]),
        slope_k: s(&c["slopeK"]),
        segment_exp: s(&c["segExp"]),
        j_lin: s(&c["jLin"]),
        max_fee: s(&c["maxFee"]),
        clamp_ticks: s(&c["clampTicks"]),
        m_gate: s(&c["mGate"]),
    }
}

fn pool(v: &Value) -> MevCaptureV21MainPool {
    let name = v["name"].as_str().unwrap();
    let config = config(v);
    let core = core_state(&v["before"]);
    MevCaptureV21MainPool::new(
        PoolKey {
            token0: Address::with_last_byte(1),
            token1: Address::with_last_byte(2),
            config: PoolConfig {
                extension: Address::with_last_byte(0xee),
                fee: s(&v["pool"]["fee"]),
                pool_type_config: TickSpacing(s(&v["pool"]["tickSpacing"])),
            },
        },
        config,
        MevCaptureV21MainPoolState {
            core,
            anchor: MevCaptureV21MainModel::new(config)
                .unwrap()
                .initialize(core.tick, 1),
        },
        ticks(name),
    )
    .unwrap_or_else(|e| panic!("{name}: {e}"))
}

fn vectors() -> Vec<Value> {
    let v: Value = serde_json::from_str(include_str!(
        "data/mevcapture-v21-main/v21-main-quoter-vectors.json"
    ))
    .unwrap();
    assert_eq!(v["branch"], "eku-1582/mevcapture-v21-main");
    v["vectors"].as_array().unwrap().clone()
}

#[test]
fn replays_every_contract_vector_exactly() {
    let vectors = vectors();
    assert_eq!(vectors.len(), 21);
    let mut calls_checked = 0;
    let (mut exact_in, mut exact_out, mut token0, mut token1, mut skip) = (0, 0, 0, 0, 0);
    for v in &vectors {
        let name = v["name"].as_str().unwrap();
        let pool = pool(v);
        let p = &v["params"];
        let params = MevCaptureV21MainSwapParams {
            is_token1: p["isToken1"].as_bool().unwrap(),
            amount: s(&p["amount"]),
            sqrt_ratio_limit: Some(sqrt_ratio_from_raw(s(&p["sqrtRatioLimit"]))),
            skip_ahead: s(&p["skipAhead"]),
        };
        if params.amount < 0 {
            exact_out += 1;
        } else {
            exact_in += 1;
        }
        if params.is_token1 {
            token1 += 1;
        } else {
            token0 += 1;
        }
        skip += usize::from(params.skip_ahead != 0);
        let swap = pool
            .swap_through_segments(core_state(&v["before"]), params, s(&v["anchorX16"]))
            .unwrap_or_else(|e| panic!("{name}: {e}"));

        let expected = v["calls"].as_array().unwrap();
        assert_eq!(swap.calls.len(), expected.len(), "{name}: call count");
        for (i, (c, e)) in swap.calls.iter().zip(expected).enumerate() {
            let ctx = format!("{name} call {i}");
            assert_eq!(
                sqrt_ratio_to_raw(c.sqrt_ratio_limit),
                s::<U256>(&e["limit"]),
                "{ctx}: limit"
            );
            assert_eq!(c.amount, s::<i128>(&e["amount"]), "{ctx}: amount");
            let (kind, sur) = match c.kind {
                MevCaptureV21MainCallKind::Charged { surcharge, .. } => ("charged", surcharge),
                MevCaptureV21MainCallKind::Toward => ("toward", 0),
                MevCaptureV21MainCallKind::Bridge => ("bridge", 0),
                MevCaptureV21MainCallKind::PassThrough => ("passThrough", 0),
            };
            assert_eq!(kind, e["kind"].as_str().unwrap(), "{ctx}: kind");
            assert_eq!(sur, s::<u64>(&e["surcharge"]), "{ctx}: surcharge");
            assert_eq!(c.state_before, core_state(&e["before"]), "{ctx}: before");
            assert_eq!(c.state_after, core_state(&e["after"]), "{ctx}: after");
            assert_eq!(c.delta0, s::<i128>(&e["delta0"]), "{ctx}: delta0");
            assert_eq!(c.delta1, s::<i128>(&e["delta1"]), "{ctx}: delta1");
            assert_eq!(c.surcharge0, s::<u128>(&e["fee0"]), "{ctx}: fee0");
            assert_eq!(c.surcharge1, s::<u128>(&e["fee1"]), "{ctx}: fee1");
            calls_checked += 1;
        }
        assert_eq!(
            swap.delta0,
            s::<i128>(&v["total"]["delta0"]),
            "{name}: total0"
        );
        assert_eq!(
            swap.delta1,
            s::<i128>(&v["total"]["delta1"]),
            "{name}: total1"
        );
        assert_eq!(
            swap.state_after.core,
            core_state(&v["after"]),
            "{name}: after"
        );
        assert_eq!(
            swap.surcharge0 + swap.surcharge1,
            swap.calls
                .iter()
                .map(|c| c.surcharge0 + c.surcharge1)
                .sum::<u128>()
        );
    }
    assert_eq!(calls_checked, 266);
    assert!(exact_in > 0 && exact_out > 0 && token0 > 0 && token1 > 0 && skip > 0);
}

/// The vector kinds the indexer has to attribute: every charged call with a nonzero fee is one
/// `FeesAccumulated` event on the calculated token, bridges and toward calls never are.
#[test]
fn surcharge_events_match_charged_calls() {
    for v in &vectors() {
        let name = v["name"].as_str().unwrap();
        let p = &v["params"];
        let is_token1 = p["isToken1"].as_bool().unwrap();
        for e in v["calls"].as_array().unwrap() {
            let (f0, f1) = (s::<u128>(&e["fee0"]), s::<u128>(&e["fee1"]));
            if e["kind"] != "charged" {
                assert_eq!(f0 + f1, 0, "{name}: uncharged call with a fee");
            }
            if is_token1 {
                assert_eq!(f1, 0, "{name}");
            } else {
                assert_eq!(f0, 0, "{name}");
            }
        }
    }
}

#[test]
fn pred_succ_cross_regions() {
    for raw in [
        (U256::from(1) << 94) | (U256::from(1) << 62),
        (U256::from(2) << 94) | (U256::from(1) << 62),
        (U256::from(3) << 94) | (U256::from(1) << 62),
        U256::from(1u64 << 63),
    ] {
        let x = sqrt_ratio_from_raw(raw);
        assert_eq!(succ_sqrt_ratio(pred_sqrt_ratio(x)), x);
        assert!(pred_sqrt_ratio(x) < x && is_valid_sqrt_ratio(pred_sqrt_ratio(x)));
        assert!(succ_sqrt_ratio(x) > x && is_valid_sqrt_ratio(succ_sqrt_ratio(x)));
        assert_eq!(sqrt_ratio_to_raw(x), raw);
    }
}

fn anchor(v: &Value) -> MevCaptureV21MainAnchor {
    MevCaptureV21MainAnchor {
        last_update_time: s(&v["lastUpdateTime"]),
        l_ref_time: s(&v["lRefTime"]),
        last_pos_time: s(&v["lastPosTime"]),
        l_ref_bits: s(&v["lRefBits"]),
        snap_bits: s(&v["snapBits"]),
        l_ref_raise_time: s(&v["lRefRaiseTime"]),
        anchor_x16: s(&v["anchorX16"]),
    }
}

fn anchor_model(v: &Value) -> MevCaptureV21MainModel {
    let c = &v["config"];
    MevCaptureV21MainModel::new(MevCaptureV21MainConfig {
        half_life: s(&c["halfLife"]),
        slope_k: s(&c["slopeK"]),
        segment_exp: s(&c["segmentExp"]),
        j_lin: s(&c["jLin"]),
        // the `next` tuple's Q0.16 maxFee; the anchor update does not read it
        max_fee: s::<u64>(&c["maxFee"]) << 48,
        clamp_ticks: s(&c["clampTicks"]),
        m_gate: s(&c["mGate"]),
    })
    .unwrap()
}

/// `_anchorUpdate`, `_refresh` and `beforeUpdatePosition` are byte-identical between the `main`
/// extension and the merged `next` one (`da368348`), so its fixtures apply unchanged.
#[test]
fn anchor_updates_all_seven_fields() {
    let v: Value =
        serde_json::from_str(include_str!("data/mevcapture-v21-main/anchorUpdates.json")).unwrap();
    let m = anchor_model(&v);
    let cases = v["anchorUpdates"].as_array().unwrap();
    assert_eq!(cases.len(), 120);
    for (i, c) in cases.iter().enumerate() {
        let mut state = anchor(&c["stateIn"]);
        let gate = m
            .before_swap(
                &mut state,
                s(&c["tick"]),
                s(&c["liquidity"]),
                s(&c["timestamp"]),
            )
            .unwrap();
        assert_eq!(gate.passed, c["passed"].as_bool().unwrap(), "case {i}");
        assert_eq!(gate.l_obs, s::<u8>(&c["lObs"]), "case {i}");
        assert_eq!(gate.e_ref, s::<u8>(&c["eRef"]), "case {i}");
        assert_eq!(state, anchor(&c["expected"]), "case {i}");
    }
}

#[test]
fn gate_scenarios_all_steps() {
    let v: Value =
        serde_json::from_str(include_str!("data/mevcapture-v21-main/gateScenarios.json")).unwrap();
    let m = anchor_model(&v);
    let mut count = 0;
    for c in v["gateScenarios"].as_array().unwrap() {
        let mut state = anchor(&c["initial"]);
        for (i, st) in c["steps"].as_array().unwrap().iter().enumerate() {
            let now = s(&st["timestamp"]);
            if st["op"] == "position" {
                m.before_position(&mut state, s(&st["activeLiquidity"]), now);
            } else {
                let gate = m.before_swap(&mut state, s(&st["tick"]), s(&st["liquidity"]), now);
                assert_eq!(gate.is_some(), st["first"].as_bool().unwrap());
                if let Some(g) = gate {
                    assert_eq!(g.passed, st["passed"].as_bool().unwrap());
                    assert_eq!(g.l_obs, s::<u8>(&st["lObs"]));
                    assert_eq!(g.e_ref, s::<u8>(&st["eRef"]));
                }
                m.after_swap(&mut state, s(&st["liquidityAfter"]), now);
            }
            assert_eq!(state, anchor(&st["expected"]), "{} step {i}", c["name"]);
            count += 1;
        }
    }
    assert_eq!(count, 1785);
}

/// `Pool::quote` runs the first-touch anchor update before the segments and the refresh after.
#[test]
fn quote_runs_anchor_update_then_segments() {
    use ekubo_sdk::quoting::types::{Pool, QuoteParams, TokenAmount};
    let v = vectors()
        .into_iter()
        .find(|v| v["name"] == "inc_exact_in_cut_bridge_rate")
        .unwrap();
    let pool = pool(&v);
    let token1 = pool.key().token1;
    let quote = |meta| {
        pool.quote(QuoteParams {
            token_amount: TokenAmount {
                token: token1,
                amount: 1_000_000_000_000_000_000,
            },
            sqrt_ratio_limit: None,
            override_state: None,
            meta,
        })
        .unwrap()
    };
    // same timestamp as initialization: no update, anchor at the initial tick (0)
    let same = quote(1);
    let direct = pool
        .swap_through_segments(
            pool.state().core,
            MevCaptureV21MainSwapParams {
                is_token1: true,
                amount: 1_000_000_000_000_000_000,
                sqrt_ratio_limit: None,
                skip_ahead: 0,
            },
            0,
        )
        .unwrap();
    assert_eq!(same.consumed_amount, direct.delta1);
    assert_eq!(same.calculated_amount, direct.delta0.unsigned_abs());
    assert_eq!(same.execution_resources.anchor_updates, 0);
    assert!(direct.surcharge0 > 0);
    // a later timestamp runs the gate (passes: lObs 67 + mGate >= eRef 0)
    let later = quote(13);
    assert_eq!(later.execution_resources.anchor_updates, 1);
    assert_eq!(later.state_after.anchor.last_update_time, 13);
}
