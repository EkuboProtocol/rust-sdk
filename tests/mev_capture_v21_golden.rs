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
