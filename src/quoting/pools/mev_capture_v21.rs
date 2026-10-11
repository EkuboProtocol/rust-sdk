//! EVM MEVCapture v2.1 state transitions, separate from the v1 wrapper.
//! Configuration must be read from the extension's `getConfig` tuple.

use crate::{
    chain::{Chain, evm::Evm},
    math::twamm::exp2::exp2,
};
use ruint::aliases::U256;
use thiserror::Error;

/// The exact `getConfig` tuple. Fees are contract Q0.16, not SDK Q0.64.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct MevCaptureV21Config {
    pub half_life: u32,
    pub slope_k: u8,
    pub segment_exp: u8,
    pub j_lin: u8,
    pub max_fee: u16,
    pub clamp_ticks: u32,
    pub m_gate: u8,
    pub max_segments: u8,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Error)]
#[error("invalid MEVCapture v2.1 configuration")]
pub struct InvalidConfig;

impl MevCaptureV21Config {
    /// Validate the deployed tuple against the merged contract constructor.
    pub fn validate(self) -> Result<Self, InvalidConfig> {
        if self.half_life == 0
            || self.half_life > 1 << 20
            || self.slope_k == 0
            || self.slope_k > 16
            || self.segment_exp > 8
            || self.j_lin == 0
            || self.j_lin > 64
            || self.max_fee == 0
            || self.max_fee > 1 << 15
            || self.clamp_ticks == 0
            || self.clamp_ticks > 2 * Evm::max_tick() as u32
            || self.m_gate > 16
            || self.max_segments != self.j_lin + 24
            || ((u64::from(self.slope_k) * (u64::from(self.j_lin) + (1 << 24) - 3))
                << self.segment_exp)
                < 2 * (u64::from(self.max_fee) - 1)
        {
            return Err(InvalidConfig);
        }
        Ok(self)
    }
}

/// All seven fields returned by `getAnchor`, including snapshot and raise clocks.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct MevCaptureV21Anchor {
    pub last_update_time: u32,
    pub l_ref_time: u32,
    pub last_pos_time: u32,
    pub l_ref_bits: u8,
    pub snap_bits: u8,
    pub l_ref_raise_time: u32,
    pub anchor_x16: i64,
}

/// First-touch gate result; a failure corresponds to `AnchorGateFailed`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AnchorGateResult {
    pub passed: bool,
    pub l_obs: u8,
    pub e_ref: u8,
}

/// Validated anchor state machine. No default deployment/config assumptions.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MevCaptureV21Model {
    config: MevCaptureV21Config,
}

impl MevCaptureV21Model {
    pub fn new(config: MevCaptureV21Config) -> Result<Self, InvalidConfig> {
        Ok(Self {
            config: config.validate()?,
        })
    }

    pub fn config(&self) -> MevCaptureV21Config {
        self.config
    }

    pub fn initialize(&self, tick: i32, now: u32) -> MevCaptureV21Anchor {
        MevCaptureV21Anchor {
            last_update_time: now,
            l_ref_time: now,
            last_pos_time: 0,
            l_ref_bits: 0,
            snap_bits: 0,
            l_ref_raise_time: now.wrapping_sub(self.config.half_life),
            anchor_x16: i64::from(tick) << 16,
        }
    }

    pub fn before_position(&self, state: &mut MevCaptureV21Anchor, liquidity: u128, now: u32) {
        if state.last_pos_time != now {
            state.last_pos_time = now;
            state.snap_bits = bit_length(liquidity);
        }
    }

    fn decayed_reference(&self, state: MevCaptureV21Anchor, now: u32) -> u8 {
        let decay = now.wrapping_sub(state.l_ref_time) / self.config.half_life;
        u32::from(state.l_ref_bits).saturating_sub(decay) as u8
    }

    fn raise(&self, base: u8, observed: u8, now: u32, raise_time: u32) -> (u8, u32) {
        if observed > base && now.wrapping_sub(raise_time) >= self.config.half_life {
            (base + 1, now)
        } else {
            (base, raise_time)
        }
    }

    /// Update only on the first swap of a uint32 timestamp.
    pub fn before_swap(
        &self,
        state: &mut MevCaptureV21Anchor,
        tick: i32,
        liquidity: u128,
        now: u32,
    ) -> Option<AnchorGateResult> {
        if state.last_update_time == now {
            return None;
        }
        let dt = now.wrapping_sub(state.last_update_time);
        let l_obs = if state.last_pos_time == now {
            state.snap_bits
        } else {
            bit_length(liquidity)
        };
        let e_ref = self.decayed_reference(*state, now);
        let passed = u16::from(l_obs) + u16::from(self.config.m_gate) >= u16::from(e_ref);
        if passed {
            // i128 also accepts every int64 state without subtraction overflow.
            let offset = i128::from(state.anchor_x16) - (i128::from(tick) << 16);
            let magnitude = offset
                .unsigned_abs()
                .checked_shr(dt / self.config.half_life)
                .unwrap_or(0);
            let fraction =
                (u128::from(dt % self.config.half_life) << 64) / u128::from(self.config.half_life);
            let magnitude: u128 =
                ((U256::from(magnitude) << 64usize) / U256::from(exp2(fraction))).to();
            let decayed = if offset < 0 {
                -(magnitude as i128)
            } else {
                magnitude as i128
            };
            let limit = ((i128::from(self.config.clamp_ticks) << 16)
                * i128::from(dt.min(self.config.half_life)))
                / i128::from(self.config.half_life);
            state.anchor_x16 =
                (i128::from(state.anchor_x16) + (decayed - offset).clamp(-limit, limit)) as i64;
            // rev6 Q1: restore the stored reference before the H1 capped raise.
            let base = e_ref.max(state.l_ref_bits.min(l_obs));
            (state.l_ref_bits, state.l_ref_raise_time) =
                self.raise(base, l_obs, now, state.l_ref_raise_time);
            state.l_ref_time = now;
        }
        state.last_update_time = now;
        Some(AnchorGateResult {
            passed,
            l_obs,
            e_ref,
        })
    }

    pub fn after_swap(&self, state: &mut MevCaptureV21Anchor, liquidity: u128, now: u32) {
        if state.last_pos_time == now {
            return;
        }
        let e = self.decayed_reference(*state, now);
        let (raised, raise_time) =
            self.raise(e, bit_length(liquidity), now, state.l_ref_raise_time);
        if raised != e {
            state.l_ref_bits = raised;
            state.l_ref_time = now;
            state.l_ref_raise_time = raise_time;
        }
    }
}

fn bit_length(liquidity: u128) -> u8 {
    (128 - liquidity.leading_zeros()) as u8
}

/// A mathematical away segment in mirrored coordinates (Q16 ticks).
/// Execution must still test sqrt-ratio membership, not just integer ticks.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AwaySegment {
    pub k: u32,
    pub lo_x16: i128,
    pub hi_x16: i128,
    pub fee: u16,
}

/// Lazily traverses the absolute grid and then doubling-width segments.
/// Stops after the first capped-fee segment, whose execution limit is the user limit.
#[derive(Clone, Debug)]
pub struct AwaySchedule {
    config: MevCaptureV21Config,
    anchor: i128,
    g1: i128,
    g_j: i128,
    w_shift: u32,
    spacing_exp: u8,
    pool_fee: u16,
    k: u32,
    finished: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Error)]
#[error("invalid MEVCapture v2.1 pool fee or spacing exponent")]
pub struct InvalidSchedule;

impl MevCaptureV21Model {
    /// Construct the mathematical schedule; `core_tick` uses Core's boundary tick convention.
    pub fn away_schedule(
        &self,
        anchor_x16: i64,
        core_tick: i32,
        increasing: bool,
        pool_fee: u16,
        spacing_exp: u8,
    ) -> Result<AwaySchedule, InvalidSchedule> {
        if pool_fee == 0 || pool_fee >= self.config.max_fee || spacing_exp > 31 {
            return Err(InvalidSchedule);
        }
        let anchor = if increasing {
            i128::from(anchor_x16)
        } else {
            -i128::from(anchor_x16)
        };
        let w_shift = u32::from(spacing_exp) + u32::from(self.config.segment_exp) + 16;
        let g1 = ((anchor >> w_shift) + 1) << w_shift;
        let g_j = g1 + (i128::from(self.config.j_lin - 1) << w_shift);
        let p = if increasing {
            i128::from(core_tick)
        } else {
            -i128::from(core_tick) - 1
        };
        let p16 = p << 16;
        let k = if p16 < g1 {
            1
        } else if p16 < g_j {
            (((p16 - g1) >> w_shift) + 2) as u32
        } else {
            u32::from(self.config.j_lin) - 1
                + u32::from(bit_length((((p16 - g_j) >> w_shift) + 2) as u128))
        };
        Ok(AwaySchedule {
            config: self.config,
            anchor,
            g1,
            g_j,
            w_shift,
            spacing_exp,
            pool_fee,
            k,
            finished: false,
        })
    }

    /// Rounded toward limit: floor(anchor) increasing; ceil(anchor) decreasing.
    pub fn toward_tick(&self, anchor_x16: i64, increasing: bool) -> i32 {
        let a = i128::from(anchor_x16);
        let tick = if increasing { a >> 16 } else { -((-a) >> 16) };
        tick.clamp(i128::from(Evm::min_tick()), i128::from(Evm::max_tick())) as i32
    }
}

impl AwaySchedule {
    fn boundary(&self, k: u32) -> i128 {
        if k <= u32::from(self.config.j_lin) {
            self.g1 + (i128::from(k - 1) << self.w_shift)
        } else {
            self.g_j + (((1i128 << (k - u32::from(self.config.j_lin) + 1)) - 2) << self.w_shift)
        }
    }
}

impl Iterator for AwaySchedule {
    type Item = AwaySegment;
    fn next(&mut self) -> Option<Self::Item> {
        if self.finished {
            return None;
        }
        let lo = if self.k == 1 {
            self.anchor
        } else {
            self.boundary(self.k - 1)
        };
        let hi = self.boundary(self.k);
        let shift = u32::from(self.spacing_exp) + 18;
        let numerator = u128::from(self.config.slope_k)
            * u128::from(self.pool_fee)
            * (lo + hi - 2 * self.anchor) as u128;
        let fee = (u128::from(self.pool_fee) + ((numerator + (1 << shift) - 1) >> shift))
            .min(u128::from(self.config.max_fee)) as u16;
        let result = AwaySegment {
            k: self.k,
            lo_x16: lo,
            hi_x16: hi,
            fee,
        };
        self.k += 1;
        self.finished = fee == self.config.max_fee;
        Some(result)
    }
}
