//! EVM MEVCapture v2.1: anchor state machine, away schedule and an exact executable pool
//! (`MevCaptureV21Pool`), separate from the v1 wrapper. Configuration must be read from the
//! extension's `getConfig` tuple; fees are contract Q0.16 (`fee_q16_to_q64` converts).

use crate::{
    chain::{Chain, evm::Evm},
    math::{
        swap::{ComputeStepError, compute_step},
        tick::{sqrt_ratio_to_tick, to_sqrt_ratio},
        twamm::exp2::exp2,
    },
    private,
    quoting::{
        pools::{
            CommonPoolConstructionError, CommonPoolQuoteError, ensure_valid_token_order, is_token1,
        },
        types::{BlockTimestamp, Pool, PoolConfig, PoolKey, PoolState, Quote, QuoteParams, Tick},
    },
};
use alloc::vec::Vec;
use derive_more::{Add, AddAssign, Sub, SubAssign};
use ruint::aliases::U256;
use thiserror::Error;

/// The exact `getConfig` tuple. Fees are contract Q0.16, not SDK Q0.64.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
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

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Error)]
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
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
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
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct AnchorGateResult {
    pub passed: bool,
    pub l_obs: u8,
    pub e_ref: u8,
}

/// Validated anchor state machine. No default deployment/config assumptions.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
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

/// `MAX_TICK_SPACING_EXP` of the v2.1 Core.
pub const MEV_CAPTURE_V21_MAX_TICK_SPACING_EXP: u8 = 19;
/// `TICK_BITMAP_STORAGE_OFFSET` of the v2.1 Core.
const TICK_BITMAP_STORAGE_OFFSET: i64 = 89_421_695;

/// Pool type configuration of a v2.1 concentrated pool: spacing is `1 << tick_spacing_exp`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct MevCaptureV21PoolTypeConfig {
    pub tick_spacing_exp: u8,
}

/// Pool key with the contract Q0.16 pool fee (`PoolConfig.fee()` of the v2.1 Core).
pub type MevCaptureV21PoolKey = PoolKey<<Evm as Chain>::Address, u16, MevCaptureV21PoolTypeConfig>;

/// Core pool state. `sqrt_ratio` is the SDK's fixed-point (64.128) value of the contract's
/// compressed 96-bit `SqrtRatio`; `tick` is Core's stored tick, which can differ from
/// `sqrt_ratio_to_tick(sqrt_ratio)` by one after a decreasing swap stops on a tick.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct MevCaptureV21CoreState {
    pub sqrt_ratio: U256,
    pub tick: i32,
    pub liquidity: u128,
}

/// Core pool state plus all seven `getAnchor` fields.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct MevCaptureV21PoolState {
    pub core: MevCaptureV21CoreState,
    pub anchor: MevCaptureV21Anchor,
}

impl PoolState for MevCaptureV21PoolState {
    fn sqrt_ratio(&self) -> U256 {
        self.core.sqrt_ratio
    }

    fn liquidity(&self) -> u128 {
        self.core.liquidity
    }
}

/// Execution resources of one forwarded swap.
#[derive(Clone, Copy, Default, Debug, PartialEq, Eq, Hash, Add, AddAssign, Sub, SubAssign)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct MevCaptureV21PoolResources {
    /// `CORE.swap` calls made by the extension (toward, away segments or pass-through).
    pub core_calls: u32,
    /// Core swap loop iterations, summed over calls (one bitmap search each).
    pub core_steps: u32,
    /// Initialized ticks crossed, summed over calls.
    pub initialized_ticks_crossed: u32,
    /// 1 when this swap runs the first-touch anchor update of its timestamp.
    pub anchor_updates: u32,
    /// 1 when the extension writes its pool state.
    pub state_writes: u32,
}

/// Role of a Core call made by the extension.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum MevCaptureV21CallKind {
    /// Zero amount or price already at the user limit: the user's parameters are forwarded.
    PassThrough,
    /// The call toward the anchor, charged only the user's `minFee`.
    Toward,
    /// Away segment `k` (1-based).
    Away { k: u32 },
}

/// One `CORE.swap` call, with the exact parameters the extension passes.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct MevCaptureV21CoreCall {
    pub kind: MevCaptureV21CallKind,
    /// Fixed-point limit; always representable as a contract `SqrtRatio`.
    pub sqrt_ratio_limit: U256,
    /// Contract Q0.16 `minFee`; Core charges `max(poolFee, min_fee)`.
    pub min_fee: u16,
    /// The remaining specified amount passed to Core.
    pub amount: i128,
    pub delta0: i128,
    pub delta1: i128,
    pub fees_paid: u128,
    pub state_after: MevCaptureV21CoreState,
    pub steps: u32,
    pub initialized_ticks_crossed: u32,
}

/// User swap parameters forwarded to the extension.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct MevCaptureV21SwapParams {
    pub is_token1: bool,
    /// Positive for exact input, negative for exact output.
    pub amount: i128,
    /// Fixed-point limit; `None` is the contract default (minimum or maximum sqrt ratio).
    pub sqrt_ratio_limit: Option<U256>,
    /// Contract Q0.16 user `minFee`.
    pub min_fee: u16,
    pub skip_ahead: u32,
}

/// Full simulation of one forwarded swap.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MevCaptureV21Swap {
    /// `Some` on the first swap of a timestamp; `passed == false` emits `AnchorGateFailed`.
    pub gate: Option<AnchorGateResult>,
    pub calls: Vec<MevCaptureV21CoreCall>,
    pub delta0: i128,
    pub delta1: i128,
    pub fees_paid: u128,
    pub state_after: MevCaptureV21PoolState,
    pub resources: MevCaptureV21PoolResources,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, Error)]
pub enum MevCaptureV21PoolConstructionError {
    #[error(transparent)]
    Common(#[from] CommonPoolConstructionError),
    #[error(transparent)]
    InvalidConfig(#[from] InvalidConfig),
    #[error("extension must be non-zero")]
    MissingExtension,
    #[error("pool fee must be non-zero and below maxFee")]
    InvalidPoolFee,
    #[error("tick spacing exponent too large")]
    InvalidTickSpacingExp,
    #[error("invalid sqrt ratio or tick")]
    InvalidPrice,
    #[error("ticks must be sorted, unique, in range and multiples of the tick spacing")]
    InvalidTicks,
    #[error("active liquidity does not match the ticks at or below the current tick")]
    ActiveLiquidityMismatch,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, Error)]
pub enum MevCaptureV21QuoteError {
    #[error(transparent)]
    Common(#[from] CommonPoolQuoteError),
    /// `InvalidSqrtRatioLimit` in Core.
    #[error("invalid price limit")]
    InvalidSqrtRatioLimit,
    /// `SqrtRatioLimitWrongDirection` in Core.
    #[error("price limit in the wrong direction")]
    SqrtRatioLimitWrongDirection,
    #[error("invalid tick {0}")]
    InvalidTick(i32),
    #[error("failed swap step computation")]
    FailedComputeSwapStep(#[from] ComputeStepError),
    /// A checked int128 sum or remaining-amount subtraction overflowed (the contract reverts).
    #[error("signed amount overflow")]
    AmountOverflow,
    #[error("liquidity overflow")]
    LiquidityOverflow,
}

/// Contract Q0.16 fee as the SDK's EVM Q0.64 fee; lossless.
#[must_use]
pub fn fee_q16_to_q64(fee: u16) -> u64 {
    u64::from(fee) << 48
}

/// Whether a fixed-point sqrt ratio is a valid contract `SqrtRatio` (`isValid` after compression).
#[must_use]
pub fn is_valid_sqrt_ratio(sqrt_ratio: U256) -> bool {
    sqrt_ratio >= Evm::min_sqrt_ratio()
        && sqrt_ratio <= Evm::max_sqrt_ratio()
        && Evm::adjust_sqrt_ratio_precision(sqrt_ratio) == sqrt_ratio
}

/// Emulation of the v2.1 Core concentrated-liquidity swap over a known set of initialized ticks.
struct CoreSwap<'a> {
    ticks: &'a [Tick],
    spacing_exp: u8,
    skip_ahead: u32,
}

struct CoreSwapResult {
    delta0: i128,
    delta1: i128,
    fees_paid: u128,
    state: MevCaptureV21CoreState,
    steps: u32,
    crossed: u32,
}

impl CoreSwap<'_> {
    fn raw(&self, tick: i64) -> i64 {
        (tick >> self.spacing_exp) + TICK_BITMAP_STORAGE_OFFSET
    }

    fn tick_of(&self, raw: i64) -> i64 {
        (raw - TICK_BITMAP_STORAGE_OFFSET) << self.spacing_exp
    }

    /// `findNextInitializedTick`; returns the tick and the index of the initialized tick, if any.
    fn next(&self, from: i32) -> (i32, Option<usize>) {
        let mut next = i64::from(from);
        let mut skip = self.skip_ahead;
        loop {
            let raw = self.raw(next + (1 << self.spacing_exp));
            let word_end = (raw >> 8 << 8) + 255;
            let i = self
                .ticks
                .partition_point(|t| self.raw(i64::from(t.index)) < raw);
            if let Some(t) = self.ticks.get(i)
                && self.raw(i64::from(t.index)) <= word_end
            {
                return (t.index, Some(i));
            }
            next = self.tick_of(word_end);
            if next >= i64::from(Evm::max_tick()) {
                return (Evm::max_tick(), None);
            }
            if skip == 0 {
                return (next as i32, None);
            }
            skip -= 1;
        }
    }

    /// `findPrevInitializedTick`.
    fn prev(&self, from: i32) -> (i32, Option<usize>) {
        let mut prev = i64::from(from);
        let mut skip = self.skip_ahead;
        loop {
            let raw = self.raw(prev);
            let word_start = raw >> 8 << 8;
            let i = self
                .ticks
                .partition_point(|t| self.raw(i64::from(t.index)) <= raw);
            if i > 0 && self.raw(i64::from(self.ticks[i - 1].index)) >= word_start {
                return (self.ticks[i - 1].index, Some(i - 1));
            }
            prev = self.tick_of(word_start);
            if prev <= i64::from(Evm::min_tick()) {
                return (Evm::min_tick(), None);
            }
            if skip == 0 {
                return (prev as i32, None);
            }
            skip -= 1;
            prev -= 1;
        }
    }

    /// `Core.swap` for a concentrated pool, using the SDK's step math with the Q0.64 form of
    /// `max(pool_fee, min_fee)`.
    #[allow(clippy::too_many_arguments)]
    fn swap(
        &self,
        state: MevCaptureV21CoreState,
        pool_fee: u16,
        min_fee: u16,
        is_token1: bool,
        amount: i128,
        limit: U256,
    ) -> Result<CoreSwapResult, MevCaptureV21QuoteError> {
        if !is_valid_sqrt_ratio(limit) {
            return Err(MevCaptureV21QuoteError::InvalidSqrtRatioLimit);
        }
        let mut result = CoreSwapResult {
            delta0: 0,
            delta1: 0,
            fees_paid: 0,
            state,
            steps: 0,
            crossed: 0,
        };
        if amount == 0 || state.sqrt_ratio == limit {
            return Ok(result);
        }
        let fee = fee_q16_to_q64(pool_fee.max(min_fee));
        let exact_out = amount < 0;
        let increasing = is_token1 != exact_out;
        if (limit < state.sqrt_ratio) == increasing {
            return Err(MevCaptureV21QuoteError::SqrtRatioLimitWrongDirection);
        }

        let MevCaptureV21CoreState {
            mut sqrt_ratio,
            mut tick,
            mut liquidity,
        } = state;
        let mut remaining = amount;
        let mut calculated: u128 = 0;
        loop {
            let (next_tick, initialized) = if increasing {
                self.next(tick)
            } else {
                self.prev(tick)
            };
            let next_ratio = to_sqrt_ratio::<Evm>(next_tick)
                .ok_or(MevCaptureV21QuoteError::InvalidTick(next_tick))?;
            let limited = if increasing {
                next_ratio.min(limit)
            } else {
                next_ratio.max(limit)
            };
            let step =
                compute_step::<Evm>(sqrt_ratio, liquidity, limited, remaining, is_token1, fee)?;
            remaining = remaining
                .checked_sub(step.consumed_amount)
                .ok_or(MevCaptureV21QuoteError::AmountOverflow)?;
            calculated = calculated
                .checked_add(step.calculated_amount)
                .ok_or(MevCaptureV21QuoteError::AmountOverflow)?;
            result.fees_paid = result.fees_paid.saturating_add(step.fee_amount);
            result.steps += 1;

            if step.sqrt_ratio_next == next_ratio {
                sqrt_ratio = next_ratio;
                tick = next_tick - i32::from(!increasing);
                if let Some(i) = initialized {
                    let delta = self.ticks[i].liquidity_delta;
                    let delta = if increasing {
                        Some(delta)
                    } else {
                        delta.checked_neg()
                    };
                    liquidity = delta
                        .and_then(|d| liquidity.checked_add_signed(d))
                        .ok_or(MevCaptureV21QuoteError::LiquidityOverflow)?;
                    result.crossed += 1;
                }
            } else if step.sqrt_ratio_next != sqrt_ratio {
                sqrt_ratio = step.sqrt_ratio_next;
                tick = sqrt_ratio_to_tick::<Evm>(sqrt_ratio);
            }

            if remaining == 0 || sqrt_ratio == limit {
                break;
            }
        }

        let specified = amount
            .checked_sub(remaining)
            .ok_or(MevCaptureV21QuoteError::AmountOverflow)?;
        // `toInt128(max(type(int128).min, calculatedAmount))`
        let calculated = if exact_out {
            i128::try_from(calculated).map_err(|_| MevCaptureV21QuoteError::AmountOverflow)?
        } else if calculated >= 1 << 127 {
            i128::MIN
        } else {
            -(calculated as i128)
        };
        (result.delta0, result.delta1) = if is_token1 {
            (calculated, specified)
        } else {
            (specified, calculated)
        };
        result.state = MevCaptureV21CoreState {
            sqrt_ratio,
            tick,
            liquidity,
        };
        Ok(result)
    }
}

/// A concentrated pool behind MEVCapture v2.1 on the v2.1 Core.
///
/// Quotes are exact for the given initialized ticks: Core's bitmap steps (including
/// uninitialized word boundaries and `skipAhead`) are emulated because each step rounds fees
/// separately. Ticks outside the fetched range must be supplied for swaps that reach them.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MevCaptureV21Pool {
    key: MevCaptureV21PoolKey,
    model: MevCaptureV21Model,
    state: MevCaptureV21PoolState,
    sorted_ticks: Vec<Tick>,
}

impl MevCaptureV21Pool {
    /// `config` must be the extension's `getConfig` tuple and `state.anchor` its `getAnchor`.
    /// `sorted_ticks` are the initialized ticks with their net liquidity deltas; a referenced
    /// tick whose net delta is zero is still initialized and must be included.
    pub fn new(
        key: MevCaptureV21PoolKey,
        config: MevCaptureV21Config,
        state: MevCaptureV21PoolState,
        sorted_ticks: Vec<Tick>,
    ) -> Result<Self, MevCaptureV21PoolConstructionError> {
        ensure_valid_token_order(&key)?;
        let model = MevCaptureV21Model::new(config)?;
        let PoolConfig {
            extension,
            fee,
            pool_type_config: MevCaptureV21PoolTypeConfig { tick_spacing_exp },
        } = key.config;
        if extension.is_zero() {
            return Err(MevCaptureV21PoolConstructionError::MissingExtension);
        }
        if fee == 0 || fee >= config.max_fee {
            return Err(MevCaptureV21PoolConstructionError::InvalidPoolFee);
        }
        if tick_spacing_exp > MEV_CAPTURE_V21_MAX_TICK_SPACING_EXP {
            return Err(MevCaptureV21PoolConstructionError::InvalidTickSpacingExp);
        }
        let core = state.core;
        // Core's tick is floor(price), or one less after a decreasing swap stopped on a tick.
        let tick_ratio = to_sqrt_ratio::<Evm>(core.tick);
        let next_ratio = core.tick.checked_add(1).and_then(to_sqrt_ratio::<Evm>);
        if !is_valid_sqrt_ratio(core.sqrt_ratio)
            || tick_ratio.is_none_or(|r| r > core.sqrt_ratio)
            || next_ratio.is_some_and(|r| r < core.sqrt_ratio)
        {
            return Err(MevCaptureV21PoolConstructionError::InvalidPrice);
        }
        let spacing_mask = (1i32 << tick_spacing_exp) - 1;
        let mut active: u128 = 0;
        for (i, t) in sorted_ticks.iter().enumerate() {
            if t.index & spacing_mask != 0
                || t.index < Evm::min_tick()
                || t.index > Evm::max_tick()
                || i > 0 && sorted_ticks[i - 1].index >= t.index
            {
                return Err(MevCaptureV21PoolConstructionError::InvalidTicks);
            }
            if t.index <= core.tick {
                active = active
                    .checked_add_signed(t.liquidity_delta)
                    .ok_or(MevCaptureV21PoolConstructionError::ActiveLiquidityMismatch)?;
            }
        }
        if active != core.liquidity {
            return Err(MevCaptureV21PoolConstructionError::ActiveLiquidityMismatch);
        }
        Ok(Self {
            key,
            model,
            state,
            sorted_ticks,
        })
    }

    pub fn model(&self) -> &MevCaptureV21Model {
        &self.model
    }

    pub fn ticks(&self) -> &[Tick] {
        &self.sorted_ticks
    }

    /// Simulates `forward` exactly: first-touch anchor update, toward call, away segments with
    /// sqrt-ratio membership, checked signed sums and the post-swap reference refresh.
    pub fn simulate_swap(
        &self,
        state: MevCaptureV21PoolState,
        params: MevCaptureV21SwapParams,
        now: u32,
    ) -> Result<MevCaptureV21Swap, MevCaptureV21QuoteError> {
        let increasing = params.is_token1 != (params.amount < 0);
        let user_limit = params.sqrt_ratio_limit.unwrap_or(if increasing {
            Evm::max_sqrt_ratio()
        } else {
            Evm::min_sqrt_ratio()
        });
        if !is_valid_sqrt_ratio(user_limit) {
            return Err(MevCaptureV21QuoteError::InvalidSqrtRatioLimit);
        }
        let config = self.model.config();
        let pool_fee = self.key.config.fee;
        let spacing_exp = self.key.config.pool_type_config.tick_spacing_exp;
        let core = CoreSwap {
            ticks: &self.sorted_ticks,
            spacing_exp,
            skip_ahead: params.skip_ahead,
        };

        let mut anchor = state.anchor;
        let gate = self
            .model
            .before_swap(&mut anchor, state.core.tick, state.core.liquidity, now);

        let mut calls = Vec::new();
        let mut current = state.core;
        let mut remaining = params.amount;
        let mut sum0: i128 = 0;
        let mut sum1: i128 = 0;
        let mut call = |kind,
                        limit: U256,
                        min_fee: u16,
                        remaining: &mut i128,
                        current: &mut MevCaptureV21CoreState,
                        sum0: &mut i128,
                        sum1: &mut i128|
         -> Result<(), MevCaptureV21QuoteError> {
            let r = core.swap(
                *current,
                pool_fee,
                min_fee,
                params.is_token1,
                *remaining,
                limit,
            )?;
            calls.push(MevCaptureV21CoreCall {
                kind,
                sqrt_ratio_limit: limit,
                min_fee,
                amount: *remaining,
                delta0: r.delta0,
                delta1: r.delta1,
                fees_paid: r.fees_paid,
                state_after: r.state,
                steps: r.steps,
                initialized_ticks_crossed: r.crossed,
            });
            *sum0 = sum0
                .checked_add(r.delta0)
                .ok_or(MevCaptureV21QuoteError::AmountOverflow)?;
            *sum1 = sum1
                .checked_add(r.delta1)
                .ok_or(MevCaptureV21QuoteError::AmountOverflow)?;
            *remaining = remaining
                .checked_sub(if params.is_token1 { r.delta1 } else { r.delta0 })
                .ok_or(MevCaptureV21QuoteError::AmountOverflow)?;
            *current = r.state;
            Ok(())
        };

        if remaining == 0 || current.sqrt_ratio == user_limit {
            call(
                MevCaptureV21CallKind::PassThrough,
                user_limit,
                params.min_fee,
                &mut remaining,
                &mut current,
                &mut sum0,
                &mut sum1,
            )?;
        } else {
            let toward_tick = self.model.toward_tick(anchor.anchor_x16, increasing);
            let anchor_ratio = to_sqrt_ratio::<Evm>(toward_tick)
                .ok_or(MevCaptureV21QuoteError::InvalidTick(toward_tick))?;
            let mut done = false;
            if (current.sqrt_ratio < anchor_ratio) == increasing
                && current.sqrt_ratio != anchor_ratio
            {
                let limit = if increasing {
                    anchor_ratio.min(user_limit)
                } else {
                    anchor_ratio.max(user_limit)
                };
                call(
                    MevCaptureV21CallKind::Toward,
                    limit,
                    params.min_fee,
                    &mut remaining,
                    &mut current,
                    &mut sum0,
                    &mut sum1,
                )?;
                // N1: otherwise the away loop starts from the toward call's rounded limit.
                done = remaining == 0 || limit == user_limit || current.sqrt_ratio != limit;
            }
            if !done {
                let schedule = self
                    .model
                    .away_schedule(
                        anchor.anchor_x16,
                        current.tick,
                        increasing,
                        pool_fee,
                        spacing_exp,
                    )
                    .map_err(|_| MevCaptureV21QuoteError::InvalidTick(current.tick))?;
                let mut n: u32 = 0;
                for segment in schedule {
                    let mut limit = user_limit;
                    if segment.fee != config.max_fee && n != u32::from(config.max_segments) - 1 {
                        let hi_tick = segment.hi_x16 >> 16;
                        if hi_tick <= i128::from(Evm::max_tick()) {
                            let tick = if increasing { hi_tick } else { -hi_tick } as i32;
                            let boundary = to_sqrt_ratio::<Evm>(tick)
                                .ok_or(MevCaptureV21QuoteError::InvalidTick(tick))?;
                            // membership is by sqrt ratio: skip a boundary the price sits on
                            if (boundary <= current.sqrt_ratio) == increasing
                                || boundary == current.sqrt_ratio
                            {
                                continue;
                            }
                            limit = if increasing {
                                boundary.min(user_limit)
                            } else {
                                boundary.max(user_limit)
                            };
                        }
                    }
                    call(
                        MevCaptureV21CallKind::Away { k: segment.k },
                        limit,
                        segment.fee.max(params.min_fee),
                        &mut remaining,
                        &mut current,
                        &mut sum0,
                        &mut sum1,
                    )?;
                    n += 1;
                    if remaining == 0 || limit == user_limit || current.sqrt_ratio != limit {
                        break;
                    }
                }
            }
        }

        self.model.after_swap(&mut anchor, current.liquidity, now);

        let mut resources = MevCaptureV21PoolResources {
            core_calls: calls.len() as u32,
            anchor_updates: u32::from(gate.is_some()),
            state_writes: u32::from(anchor != state.anchor),
            ..Default::default()
        };
        let mut fees_paid: u128 = 0;
        for c in &calls {
            resources.core_steps += c.steps;
            resources.initialized_ticks_crossed += c.initialized_ticks_crossed;
            fees_paid = fees_paid.saturating_add(c.fees_paid);
        }
        Ok(MevCaptureV21Swap {
            gate,
            calls,
            delta0: sum0,
            delta1: sum1,
            fees_paid,
            state_after: MevCaptureV21PoolState {
                core: current,
                anchor,
            },
            resources,
        })
    }
}

impl AsRef<Self> for MevCaptureV21Pool {
    fn as_ref(&self) -> &Self {
        self
    }
}

impl Pool for MevCaptureV21Pool {
    type Address = <Evm as Chain>::Address;
    type Fee = u16;
    type Resources = MevCaptureV21PoolResources;
    type State = MevCaptureV21PoolState;
    type QuoteError = MevCaptureV21QuoteError;
    type Meta = BlockTimestamp;
    type PoolTypeConfig = MevCaptureV21PoolTypeConfig;

    fn key(&self) -> MevCaptureV21PoolKey {
        self.key
    }

    fn state(&self) -> Self::State {
        self.state
    }

    /// Quotes with a zero user `minFee` and `skipAhead`; use [`MevCaptureV21Pool::simulate_swap`]
    /// for other parameters and per-call records.
    fn quote(
        &self,
        params: QuoteParams<Self::Address, Self::State, Self::Meta>,
    ) -> Result<Quote<Self::Resources, Self::State>, Self::QuoteError> {
        let is_token1 = is_token1(&self.key, params.token_amount.token)?;
        let amount = params.token_amount.amount;
        let swap = self.simulate_swap(
            params.override_state.unwrap_or(self.state),
            MevCaptureV21SwapParams {
                is_token1,
                amount,
                sqrt_ratio_limit: params.sqrt_ratio_limit,
                min_fee: 0,
                skip_ahead: 0,
            },
            params.meta as u32,
        )?;
        let (specified, calculated) = if is_token1 {
            (swap.delta1, swap.delta0)
        } else {
            (swap.delta0, swap.delta1)
        };
        Ok(Quote {
            is_price_increasing: is_token1 != (amount < 0),
            consumed_amount: specified,
            calculated_amount: calculated.unsigned_abs(),
            execution_resources: swap.resources,
            state_after: swap.state_after,
            fees_paid: swap.fees_paid,
        })
    }

    fn has_liquidity(&self) -> bool {
        self.state.core.liquidity > 0 || !self.sorted_ticks.is_empty()
    }

    fn max_tick_with_liquidity(&self) -> Option<i32> {
        self.sorted_ticks.last().map(|t| t.index)
    }

    fn min_tick_with_liquidity(&self) -> Option<i32> {
        self.sorted_ticks.first().map(|t| t.index)
    }

    fn is_path_dependent(&self) -> bool {
        true
    }
}

impl private::Sealed for MevCaptureV21Pool {}
impl private::Sealed for MevCaptureV21PoolState {}
