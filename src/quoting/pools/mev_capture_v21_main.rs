//! EVM MEVCapture v2.1 on the current Core (`main` variant, EKU-946 rev 10 §(b-main)).
//!
//! The extension charges no `minFee`. Each charged Core call is cut one representable
//! `SqrtRatio` step short of the next initialized tick and its surcharge is added to the
//! calculated token through `Core.accumulateAsFees`; every initialized tick is crossed by its
//! own uncharged one-step bridge call. [`MevCaptureV21MainPool::simulate_swap`] reproduces the
//! extension's Core calls exactly with Core's integer arithmetic.

use crate::{
    chain::{
        Chain,
        evm::{EVM_MAX_TICK, EVM_MIN_TICK, Evm},
    },
    math::{
        swap::{ComputeStepError, amount_before_fee, compute_fee, compute_step},
        tick::{sqrt_ratio_to_tick, to_sqrt_ratio},
        twamm::exp2::exp2,
    },
    private,
    quoting::{
        pools::{
            CommonPoolConstructionError, CommonPoolQuoteError,
            concentrated::{ConcentratedPoolTypeConfig, TickSpacing},
            ensure_valid_token_order, is_token1,
        },
        types::{BlockTimestamp, Pool, PoolConfig, PoolKey, PoolState, Quote, QuoteParams, Tick},
    },
};
use alloc::vec::Vec;
use derive_more::{Add, AddAssign, Sub, SubAssign};
use ruint::aliases::U256;
use thiserror::Error;

/// `MAX_TICK_SPACING` of the current Core.
pub const MEV_CAPTURE_V21_MAIN_MAX_TICK_SPACING: u32 = 698_605;
/// `TICK_BITMAP_STORAGE_OFFSET` of the current Core.
const TICK_BITMAP_STORAGE_OFFSET: i64 = 89_421_695;

/// The extension's `getConfig` tuple (`segmentWidthMultiplier` is `1 << segment_exp`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct MevCaptureV21MainConfig {
    pub half_life: u32,
    pub slope_k: u8,
    pub segment_exp: u8,
    pub j_lin: u8,
    /// Q0.64, like the pool fee.
    pub max_fee: u64,
    pub clamp_ticks: u32,
    pub m_gate: u8,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Error)]
#[error("invalid MEVCapture v2.1 configuration")]
pub struct InvalidMainConfig;

impl MevCaptureV21MainConfig {
    /// The constructor's checks.
    pub fn validate(self) -> Result<Self, InvalidMainConfig> {
        if self.half_life == 0
            || self.half_life > 1 << 20
            || self.slope_k == 0
            || self.slope_k > 16
            || self.segment_exp > 8
            || self.j_lin == 0
            || self.j_lin > 64
            || self.max_fee == 0
            || self.max_fee > 1 << 63
            || self.clamp_ticks == 0
            || u64::from(self.clamp_ticks) > 2 * EVM_MAX_TICK as u64
            || self.m_gate > 16
        {
            return Err(InvalidMainConfig);
        }
        Ok(self)
    }
}

/// All seven fields returned by `getAnchor`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct MevCaptureV21MainAnchor {
    pub last_update_time: u32,
    pub l_ref_time: u32,
    pub last_pos_time: u32,
    pub l_ref_bits: u8,
    pub snap_bits: u8,
    pub l_ref_raise_time: u32,
    pub anchor_x16: i64,
}

/// First-touch gate result; a failure corresponds to `AnchorGateFailed(poolId, lObs, eRef)`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct MevCaptureV21MainGate {
    pub passed: bool,
    pub l_obs: u8,
    pub e_ref: u8,
}

/// Validated configuration with the anchor state machine and the away-segment arithmetic.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct MevCaptureV21MainModel {
    config: MevCaptureV21MainConfig,
}

fn bit_length(x: u128) -> u8 {
    (128 - x.leading_zeros()) as u8
}

impl MevCaptureV21MainModel {
    pub fn new(config: MevCaptureV21MainConfig) -> Result<Self, InvalidMainConfig> {
        Ok(Self {
            config: config.validate()?,
        })
    }

    pub fn config(&self) -> MevCaptureV21MainConfig {
        self.config
    }

    /// `beforeInitializePool`.
    pub fn initialize(&self, tick: i32, now: u32) -> MevCaptureV21MainAnchor {
        MevCaptureV21MainAnchor {
            last_update_time: now,
            l_ref_time: now,
            last_pos_time: 0,
            l_ref_bits: 0,
            snap_bits: 0,
            l_ref_raise_time: now.wrapping_sub(self.config.half_life),
            anchor_x16: i64::from(tick) << 16,
        }
    }

    /// `beforeUpdatePosition`: snapshot of the active liquidity, once per timestamp.
    pub fn before_position(&self, state: &mut MevCaptureV21MainAnchor, liquidity: u128, now: u32) {
        if state.last_pos_time != now {
            state.last_pos_time = now;
            state.snap_bits = bit_length(liquidity);
        }
    }

    fn decayed_reference(&self, state: MevCaptureV21MainAnchor, now: u32) -> u8 {
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

    /// `_anchorUpdate`, run only on the first swap of a timestamp; `None` otherwise.
    pub fn before_swap(
        &self,
        state: &mut MevCaptureV21MainAnchor,
        tick: i32,
        liquidity: u128,
        now: u32,
    ) -> Option<MevCaptureV21MainGate> {
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
            // rounds up on `main` (the `next` variant floors): every update that consumes elapsed
            // time grants at least one 2^-16 tick
            let half_life = i128::from(self.config.half_life);
            let limit = ((i128::from(self.config.clamp_ticks) << 16)
                * i128::from(dt.min(self.config.half_life))
                + half_life
                - 1)
                / half_life;
            state.anchor_x16 =
                (i128::from(state.anchor_x16) + (decayed - offset).clamp(-limit, limit)) as i64;
            let base = e_ref.max(state.l_ref_bits.min(l_obs));
            (state.l_ref_bits, state.l_ref_raise_time) =
                self.raise(base, l_obs, now, state.l_ref_raise_time);
            state.l_ref_time = now;
        }
        state.last_update_time = now;
        Some(MevCaptureV21MainGate {
            passed,
            l_obs,
            e_ref,
        })
    }

    /// `_refresh`: raises the reference from the liquidity after the swap.
    pub fn after_swap(&self, state: &mut MevCaptureV21MainAnchor, liquidity: u128, now: u32) {
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

/// Away segments in mirrored Q16 tick coordinates (the swap always moves toward larger values).
#[derive(Clone, Copy, Debug)]
struct Grid {
    w16: i128,
    g1: i128,
    g_j: i128,
    j_lin: u32,
}

impl Grid {
    fn new(a: i128, spacing: u32, config: MevCaptureV21MainConfig) -> Self {
        let w16 = i128::from(spacing) << (u32::from(config.segment_exp) + 16);
        let g1 = (a.div_euclid(w16) + 1) * w16;
        Self {
            w16,
            g1,
            g_j: g1 + i128::from(config.j_lin - 1) * w16,
            j_lin: u32::from(config.j_lin),
        }
    }

    /// `_boundary`.
    fn boundary(&self, k: u32) -> i128 {
        if k <= self.j_lin {
            self.g1 + i128::from(k - 1) * self.w16
        } else {
            self.g_j + ((1i128 << (k - self.j_lin + 1)) - 2) * self.w16
        }
    }

    /// `_firstSegment`.
    fn first_segment(&self, p: i128) -> u32 {
        let p16 = p << 16;
        if p16 < self.g1 {
            1
        } else if p16 < self.g_j {
            ((p16 - self.g1) / self.w16 + 2) as u32
        } else {
            self.j_lin - 1 + u32::from(bit_length(((p16 - self.g_j) / self.w16 + 2) as u128))
        }
    }
}

/// `_surcharge`: `min(maxFee - poolFee, ceil(slopeK * poolFee * twiceMid / (spacing << 18)))`.
fn surcharge(
    config: MevCaptureV21MainConfig,
    pool_fee: u64,
    twice_mid_x16: i128,
    spacing: u32,
) -> u64 {
    let den = U256::from(spacing) << 18usize;
    let num = U256::from(config.slope_k)
        * U256::from(pool_fee)
        * U256::from(u128::try_from(twice_mid_x16).expect("lo >= anchor"));
    let sur = (num + den - U256::ONE) / den;
    let cap = config.max_fee - pool_fee;
    if sur > U256::from(cap) { cap } else { sur.to() }
}

const MANTISSA_BITS: u32 = 94;

/// Raw contract `SqrtRatio` (`region << 94 | mantissa`) of a representable fixed-point ratio.
fn to_raw(fixed: U256) -> (u32, U256) {
    let region = if fixed >= U256::ONE << 160 {
        3
    } else if fixed >= U256::ONE << 128 {
        2
    } else if fixed >= U256::ONE << 96 {
        1
    } else {
        0
    };
    (region, fixed >> (2 + 32 * region) as usize)
}

fn from_raw(region: u32, mantissa: U256) -> U256 {
    mantissa << (2 + 32 * region) as usize
}

/// `predSqrtRatio`: the largest valid sqrt ratio strictly below `x`.
pub fn pred_sqrt_ratio(x: U256) -> U256 {
    let (region, mantissa) = to_raw(x);
    if region != 0 && mantissa == U256::ONE << 62 {
        from_raw(
            region - 1,
            (U256::ONE << MANTISSA_BITS as usize) - U256::ONE,
        )
    } else {
        from_raw(region, mantissa - U256::ONE)
    }
}

/// `succSqrtRatio`: the smallest valid sqrt ratio strictly above `x`.
pub fn succ_sqrt_ratio(x: U256) -> U256 {
    let (region, mantissa) = to_raw(x);
    if region != 3 && mantissa == (U256::ONE << MANTISSA_BITS as usize) - U256::ONE {
        from_raw(region + 1, U256::ONE << 62)
    } else {
        from_raw(region, mantissa + U256::ONE)
    }
}

/// Fixed-point (64.128) value of a raw contract `SqrtRatio`.
pub fn sqrt_ratio_from_raw(raw: U256) -> U256 {
    from_raw(
        (raw >> MANTISSA_BITS as usize).to(),
        raw & ((U256::ONE << MANTISSA_BITS as usize) - U256::ONE),
    )
}

/// Raw contract `SqrtRatio` of a representable fixed-point ratio.
pub fn sqrt_ratio_to_raw(fixed: U256) -> U256 {
    let (region, mantissa) = to_raw(fixed);
    (U256::from(region) << MANTISSA_BITS as usize) | mantissa
}

/// Whether a fixed-point sqrt ratio is a valid contract `SqrtRatio`.
#[must_use]
pub fn is_valid_sqrt_ratio(sqrt_ratio: U256) -> bool {
    sqrt_ratio >= Evm::min_sqrt_ratio()
        && sqrt_ratio <= Evm::max_sqrt_ratio()
        && Evm::adjust_sqrt_ratio_precision(sqrt_ratio) == sqrt_ratio
}

/// Core pool state. `tick` is Core's stored tick: one below the price's tick after a decreasing
/// swap stopped on a tick.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct MevCaptureV21MainCoreState {
    pub sqrt_ratio: U256,
    pub tick: i32,
    pub liquidity: u128,
}

/// Core pool state plus the extension's `getAnchor` fields.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct MevCaptureV21MainPoolState {
    pub core: MevCaptureV21MainCoreState,
    pub anchor: MevCaptureV21MainAnchor,
}

impl PoolState for MevCaptureV21MainPoolState {
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
pub struct MevCaptureV21MainPoolResources {
    /// `CORE.swap` calls made by the extension.
    pub core_calls: u32,
    /// Core swap loop iterations, summed over calls (one bitmap search each).
    pub core_steps: u32,
    /// Initialized ticks crossed (one bridge call each, except in toward and pass-through calls).
    pub initialized_ticks_crossed: u32,
    /// Bridge calls.
    pub bridges: u32,
    /// Tick-event searches by the extension (`next/prevInitializedTick`).
    pub tick_event_searches: u32,
    /// `CORE.accumulateAsFees` calls.
    pub accumulate_as_fees: u32,
    /// 1 when this swap runs the first-touch anchor update of its timestamp.
    pub anchor_updates: u32,
    /// 1 when the extension writes its pool state.
    pub state_writes: u32,
}

/// Role of a Core call made by the extension.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum MevCaptureV21MainCallKind {
    /// Zero amount or price already at the user limit: the user's parameters are forwarded.
    PassThrough,
    /// The uncut, uncharged call toward the anchor.
    Toward,
    /// A call in away segment `k` (1-based), charged `surcharge` (Q0.64) on the calculated token.
    Charged { k: u32, surcharge: u64 },
    /// One representable step onto an initialized tick, uncharged.
    Bridge,
}

/// One `CORE.swap` call, with the exact parameters the extension passes.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct MevCaptureV21MainCoreCall {
    pub kind: MevCaptureV21MainCallKind,
    pub sqrt_ratio_limit: U256,
    /// The remaining specified amount passed to Core.
    pub amount: i128,
    /// Core's balance update.
    pub delta0: i128,
    pub delta1: i128,
    /// Surcharge passed to `accumulateAsFees` right after the call (zero: not called).
    pub surcharge0: u128,
    pub surcharge1: u128,
    /// LP fees paid inside Core (pool fee).
    pub fees_paid: u128,
    pub state_before: MevCaptureV21MainCoreState,
    pub state_after: MevCaptureV21MainCoreState,
    pub steps: u32,
    pub initialized_ticks_crossed: u32,
}

/// User swap parameters forwarded to the extension.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct MevCaptureV21MainSwapParams {
    pub is_token1: bool,
    /// Positive for exact input, negative for exact output.
    pub amount: i128,
    /// Fixed-point limit; `None` is the contract default (minimum or maximum sqrt ratio).
    pub sqrt_ratio_limit: Option<U256>,
    pub skip_ahead: u32,
}

/// Full simulation of one forwarded swap.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MevCaptureV21MainSwap {
    /// `Some` on the first swap of a timestamp; `passed == false` emits `AnchorGateFailed`.
    pub gate: Option<MevCaptureV21MainGate>,
    /// The anchor the swap used.
    pub anchor_x16: i64,
    pub calls: Vec<MevCaptureV21MainCoreCall>,
    /// The forwarded balance update (Core deltas plus surcharges).
    pub delta0: i128,
    pub delta1: i128,
    /// Total surcharge, by token (the sum of the `FeesAccumulated` amounts).
    pub surcharge0: u128,
    pub surcharge1: u128,
    /// LP fees paid inside Core.
    pub fees_paid: u128,
    pub state_after: MevCaptureV21MainPoolState,
    pub resources: MevCaptureV21MainPoolResources,
}

/// Pool key on the current Core: Q0.64 fee and any concentrated tick spacing.
pub type MevCaptureV21MainPoolKey =
    PoolKey<<Evm as Chain>::Address, <Evm as Chain>::Fee, ConcentratedPoolTypeConfig>;
/// Pool configuration of a [`MevCaptureV21MainPool`].
pub type MevCaptureV21MainPoolConfig =
    PoolConfig<<Evm as Chain>::Address, <Evm as Chain>::Fee, ConcentratedPoolTypeConfig>;

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, Error)]
pub enum MevCaptureV21MainPoolConstructionError {
    #[error(transparent)]
    Common(#[from] CommonPoolConstructionError),
    #[error(transparent)]
    InvalidConfig(#[from] InvalidMainConfig),
    #[error("extension must be non-zero")]
    MissingExtension,
    #[error("pool fee must be non-zero and below maxFee")]
    InvalidPoolFee,
    #[error("tick spacing must be in [1, MAX_TICK_SPACING]")]
    InvalidTickSpacing,
    #[error("invalid sqrt ratio or tick")]
    InvalidPrice,
    #[error("ticks must be sorted, unique, in range and multiples of the tick spacing")]
    InvalidTicks,
    #[error("active liquidity does not match the ticks at or below the current tick")]
    ActiveLiquidityMismatch,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, Error)]
pub enum MevCaptureV21MainQuoteError {
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
    /// A checked sum, cast or `amountBeforeFee` overflowed (the contract reverts).
    #[error("amount overflow")]
    AmountOverflow,
    #[error("liquidity overflow")]
    LiquidityOverflow,
    /// A Core call moved neither the price nor the amount (the contract would run out of gas).
    #[error("no progress")]
    NoProgress,
}

/// Emulation of the current Core's concentrated-liquidity swap over a known set of initialized
/// ticks, including its bitmap words and `skipAhead`.
struct CoreSwap<'a> {
    ticks: &'a [Tick],
    spacing: i64,
    skip_ahead: u32,
}

struct CoreSwapResult {
    delta0: i128,
    delta1: i128,
    fees_paid: u128,
    state: MevCaptureV21MainCoreState,
    steps: u32,
    crossed: u32,
}

impl CoreSwap<'_> {
    /// `tickToBitmapWordAndIndex` as one raw index (rounds toward negative infinity).
    fn raw(&self, tick: i64) -> i64 {
        tick.div_euclid(self.spacing) + TICK_BITMAP_STORAGE_OFFSET
    }

    fn tick_of(&self, raw: i64) -> i64 {
        (raw - TICK_BITMAP_STORAGE_OFFSET) * self.spacing
    }

    /// `findNextInitializedTick`; returns the tick and the index of the initialized tick, if any.
    fn next(&self, from: i32) -> (i32, Option<usize>) {
        let mut next = i64::from(from);
        let mut skip = self.skip_ahead;
        loop {
            let raw = self.raw(next + self.spacing);
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
            if next >= i64::from(EVM_MAX_TICK) {
                return (EVM_MAX_TICK, None);
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
            if prev <= i64::from(EVM_MIN_TICK) {
                return (EVM_MIN_TICK, None);
            }
            if skip == 0 {
                return (prev as i32, None);
            }
            skip -= 1;
            prev -= 1;
        }
    }

    fn search(&self, from: i32, increasing: bool) -> (i32, Option<usize>) {
        if increasing {
            self.next(from)
        } else {
            self.prev(from)
        }
    }

    /// `Core.swap` for a concentrated pool.
    fn swap(
        &self,
        state: MevCaptureV21MainCoreState,
        fee: u64,
        is_token1: bool,
        amount: i128,
        limit: U256,
    ) -> Result<CoreSwapResult, MevCaptureV21MainQuoteError> {
        if !is_valid_sqrt_ratio(limit) {
            return Err(MevCaptureV21MainQuoteError::InvalidSqrtRatioLimit);
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
        let exact_out = amount < 0;
        let increasing = is_token1 != exact_out;
        if (limit < state.sqrt_ratio) == increasing {
            return Err(MevCaptureV21MainQuoteError::SqrtRatioLimitWrongDirection);
        }

        let MevCaptureV21MainCoreState {
            mut sqrt_ratio,
            mut tick,
            mut liquidity,
        } = state;
        let mut remaining = amount;
        let mut calculated: u128 = 0;
        loop {
            let (next_tick, initialized) = self.search(tick, increasing);
            let next_ratio = to_sqrt_ratio::<Evm>(next_tick)
                .ok_or(MevCaptureV21MainQuoteError::InvalidTick(next_tick))?;
            let limited = if increasing {
                next_ratio.min(limit)
            } else {
                next_ratio.max(limit)
            };
            let step =
                compute_step::<Evm>(sqrt_ratio, liquidity, limited, remaining, is_token1, fee)?;
            remaining = remaining
                .checked_sub(step.consumed_amount)
                .ok_or(MevCaptureV21MainQuoteError::AmountOverflow)?;
            calculated = calculated
                .checked_add(step.calculated_amount)
                .ok_or(MevCaptureV21MainQuoteError::AmountOverflow)?;
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
                        .ok_or(MevCaptureV21MainQuoteError::LiquidityOverflow)?;
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
            .ok_or(MevCaptureV21MainQuoteError::AmountOverflow)?;
        let calculated = if exact_out {
            i128::try_from(calculated).map_err(|_| MevCaptureV21MainQuoteError::AmountOverflow)?
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
        result.state = MevCaptureV21MainCoreState {
            sqrt_ratio,
            tick,
            liquidity,
        };
        Ok(result)
    }
}

/// A concentrated pool on the current Core behind MEVCapture v2.1 (`main` variant).
///
/// Quotes are exact for the given initialized ticks: Core's bitmap words and `skipAhead`
/// are emulated because the extension cuts calls at Core's tick events. Every initialized tick
/// the swap can reach must be supplied.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MevCaptureV21MainPool {
    key: MevCaptureV21MainPoolKey,
    model: MevCaptureV21MainModel,
    state: MevCaptureV21MainPoolState,
    sorted_ticks: Vec<Tick>,
}

impl MevCaptureV21MainPool {
    /// `config` must be the extension's `getConfig` tuple and `state.anchor` its `getAnchor`.
    /// `sorted_ticks` are the initialized ticks with their net liquidity deltas; a referenced
    /// tick whose net delta is zero is still initialized and must be included.
    pub fn new(
        key: MevCaptureV21MainPoolKey,
        config: MevCaptureV21MainConfig,
        state: MevCaptureV21MainPoolState,
        sorted_ticks: Vec<Tick>,
    ) -> Result<Self, MevCaptureV21MainPoolConstructionError> {
        ensure_valid_token_order(&key)?;
        let model = MevCaptureV21MainModel::new(config)?;
        let PoolConfig {
            extension,
            fee,
            pool_type_config: TickSpacing(spacing),
        } = key.config;
        if extension.is_zero() {
            return Err(MevCaptureV21MainPoolConstructionError::MissingExtension);
        }
        if fee == 0 || fee >= config.max_fee {
            return Err(MevCaptureV21MainPoolConstructionError::InvalidPoolFee);
        }
        if spacing == 0 || spacing > MEV_CAPTURE_V21_MAIN_MAX_TICK_SPACING {
            return Err(MevCaptureV21MainPoolConstructionError::InvalidTickSpacing);
        }
        let core = state.core;
        let tick_ratio = to_sqrt_ratio::<Evm>(core.tick);
        let next_ratio = core.tick.checked_add(1).and_then(to_sqrt_ratio::<Evm>);
        if !is_valid_sqrt_ratio(core.sqrt_ratio)
            || tick_ratio.is_none_or(|r| r > core.sqrt_ratio)
            || next_ratio.is_some_and(|r| r < core.sqrt_ratio)
        {
            return Err(MevCaptureV21MainPoolConstructionError::InvalidPrice);
        }
        let mut active: u128 = 0;
        for (i, t) in sorted_ticks.iter().enumerate() {
            if t.index % spacing as i32 != 0
                || t.index < EVM_MIN_TICK
                || t.index > EVM_MAX_TICK
                || i > 0 && sorted_ticks[i - 1].index >= t.index
            {
                return Err(MevCaptureV21MainPoolConstructionError::InvalidTicks);
            }
            if t.index <= core.tick {
                active = active
                    .checked_add_signed(t.liquidity_delta)
                    .ok_or(MevCaptureV21MainPoolConstructionError::ActiveLiquidityMismatch)?;
            }
        }
        if active != core.liquidity {
            return Err(MevCaptureV21MainPoolConstructionError::ActiveLiquidityMismatch);
        }
        Ok(Self {
            key,
            model,
            state,
            sorted_ticks,
        })
    }

    pub fn model(&self) -> &MevCaptureV21MainModel {
        &self.model
    }

    pub fn ticks(&self) -> &[Tick] {
        &self.sorted_ticks
    }

    /// Simulates `forward` exactly: the first-touch anchor update, the toward call, the away
    /// state machine (rate cuts, tick cuts, bridges, surcharges) and the post-swap refresh.
    pub fn simulate_swap(
        &self,
        state: MevCaptureV21MainPoolState,
        params: MevCaptureV21MainSwapParams,
        now: u32,
    ) -> Result<MevCaptureV21MainSwap, MevCaptureV21MainQuoteError> {
        let mut anchor = state.anchor;
        let gate = self
            .model
            .before_swap(&mut anchor, state.core.tick, state.core.liquidity, now);
        let mut swap = self.swap_through_segments(state.core, params, anchor.anchor_x16)?;
        self.model
            .after_swap(&mut anchor, swap.state_after.core.liquidity, now);
        swap.gate = gate;
        swap.resources.anchor_updates = u32::from(gate.is_some());
        swap.resources.state_writes = u32::from(anchor != state.anchor);
        swap.state_after.anchor = anchor;
        Ok(swap)
    }

    /// `_swapThroughSegments` with a given anchor (no anchor update or refresh); the returned
    /// `state_after.anchor` is the pool's stored anchor state.
    pub fn swap_through_segments(
        &self,
        core_state: MevCaptureV21MainCoreState,
        params: MevCaptureV21MainSwapParams,
        anchor_x16: i64,
    ) -> Result<MevCaptureV21MainSwap, MevCaptureV21MainQuoteError> {
        let increasing = params.is_token1 != (params.amount < 0);
        let exact_out = params.amount < 0;
        let user_limit = params.sqrt_ratio_limit.unwrap_or(if increasing {
            Evm::max_sqrt_ratio()
        } else {
            Evm::min_sqrt_ratio()
        });
        if !is_valid_sqrt_ratio(user_limit) {
            return Err(MevCaptureV21MainQuoteError::InvalidSqrtRatioLimit);
        }
        let config = self.model.config();
        let pool_fee = self.key.config.fee;
        let TickSpacing(spacing) = self.key.config.pool_type_config;
        let core = CoreSwap {
            ticks: &self.sorted_ticks,
            spacing: i64::from(spacing),
            skip_ahead: params.skip_ahead,
        };
        let nearer = |x: U256, y: U256| if increasing { x.min(y) } else { x.max(y) };

        let mut calls: Vec<MevCaptureV21MainCoreCall> = Vec::new();
        let mut current = core_state;
        let mut remaining = params.amount;
        let mut resources = MevCaptureV21MainPoolResources::default();

        let mut call = |kind: MevCaptureV21MainCallKind,
                        limit: U256,
                        remaining: &mut i128,
                        current: &mut MevCaptureV21MainCoreState|
         -> Result<(), MevCaptureV21MainQuoteError> {
            let r = core.swap(*current, pool_fee, params.is_token1, *remaining, limit)?;
            let (mut surcharge0, mut surcharge1) = (0, 0);
            if let MevCaptureV21MainCallKind::Charged { surcharge, .. } = kind
                && surcharge != 0
            {
                let calculated = if params.is_token1 { r.delta0 } else { r.delta1 };
                let fee = if exact_out {
                    let input = calculated as u128;
                    let input_net = input - compute_fee::<Evm>(input, pool_fee);
                    amount_before_fee::<Evm>(input_net, surcharge)
                        .ok_or(MevCaptureV21MainQuoteError::AmountOverflow)?
                        - input_net
                } else {
                    compute_fee::<Evm>(calculated.unsigned_abs(), surcharge)
                };
                if params.is_token1 {
                    surcharge0 = fee;
                } else {
                    surcharge1 = fee;
                }
            }
            let specified = if params.is_token1 { r.delta1 } else { r.delta0 };
            let progressed = r.state != *current || specified != 0;
            calls.push(MevCaptureV21MainCoreCall {
                kind,
                sqrt_ratio_limit: limit,
                amount: *remaining,
                delta0: r.delta0,
                delta1: r.delta1,
                surcharge0,
                surcharge1,
                fees_paid: r.fees_paid,
                state_before: *current,
                state_after: r.state,
                steps: r.steps,
                initialized_ticks_crossed: r.crossed,
            });
            *remaining = remaining
                .checked_sub(specified)
                .ok_or(MevCaptureV21MainQuoteError::AmountOverflow)?;
            *current = r.state;
            if !progressed && *remaining != 0 && current.sqrt_ratio != user_limit {
                return Err(MevCaptureV21MainQuoteError::NoProgress);
            }
            Ok(())
        };

        if remaining == 0 || current.sqrt_ratio == user_limit {
            call(
                MevCaptureV21MainCallKind::PassThrough,
                user_limit,
                &mut remaining,
                &mut current,
            )?;
        } else {
            let a = if increasing {
                i128::from(anchor_x16)
            } else {
                -i128::from(anchor_x16)
            };
            let mut done = false;
            {
                let anchor_tick = (if increasing { a >> 16 } else { -(a >> 16) })
                    .clamp(i128::from(EVM_MIN_TICK), i128::from(EVM_MAX_TICK))
                    as i32;
                let anchor_ratio = to_sqrt_ratio::<Evm>(anchor_tick)
                    .ok_or(MevCaptureV21MainQuoteError::InvalidTick(anchor_tick))?;
                if (current.sqrt_ratio < anchor_ratio && increasing)
                    || (current.sqrt_ratio > anchor_ratio && !increasing)
                {
                    let limit = nearer(anchor_ratio, user_limit);
                    call(
                        MevCaptureV21MainCallKind::Toward,
                        limit,
                        &mut remaining,
                        &mut current,
                    )?;
                    done = remaining == 0 || limit == user_limit || current.sqrt_ratio != limit;
                }
            }

            if !done {
                let grid = Grid::new(a, spacing, config);
                let p = if increasing {
                    i128::from(current.tick)
                } else {
                    -i128::from(current.tick) - 1
                };
                let mut k = grid.first_segment(p);
                let mut lo = if k == 1 { a } else { grid.boundary(k - 1) };
                let cap = config.max_fee - pool_fee;
                loop {
                    let hi = grid.boundary(k);
                    let sur = surcharge(config, pool_fee, lo + hi - 2 * a, spacing);
                    let mut limit = user_limit;
                    if sur != cap {
                        let hi_tick = hi >> 16;
                        if hi_tick <= i128::from(EVM_MAX_TICK) {
                            let t = if increasing { hi_tick } else { -hi_tick } as i32;
                            let boundary = to_sqrt_ratio::<Evm>(t)
                                .ok_or(MevCaptureV21MainQuoteError::InvalidTick(t))?;
                            if (increasing && boundary <= current.sqrt_ratio)
                                || (!increasing && boundary >= current.sqrt_ratio)
                            {
                                lo = hi;
                                k += 1;
                                continue;
                            }
                            limit = nearer(boundary, limit);
                        }
                    }

                    let (mut event_tick, mut initialized) = core.search(current.tick, increasing);
                    resources.tick_event_searches += 1;
                    let mut event_ratio = to_sqrt_ratio::<Evm>(event_tick)
                        .ok_or(MevCaptureV21MainQuoteError::InvalidTick(event_tick))?;
                    if event_ratio == current.sqrt_ratio {
                        (event_tick, initialized) = core.search(
                            if increasing {
                                event_tick
                            } else {
                                event_tick - 1
                            },
                            increasing,
                        );
                        resources.tick_event_searches += 1;
                        event_ratio = to_sqrt_ratio::<Evm>(event_tick)
                            .ok_or(MevCaptureV21MainQuoteError::InvalidTick(event_tick))?;
                    }

                    let kind = if initialized.is_some() {
                        let cut = if increasing {
                            pred_sqrt_ratio(event_ratio)
                        } else {
                            succ_sqrt_ratio(event_ratio)
                        };
                        if cut == current.sqrt_ratio {
                            limit = nearer(event_ratio, user_limit);
                            MevCaptureV21MainCallKind::Bridge
                        } else {
                            limit = nearer(cut, limit);
                            MevCaptureV21MainCallKind::Charged { k, surcharge: sur }
                        }
                    } else {
                        limit = nearer(event_ratio, limit);
                        MevCaptureV21MainCallKind::Charged { k, surcharge: sur }
                    };

                    call(kind, limit, &mut remaining, &mut current)?;
                    if remaining == 0 || current.sqrt_ratio == user_limit {
                        break;
                    }
                }
            }
        }

        let mut sum0: i128 = 0;
        let mut sum1: i128 = 0;
        let (mut surcharge0, mut surcharge1, mut fees_paid) = (0u128, 0u128, 0u128);
        for c in &calls {
            let s0 = i128::try_from(c.surcharge0)
                .map_err(|_| MevCaptureV21MainQuoteError::AmountOverflow)?;
            let s1 = i128::try_from(c.surcharge1)
                .map_err(|_| MevCaptureV21MainQuoteError::AmountOverflow)?;
            sum0 = sum0
                .checked_add(c.delta0)
                .and_then(|s| s.checked_add(s0))
                .ok_or(MevCaptureV21MainQuoteError::AmountOverflow)?;
            sum1 = sum1
                .checked_add(c.delta1)
                .and_then(|s| s.checked_add(s1))
                .ok_or(MevCaptureV21MainQuoteError::AmountOverflow)?;
            surcharge0 += c.surcharge0;
            surcharge1 += c.surcharge1;
            fees_paid = fees_paid.saturating_add(c.fees_paid);
            resources.core_steps += c.steps;
            resources.initialized_ticks_crossed += c.initialized_ticks_crossed;
            resources.bridges += u32::from(c.kind == MevCaptureV21MainCallKind::Bridge);
            resources.accumulate_as_fees += u32::from(c.surcharge0 != 0 || c.surcharge1 != 0);
        }
        resources.core_calls = calls.len() as u32;

        Ok(MevCaptureV21MainSwap {
            gate: None,
            anchor_x16,
            calls,
            delta0: sum0,
            delta1: sum1,
            surcharge0,
            surcharge1,
            fees_paid,
            state_after: MevCaptureV21MainPoolState {
                core: current,
                anchor: self.state.anchor,
            },
            resources,
        })
    }
}

impl AsRef<Self> for MevCaptureV21MainPool {
    fn as_ref(&self) -> &Self {
        self
    }
}

impl Pool for MevCaptureV21MainPool {
    type Address = <Evm as Chain>::Address;
    type Fee = <Evm as Chain>::Fee;
    type Resources = MevCaptureV21MainPoolResources;
    type State = MevCaptureV21MainPoolState;
    type QuoteError = MevCaptureV21MainQuoteError;
    type Meta = BlockTimestamp;
    type PoolTypeConfig = ConcentratedPoolTypeConfig;

    fn key(&self) -> MevCaptureV21MainPoolKey {
        self.key
    }

    fn state(&self) -> Self::State {
        self.state
    }

    /// Quotes with `skipAhead = 0`; use [`MevCaptureV21MainPool::simulate_swap`] for other
    /// parameters and per-call records. `fees_paid` is the pool fee only; the surcharge is part
    /// of the calculated amount.
    fn quote(
        &self,
        params: QuoteParams<Self::Address, Self::State, Self::Meta>,
    ) -> Result<Quote<Self::Resources, Self::State>, Self::QuoteError> {
        let is_token1 = is_token1(&self.key, params.token_amount.token)?;
        let amount = params.token_amount.amount;
        let swap = self.simulate_swap(
            params.override_state.unwrap_or(self.state),
            MevCaptureV21MainSwapParams {
                is_token1,
                amount,
                sqrt_ratio_limit: params.sqrt_ratio_limit,
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

impl private::Sealed for MevCaptureV21MainPool {}
impl private::Sealed for MevCaptureV21MainPoolState {}
