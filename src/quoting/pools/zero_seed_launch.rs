//! Quoting and installation math for pools of the `ZeroSeedLaunch` extension.
//!
//! A zero-seed launch mints a fixed supply and installs all of it, in one transaction, as a single
//! token-only concentrated position from the ask price up to an upper bound, with no quote seed.
//! The pool fee is 0. The pool, the position and its liquidity never change after creation: only
//! swaps forwarded through the extension move the price, and every swap's price limit is clamped
//! to the position bounds. Time only lowers the creator fee, from `initial_fee` at
//! `trading_start` along an exponential with per-second factor `decay_factor`, rescaled to reach
//! `final_fee` exactly after `fee_duration`. The creator fee is charged on the calculated side of
//! the actual fill and saved separately from the position.
//!
//! The model mirrors `ZeroSeedLaunch.handleForwardData` and the `Core` swap loop step by step,
//! including the tick bitmap word boundaries a swap with `skipAhead` 0 stops at, so it reproduces
//! the contract's deltas, creator fee and post-swap `Core` state exactly. The installation
//! functions mirror `previewInstallation` and the binding check of `create`.
//!
//! Target: `EkuboProtocol/evm-contracts@b1cbb1c1a9a00de62072a63a8f4aab4d97065573` (draft
//! exponential creator-fee decay), against the Q0.64-fee `Core` of that commit's base. Not the
//! Q0.16 `next` Core.

use core::str::FromStr;
use derive_more::{Add, AddAssign, Sub, SubAssign};
use num_traits::Zero;
use ruint::aliases::U256;
use thiserror::Error;

use crate::{
    chain::{
        Chain,
        evm::{EVM_MAX_TICK_SPACING, Evm},
    },
    math::{
        delta::{AmountDeltaError, amount0_delta, amount1_delta},
        muldiv::muldiv,
        sqrt_ratio::{next_sqrt_ratio_from_amount0, next_sqrt_ratio_from_amount1},
        swap::{amount_before_fee, compute_fee, is_price_increasing},
        tick::{sqrt_ratio_to_tick, to_sqrt_ratio},
    },
    private,
    quoting::{
        pools::{
            CommonPoolConstructionError, CommonPoolQuoteError,
            concentrated::{ConcentratedPoolResources, ConcentratedPoolTypeConfig, TickSpacing},
            ensure_valid_token_order, is_token1,
        },
        types::{BlockTimestamp, Pool, PoolConfig, PoolKey, PoolState, Quote, QuoteParams},
    },
};

type Address = <Evm as Chain>::Address;

/// Offline observation from the LOCAL harness, never a live provider attestation.
/// Callers must bind these values to the same executed instance/block as the pool state.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ZeroSeedLaunchInstance {
    pub chain_id: u64,
    pub extension: Address,
    pub core: Address,
    pub constructor_quote: Address,
    pub quote_token_getter: Address,
    pub extension_runtime: U256,
    pub core_runtime: U256,
    pub quote_runtime: U256,
}

impl ZeroSeedLaunchInstance {
    /// Fail closed against the two constructor-executed WETH LOCAL manifest entries.
    /// There are NO approved live entries. Synthetic six-decimal arithmetic is not supported.
    pub fn validate(&self) -> Result<(), ZeroSeedLaunchParameterError> {
        let addr = |s| Address::from_str(s).expect("static manifest address");
        let hash = |s| U256::from_str(s).expect("static manifest hash");
        let high = addr("0xffffffffffffffffffffffffffffffffffffffff");
        let low = addr("0x0000000000000000000000000000000000010000");
        let (extension, runtime) = if self.constructor_quote == high {
            (
                addr("0x5142e167b32877ca3cf3060010a0a1418e3ef1b9"),
                hash("0x8fb360bb48006819049e6b9a53679ccaa01264e61465ce8e8cd2e8b185d3a8d1"),
            )
        } else if self.constructor_quote == low {
            (
                addr("0x51174b5db84c81a906ec55445070fd84c8c8e655"),
                hash("0xa951db07ad354ea45df3ff1b720b69c7cc588c4feb44aaea79cd79639da61f6e"),
            )
        } else {
            return Err(ZeroSeedLaunchParameterError::UnsupportedInstance);
        };
        if self.chain_id != 31337
            || self.extension != extension
            || self.core != addr("0x00000000000014aa86c5d3c41765bb24e11bd701")
            || self.quote_token_getter != self.constructor_quote
            || self.extension_runtime != runtime
            || self.core_runtime
                != hash("0xc5f90c9d0dbc5037f8f9e248f4bb292e7c1824f584eb6550cb4cad525b38c71a")
            || self.quote_runtime
                != hash("0x8a3a1f6a9f9dce633117adee5b458245835a8645a8c8726a26382a4622508b1c")
        {
            return Err(ZeroSeedLaunchParameterError::UnsupportedInstance);
        }
        Ok(())
    }
}

/// Finite LOCAL producer/decoder context, separate from pure `fee_at` and pool math.
/// Integer types express the unsigned domains; every addition is checked.
#[derive(Clone, Copy, Debug)]
pub struct ZeroSeedLaunchLocalPreview<'a> {
    pub instance: &'a ZeroSeedLaunchInstance,
    pub name: &'a str,
    pub symbol: &'a str,
    /// Observed code presence at the predicted token address (same local snapshot).
    pub predicted_token_has_code: bool,
    pub build_time: u64,
    pub execution_expiry: u64,
}

impl ZeroSeedLaunchLocalPreview<'_> {
    /// Re-run at build, use and owner review with fresh `now`; never rewrite signed start.
    pub fn validate(
        &self,
        parameters: &ZeroSeedLaunchParameters,
        now: u64,
    ) -> Result<(), ZeroSeedLaunchParameterError> {
        type E = ZeroSeedLaunchParameterError;
        self.instance.validate()?;
        if parameters.quote_token != self.instance.constructor_quote {
            return Err(E::UnsupportedQuoteToken);
        }
        if self.name.len() > 31 || self.symbol.len() > 31 {
            return Err(E::MetadataTooLong);
        }
        if self.predicted_token_has_code {
            return Err(E::LaunchTokenExists);
        }
        let min_start = self.build_time.checked_add(300).ok_or(E::Overflow)?;
        let max_start = self.build_time.checked_add(86400).ok_or(E::Overflow)?;
        let fresh_min = now.checked_add(300).ok_or(E::Overflow)?;
        let start = parameters.fee.trading_start;
        if now < self.build_time
            || now >= self.execution_expiry
            || start < min_start
            || start > max_start
            || start < fresh_min
            || self.execution_expiry <= self.build_time
            || self.execution_expiry > start
        {
            return Err(E::InvalidLocalTiming);
        }
        Ok(())
    }
}

/// Single-preview arithmetic pair. Keep requested supply separately; bind THIS actual pair at
/// creation, without another preview. Not calldata, an execution guarantee or live authorization.
pub fn preview_installation(
    parameters: &ZeroSeedLaunchParameters,
    now: u64,
    context: &ZeroSeedLaunchLocalPreview<'_>,
) -> Result<ZeroSeedLaunchInstallation, ZeroSeedLaunchParameterError> {
    context.validate(parameters, now)?;
    preview_installation_math(parameters, now)
}

/// Exact binding of the single preview's installed supply/liquidity. Rechecks fresh local context.
pub fn check_launch_binding(
    parameters: &ZeroSeedLaunchParameters,
    liquidity: u128,
    now: u64,
    context: &ZeroSeedLaunchLocalPreview<'_>,
) -> Result<ZeroSeedLaunchInstallation, ZeroSeedLaunchParameterError> {
    context.validate(parameters, now)?;
    check_launch_binding_math(parameters, liquidity, now)
}

/// Mirrors all five contract sink refusals. Atomic full two-asset claim, not a per-side claim.
pub fn validate_claim_recipient(
    instance: &ZeroSeedLaunchInstance,
    key: &ZeroSeedLaunchPoolKey,
    recipient: Address,
) -> Result<(), ZeroSeedLaunchParameterError> {
    instance.validate()?;
    if key.config.extension != instance.extension
        || (key.token0 != instance.constructor_quote && key.token1 != instance.constructor_quote)
    {
        return Err(ZeroSeedLaunchParameterError::UnsupportedInstance);
    }
    if recipient.is_zero()
        || recipient == instance.core
        || recipient == instance.extension
        || recipient == key.token0
        || recipient == key.token1
    {
        return Err(ZeroSeedLaunchParameterError::InvalidRecipient);
    }
    Ok(())
}

/// Highest creator fee rate the contract accepts, Q0.64: `floor(2**64 * 99 / 100)`, 99%.
/// A draft cap, not a live parameter. Exactly 100% is not encodable.
pub const ZERO_SEED_LAUNCH_MAX_CREATOR_FEE: u64 = 18_262_276_632_972_456_099;

/// `skipAhead` of the forwarded swaps this model quotes. The deployed Yul router's forwarded hop
/// uses 0.
const SKIP_AHEAD: u32 = 0;

/// Offset `Core` adds to compressed ticks to index its tick bitmaps.
const TICK_BITMAP_STORAGE_OFFSET: i64 = 89_421_695;

const TWO_POW_128: U256 = U256::from_limbs([0, 0, 1, 0]);

// Gas estimates fitted to the in-test gas of the forwarded swap frame (test locker
// `forwardSwap`, token settlement included) of the parity vectors generated at
// `EkuboProtocol/evm-contracts@d6aeb58d845aa29454f3ed8df15e84a306a6f26d`: worst error
// 40% on non-cold fills. Unchanged for the exponential schedule of `b1cbb1c1`: the contract
// measures +2,947 to +3,150 gas per swap strictly inside the fee window (two `powQ64`
// evaluations and a division) and within +132 at the endpoints; against the regenerated
// parity vectors the estimate's error on interior fills is -27% to +18% (mean -3%), and the
// worst non-cold error, 39.3%, is on an endpoint fill. They exclude the 21,000 transaction base, calldata, the router and any account
// abstraction overhead. A swap that writes a zero storage slot, such as the first creator fee after
// a claim or the first launch tokens a holder receives, costs about 20,000 more per slot, which
// the pool state cannot predict; the first swap of a launch costs about 60,000-70,000 more.
// Calibrate against execution before relying on them.

/// A forwarded launch swap that stays within one tick bitmap word.
pub const ZERO_SEED_LAUNCH_SWAP_GAS_UNCALIBRATED: u64 = 33_500;
/// Extra gas per additional swap step at a tick bitmap word boundary or launch bound. With
/// `skipAhead` 0 a swap across the whole 100x reference range takes about 180 steps.
pub const ZERO_SEED_LAUNCH_EXTRA_BITMAP_LOOKUP_GAS_UNCALIBRATED: u64 = 4_300;

/// Unique identifier for a [`ZeroSeedLaunchPool`]. The pool fee is 0 and the extension is the
/// `ZeroSeedLaunch` contract.
pub type ZeroSeedLaunchPoolKey =
    PoolKey<Address, <Evm as Chain>::Fee, ZeroSeedLaunchPoolTypeConfig>;
/// Pool configuration for a [`ZeroSeedLaunchPool`].
pub type ZeroSeedLaunchPoolConfig =
    PoolConfig<Address, <Evm as Chain>::Fee, ZeroSeedLaunchPoolTypeConfig>;
/// Type config for a [`ZeroSeedLaunchPool`], the tick spacing of the launch pool.
pub type ZeroSeedLaunchPoolTypeConfig = ConcentratedPoolTypeConfig;

/// Range of a launch in economic ticks, as in `LaunchParameters`.
///
/// Ticks are log base 1.000001 of raw quote units per raw launch-token unit, so neither decimals
/// nor token order change their meaning. For a token0 launch the position is
/// `[ask_tick, upper_tick]` and the pool starts at `ask_tick`; for a token1 launch it is
/// `[-upper_tick, -ask_tick]` and the pool starts at `-ask_tick`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ZeroSeedLaunchRange {
    /// Whether the launch token is token1 of the pool, i.e. the quote token address is lower.
    pub launch_token_is_token1: bool,
    /// Economic lower bound and starting price.
    pub ask_tick: i32,
    /// Economic upper bound; buys stop there.
    pub upper_tick: i32,
    /// Tick spacing of the pool.
    pub tick_spacing: u32,
}

impl ZeroSeedLaunchRange {
    /// Bounds of the launch position in pool ticks.
    #[must_use]
    pub fn pool_bounds(&self) -> (i32, i32) {
        if self.launch_token_is_token1 {
            (-self.upper_tick, -self.ask_tick)
        } else {
            (self.ask_tick, self.upper_tick)
        }
    }

    /// Pool tick at creation: the token-only side of the position.
    #[must_use]
    pub fn initial_tick(&self) -> i32 {
        let (lower, upper) = self.pool_bounds();
        if self.launch_token_is_token1 {
            upper
        } else {
            lower
        }
    }
}

/// 2**64: the Q0.64 unit, exactly 100%. Not encodable as a `u64` fee or decay factor.
pub const ZERO_SEED_LAUNCH_Q64: u128 = 1 << 64;

/// `powQ64` from `math/feeDecay.sol`: `factor ** exponent` in Q0.64 by square-and-multiply,
/// flooring after every multiply.
///
/// The operation order is normative: for each set exponent bit multiply the running result by the
/// current factor and floor, shift, then square and floor the factor only if bits remain. Both
/// operands of every product are at most 2**64 and a `u64` factor is below 2**64, so every product
/// is below 2**128 and the result is at most 2**64. `pow_q64(b, 0)` is 2**64.
#[must_use]
pub fn pow_q64(factor: u64, mut exponent: u64) -> u128 {
    let mut result = ZERO_SEED_LAUNCH_Q64;
    let mut base = u128::from(factor);
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
}

/// Creator fee schedule, as in `LaunchParameters`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ZeroSeedLaunchFeeSchedule {
    /// First timestamp at which swaps are accepted; the decay starts here.
    pub trading_start: u64,
    /// Seconds from `trading_start` to `final_fee`. Not zero.
    pub fee_duration: u32,
    /// Creator fee until `trading_start`, Q0.64.
    pub initial_fee: u64,
    /// Creator fee from `trading_start + fee_duration` on, Q0.64.
    pub final_fee: u64,
    /// Per-second Q0.64 multiplier of the unscaled exponential, in `(0, 2**64)`. A literal
    /// encoded factor, not a half-life. `LaunchParameters.decayFactor`.
    pub decay_factor: u64,
}

impl ZeroSeedLaunchFeeSchedule {
    /// `feeAt`: the creator fee at `timestamp`, Q0.64.
    ///
    /// `initial_fee` until `trading_start`, then
    /// `final_fee + floor((initial_fee - final_fee) * (b**t - b**D) / (2**64 - b**D))` with
    /// `b**n = pow_q64(decay_factor, n)`, `t` the elapsed seconds and `D` the duration, then
    /// `final_fee` from `elapsed >= fee_duration` on. Elapsed time saturates at the duration
    /// before any narrowing, as in the contract.
    #[must_use]
    pub fn fee_at(&self, timestamp: u64) -> u64 {
        if timestamp <= self.trading_start {
            return self.initial_fee;
        }
        decayed_fee(
            self.initial_fee,
            self.final_fee,
            self.decay_factor,
            self.fee_duration,
            timestamp - self.trading_start,
        )
    }
}

/// `decayedFee` from `math/feeDecay.sol`, for `final_fee <= initial_fee`.
///
/// Below the duration `pow_q64` is non-increasing in the exponent, so `b**t >= b**D`; and
/// `b**D <= b < 2**64`, so the divisor is at least 1. `(initial - final) < 2**64` and
/// `b**t - b**D <= 2**64`, so the numerator fits a `u128` and the quotient is at most
/// `initial - final`.
#[must_use]
pub fn decayed_fee(
    initial_fee: u64,
    final_fee: u64,
    decay_factor: u64,
    duration: u32,
    elapsed: u64,
) -> u64 {
    if elapsed == 0 {
        return initial_fee;
    }
    if elapsed >= u64::from(duration) {
        return final_fee;
    }
    let endpoint = pow_q64(decay_factor, u64::from(duration));
    let excess = u128::from(initial_fee - final_fee) * (pow_q64(decay_factor, elapsed) - endpoint)
        / (ZERO_SEED_LAUNCH_Q64 - endpoint);
    final_fee + excess as u64
}

/// The launch inputs `previewInstallation` and `create` validate.
///
/// The token name, symbol, decimals and salt only determine the token address, so they are not
/// part of this model: take the token address, and with it `range.launch_token_is_token1`, from
/// `previewInstallation`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ZeroSeedLaunchParameters {
    /// Quote token. Supported entrypoints require the exact constructor-pinned instance quote.
    pub quote_token: Address,
    /// Requested supply for a preview, or the bound installed supply for `create`.
    pub supply: u128,
    pub range: ZeroSeedLaunchRange,
    pub fee: ZeroSeedLaunchFeeSchedule,
}

/// The plan `previewInstallation` returns, without the token address and pool key.
///
/// Pass `liquidity` and `installed_supply` together to `create` as `liquidity` and `supply`. Do
/// not preview `installed_supply` again: `maxLiquidity` rounds down twice, so that usually returns
/// `liquidity - 1` and the pair never converges.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ZeroSeedLaunchInstallation {
    /// Launch position lower bound, pool tick.
    pub tick_lower: i32,
    /// Launch position upper bound, pool tick.
    pub tick_upper: i32,
    /// Pool tick at creation.
    pub initial_tick: i32,
    /// Liquidity of the launch position.
    pub liquidity: u128,
    /// Exact launch-token amount `Core` takes for `liquidity`, rounded up. Never above the
    /// requested supply of a preview.
    pub installed_supply: u128,
}

/// Why `previewInstallation` or `create` refuses a launch, by contract error.
#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, Error)]
pub enum ZeroSeedLaunchParameterError {
    #[error("missing or mismatched local instance provenance")]
    UnsupportedInstance,
    #[error("metadata exceeds 31 UTF-8 bytes")]
    MetadataTooLong,
    #[error("predicted launch token address has code")]
    LaunchTokenExists,
    #[error("invalid claim recipient")]
    InvalidRecipient,
    #[error("invalid or stale LOCAL start/expiry context")]
    InvalidLocalTiming,
    /// `UnsupportedQuoteToken`, or a quote that mismatches the supported constructor instance.
    #[error("quote token is not supported")]
    UnsupportedQuoteToken,
    /// `InvalidParameters`: supply, tick spacing or range out of bounds.
    #[error("invalid launch parameters")]
    InvalidParameters,
    /// `FeeTooHigh`: initial fee above the 99% cap.
    #[error("creator fee above the cap")]
    FeeTooHigh,
    /// `InvalidFeeSchedule`: final fee above the initial fee, zero duration or zero decay factor.
    #[error("invalid fee schedule")]
    InvalidFeeSchedule,
    /// `InvalidTradingStart`: trading start before the creation block.
    #[error("trading start is in the past")]
    InvalidTradingStart,
    /// Core `BoundsTickSpacing`: a bound is not a multiple of the tick spacing.
    #[error("range bounds are not aligned to the tick spacing")]
    BoundsTickSpacing,
    /// `ZeroLiquidity`.
    #[error("supply buys zero liquidity")]
    ZeroLiquidity,
    /// `LiquidityAboveTickCap(liquidity, cap)`.
    #[error("liquidity {liquidity} above the per-tick cap {cap}")]
    LiquidityAboveTickCap { liquidity: u128, cap: u128 },
    /// `SupplyNotExactlyInstallable(requested, installable)`: `create` only.
    #[error("supply {requested} is not the amount {installable} the liquidity takes")]
    SupplyNotExactlyInstallable { requested: u128, installable: u128 },
    /// The token amount for the liquidity does not fit Core's signed delta.
    #[error("installation amount overflow")]
    Overflow,
}

/// `_validate` of `previewInstallation` and `create`, plus Core's bound alignment check.
///
/// Pure arithmetic validation, NOT supported-instance or producer timing approval.
/// `now` is the timestamp of the block the contract call executes in.
pub fn validate_launch_parameters_math(
    parameters: &ZeroSeedLaunchParameters,
    now: u64,
) -> Result<(), ZeroSeedLaunchParameterError> {
    type E = ZeroSeedLaunchParameterError;
    if parameters.quote_token.is_zero() {
        return Err(E::UnsupportedQuoteToken);
    }
    if parameters.supply == 0 || parameters.supply > i128::MAX as u128 {
        return Err(E::InvalidParameters);
    }
    let range = &parameters.range;
    if range.tick_spacing == 0
        || range.tick_spacing > EVM_MAX_TICK_SPACING.0
        || range.ask_tick < Evm::min_tick()
        || range.upper_tick > Evm::max_tick()
        || range.ask_tick >= range.upper_tick
    {
        return Err(E::InvalidParameters);
    }
    let fee = &parameters.fee;
    if fee.initial_fee > ZERO_SEED_LAUNCH_MAX_CREATOR_FEE {
        return Err(E::FeeTooHigh);
    }
    if fee.final_fee > fee.initial_fee || fee.fee_duration == 0 || fee.decay_factor == 0 {
        return Err(E::InvalidFeeSchedule);
    }
    if fee.trading_start < now {
        return Err(E::InvalidTradingStart);
    }
    let spacing = range.tick_spacing as i32;
    let (lower, upper) = range.pool_bounds();
    if lower % spacing != 0 || upper % spacing != 0 {
        return Err(E::BoundsTickSpacing);
    }
    Ok(())
}

/// `previewInstallation`: the largest liquidity `parameters.supply` buys and the exact supply
/// that liquidity takes.
pub fn preview_installation_math(
    parameters: &ZeroSeedLaunchParameters,
    now: u64,
) -> Result<ZeroSeedLaunchInstallation, ZeroSeedLaunchParameterError> {
    validate_launch_parameters_math(parameters, now)?;
    let (lower, upper) = range_sqrt_ratios(&parameters.range);
    let liquidity = if parameters.range.launch_token_is_token1 {
        max_liquidity_for_token1(lower, upper, parameters.supply)
    } else {
        max_liquidity_for_token0(lower, upper, parameters.supply)?
    };
    install(&parameters.range, liquidity.min(U256::from(u128::MAX)).to())
}

/// The binding check of `create`: `parameters.supply` must be exactly the amount `liquidity`
/// takes. Returns the installation `create` performs.
pub fn check_launch_binding_math(
    parameters: &ZeroSeedLaunchParameters,
    liquidity: u128,
    now: u64,
) -> Result<ZeroSeedLaunchInstallation, ZeroSeedLaunchParameterError> {
    validate_launch_parameters_math(parameters, now)?;
    let installation = install(&parameters.range, liquidity)?;
    if installation.installed_supply != parameters.supply {
        return Err(ZeroSeedLaunchParameterError::SupplyNotExactlyInstallable {
            requested: parameters.supply,
            installable: installation.installed_supply,
        });
    }
    Ok(installation)
}

/// `_install`: the token amount `Core` takes for `liquidity` at the initial price, rounded up.
fn install(
    range: &ZeroSeedLaunchRange,
    liquidity: u128,
) -> Result<ZeroSeedLaunchInstallation, ZeroSeedLaunchParameterError> {
    if liquidity == 0 {
        return Err(ZeroSeedLaunchParameterError::ZeroLiquidity);
    }
    let cap = max_liquidity_per_tick(range.tick_spacing);
    if liquidity > cap {
        return Err(ZeroSeedLaunchParameterError::LiquidityAboveTickCap { liquidity, cap });
    }
    let (lower, upper) = range_sqrt_ratios(range);
    // Token-only: all token0 from the lower bound, or all token1 below the upper bound.
    let amount = if range.launch_token_is_token1 {
        amount1_delta(lower, upper, liquidity, true)
    } else {
        amount0_delta(lower, upper, liquidity, true)
    }
    .map_err(|_| ZeroSeedLaunchParameterError::Overflow)?;
    if amount > i128::MAX as u128 {
        return Err(ZeroSeedLaunchParameterError::Overflow);
    }
    let (tick_lower, tick_upper) = range.pool_bounds();
    Ok(ZeroSeedLaunchInstallation {
        tick_lower,
        tick_upper,
        initial_tick: range.initial_tick(),
        liquidity,
        installed_supply: amount,
    })
}

/// Validated ranges have bounds inside the tick range.
fn range_sqrt_ratios(range: &ZeroSeedLaunchRange) -> (U256, U256) {
    let (lower, upper) = range.pool_bounds();
    (
        to_sqrt_ratio::<Evm>(lower).expect("validated lower bound"),
        to_sqrt_ratio::<Evm>(upper).expect("validated upper bound"),
    )
}

/// The launch as `LaunchCreated` reports it.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ZeroSeedLaunchConfig {
    /// `LaunchParameters.askTick`, `upperTick` and `tickSpacing`, and the token order from the
    /// event's `token` and pool key.
    pub range: ZeroSeedLaunchRange,
    /// The event's `liquidity`, the constant liquidity of the launch position.
    pub liquidity: u128,
    /// `LaunchParameters.tradingStart`, `feeDuration`, `initialFee`, `finalFee` and
    /// `decayFactor`.
    pub fee: ZeroSeedLaunchFeeSchedule,
}

/// `Core` state of a [`ZeroSeedLaunchPool`]: `Core.poolState` of the launch pool.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ZeroSeedLaunchPoolState {
    /// Pool sqrt ratio, fixed point.
    pub sqrt_ratio: U256,
    /// Pool tick. At a bound it is not always the floor tick of `sqrt_ratio`.
    pub tick: i32,
    /// Active liquidity: the launch position's while the tick is inside it, else 0.
    pub liquidity: u128,
}

/// Resources of a forwarded launch swap.
#[derive(Clone, Copy, Default, Debug, PartialEq, Eq, Hash, Add, AddAssign, Sub, SubAssign)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ZeroSeedLaunchPoolResources {
    /// Resources of the swap on `Core`.
    pub concentrated: ConcentratedPoolResources,
    /// Forwarded launch swaps (1 per quote).
    pub swaps: u32,
}

impl ZeroSeedLaunchPoolResources {
    /// Gas estimate fitted to in-test local fixture gas. Uncalibrated: see the constants.
    #[must_use]
    pub fn uncalibrated_gas_estimate(&self) -> u64 {
        ZERO_SEED_LAUNCH_SWAP_GAS_UNCALIBRATED * u64::from(self.swaps)
            + ZERO_SEED_LAUNCH_EXTRA_BITMAP_LOOKUP_GAS_UNCALIBRATED
                * u64::from(
                    self.concentrated.initialized_ticks_crossed
                        + self.concentrated.extra_distinct_bitmap_lookups,
                )
    }
}

/// Errors that can occur when constructing a [`ZeroSeedLaunchPool`].
#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, Error)]
pub enum ZeroSeedLaunchPoolConstructionError {
    #[error(transparent)]
    Common(#[from] CommonPoolConstructionError),
    #[error("launch pools have no pool fee")]
    FeeMustBeZero,
    #[error("extension must be non-zero")]
    MissingExtension,
    #[error("quote token is not supported")]
    UnsupportedQuoteToken,
    #[error("launch config does not match the pool key")]
    InvalidLaunchConfig,
    #[error("sqrt ratio is outside the launch position")]
    InvalidSqrtRatio,
    #[error("active liquidity does not match the launch position and tick")]
    ActiveLiquidityMismatch,
}

/// Errors that can occur when quoting a [`ZeroSeedLaunchPool`].
#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, Error)]
pub enum ZeroSeedLaunchPoolQuoteError {
    #[error(transparent)]
    Common(#[from] CommonPoolQuoteError),
    /// The forward reverts with `TradingNotStarted`.
    #[error("trading has not started")]
    TradingNotStarted,
    /// Not a valid `Core` sqrt ratio. Stricter than the contract, which ignores an invalid limit
    /// beyond the position bounds.
    #[error("invalid price limit")]
    InvalidSqrtRatioLimit,
    /// `Core` reverts with `SqrtRatioLimitWrongDirection`.
    #[error("price limit in the wrong direction")]
    SqrtRatioLimitWrongDirection,
    /// `amountBeforeFee` reverts: the exact-output gross-up does not fit a `uint128`.
    #[error("amount before fee overflow")]
    AmountBeforeFeeOverflow,
    #[error("amount delta error")]
    AmountDelta(#[from] AmountDeltaError),
    /// A delta does not fit a signed 128-bit amount; the contract reverts.
    #[error("arithmetic overflow")]
    Overflow,
}

/// Why [`ZeroSeedLaunchPool::quote_full_fill`] refuses a quote.
#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, Error)]
pub enum ZeroSeedLaunchFullFillError {
    #[error(transparent)]
    Quote(#[from] ZeroSeedLaunchPoolQuoteError),
    /// The swap stops at a launch bound or the price limit before filling the specified amount.
    #[error("only {filled} of {requested} fills")]
    PartialFill { requested: i128, filled: i128 },
    /// The swap fills but pays out nothing, e.g. dust or a sell with no bid.
    #[error("the swap pays out nothing")]
    ZeroOutput,
}

/// A forwarded swap exactly as `LaunchSwapped` reports it, with the `Core` state after it.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ZeroSeedLaunchSwap {
    /// Fee-inclusive token0 delta from the pool's side, as the locker settles it.
    pub delta0: i128,
    /// Fee-inclusive token1 delta from the pool's side.
    pub delta1: i128,
    /// Creator fee rate at the block timestamp, Q0.64.
    pub fee_rate: u64,
    /// Creator fee added to the creator's ledger.
    pub fee_amount: u128,
    /// Whether the fee is in token1: the calculated side.
    pub fee_is_token1: bool,
    /// `Core` state after the swap.
    pub state_after: ZeroSeedLaunchPoolState,
    pub resources: ZeroSeedLaunchPoolResources,
}

/// Launch pool quoted against the `Core` state of the launch pool.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ZeroSeedLaunchPool {
    key: ZeroSeedLaunchPoolKey,
    launch: ZeroSeedLaunchConfig,
    state: ZeroSeedLaunchPoolState,
    lower_sqrt_ratio: U256,
    upper_sqrt_ratio: U256,
}

/// Result of one iteration of `Core`'s swap loop with non-zero liquidity and a zero pool fee.
struct Step {
    amount_remaining: i128,
    calculated_delta: i128,
    sqrt_ratio_next: U256,
}

struct SwapOutcome {
    delta0: i128,
    delta1: i128,
    initialized_ticks_crossed: u32,
    extra_bitmap_lookups: u32,
}

impl ZeroSeedLaunchPool {
    /// Creates a supported LOCAL launch pool; missing/mismatched provenance refuses it.
    ///
    /// `key` is the pool key from `LaunchCreated`, `launch` the rest of that event and `state`
    /// `Core.poolState` of the pool at the block being quoted. No live instance is supported.
    pub fn new(
        key: ZeroSeedLaunchPoolKey,
        launch: ZeroSeedLaunchConfig,
        state: ZeroSeedLaunchPoolState,
        instance: &ZeroSeedLaunchInstance,
    ) -> Result<Self, ZeroSeedLaunchPoolConstructionError> {
        instance
            .validate()
            .map_err(|_| ZeroSeedLaunchPoolConstructionError::UnsupportedQuoteToken)?;
        let quote = if launch.range.launch_token_is_token1 {
            key.token0
        } else {
            key.token1
        };
        if key.config.extension != instance.extension || quote != instance.constructor_quote {
            return Err(ZeroSeedLaunchPoolConstructionError::UnsupportedQuoteToken);
        }
        Self::new_math(key, launch, state)
    }

    /// Pure pool math, including synthetic quote arithmetic. This is NOT asset/instance approval;
    /// service routing must use `new`, never this constructor. No RPC, calldata or plan production.
    pub fn new_math(
        key: ZeroSeedLaunchPoolKey,
        launch: ZeroSeedLaunchConfig,
        state: ZeroSeedLaunchPoolState,
    ) -> Result<Self, ZeroSeedLaunchPoolConstructionError> {
        type E = ZeroSeedLaunchPoolConstructionError;
        ensure_valid_token_order(&key)?;
        let PoolConfig {
            extension,
            fee,
            pool_type_config: TickSpacing(tick_spacing),
        } = key.config;
        if !fee.is_zero() {
            return Err(E::FeeMustBeZero);
        }
        if extension.is_zero() {
            return Err(E::MissingExtension);
        }
        let quote_token = if launch.range.launch_token_is_token1 {
            key.token0
        } else {
            key.token1
        };
        if quote_token.is_zero() {
            return Err(E::UnsupportedQuoteToken);
        }

        let range = launch.range;
        let fee_schedule = launch.fee;
        // Validate before token-order inversion: negating i32::MIN would overflow.
        if range.ask_tick < Evm::min_tick()
            || range.upper_tick > Evm::max_tick()
            || range.ask_tick >= range.upper_tick
        {
            return Err(E::InvalidLaunchConfig);
        }
        let (lower, upper) = range.pool_bounds();
        if range.tick_spacing != tick_spacing
            || tick_spacing == 0
            || tick_spacing > EVM_MAX_TICK_SPACING.0
            || range.ask_tick >= range.upper_tick
            || lower < Evm::min_tick()
            || upper > Evm::max_tick()
            || lower % tick_spacing as i32 != 0
            || upper % tick_spacing as i32 != 0
            || launch.liquidity == 0
            || launch.liquidity > max_liquidity_per_tick(tick_spacing)
            || fee_schedule.initial_fee > ZERO_SEED_LAUNCH_MAX_CREATOR_FEE
            || fee_schedule.final_fee > fee_schedule.initial_fee
            || fee_schedule.fee_duration == 0
            || fee_schedule.decay_factor == 0
        {
            return Err(E::InvalidLaunchConfig);
        }
        let (lower_sqrt_ratio, upper_sqrt_ratio) = range_sqrt_ratios(&range);

        if state.sqrt_ratio < lower_sqrt_ratio
            || state.sqrt_ratio > upper_sqrt_ratio
            || Evm::adjust_sqrt_ratio_precision(state.sqrt_ratio) != state.sqrt_ratio
        {
            return Err(E::InvalidSqrtRatio);
        }
        let in_range = state.tick >= lower && state.tick < upper;
        if state.liquidity != if in_range { launch.liquidity } else { 0 } {
            return Err(E::ActiveLiquidityMismatch);
        }

        Ok(Self {
            key,
            launch,
            state,
            lower_sqrt_ratio,
            upper_sqrt_ratio,
        })
    }

    /// The launch as `LaunchCreated` reports it.
    #[must_use]
    pub fn launch(&self) -> &ZeroSeedLaunchConfig {
        &self.launch
    }

    /// Creator fee charged at `timestamp`, Q0.64.
    #[must_use]
    pub fn fee_at(&self, timestamp: u64) -> u64 {
        self.launch.fee.fee_at(timestamp)
    }

    /// Simulates the forward `Core.forward(extension, abi.encode(poolKey, swapParameters))` at
    /// block timestamp `timestamp`, with `skipAhead` 0.
    ///
    /// `amount` and `is_token1` are the specified side as in `SwapParameters`: positive for exact
    /// input, negative for exact output. `sqrt_ratio_limit` `None` is the default limit. The
    /// result is the low-level outcome, including partial fills at the launch bounds or the limit
    /// and zero fills; see [`Self::quote_full_fill`] for a refusing variant.
    pub fn simulate_swap(
        &self,
        state: ZeroSeedLaunchPoolState,
        amount: i128,
        is_token1: bool,
        sqrt_ratio_limit: Option<U256>,
        timestamp: u64,
    ) -> Result<ZeroSeedLaunchSwap, ZeroSeedLaunchPoolQuoteError> {
        type E = ZeroSeedLaunchPoolQuoteError;
        if timestamp < self.launch.fee.trading_start {
            return Err(E::TradingNotStarted);
        }
        let increasing = is_price_increasing(amount, is_token1);
        let limit = match sqrt_ratio_limit {
            Some(limit) => {
                if limit < Evm::min_sqrt_ratio()
                    || limit > Evm::max_sqrt_ratio()
                    || Evm::adjust_sqrt_ratio_precision(limit) != limit
                {
                    return Err(E::InvalidSqrtRatioLimit);
                }
                limit
            }
            None if increasing => Evm::max_sqrt_ratio(),
            None => Evm::min_sqrt_ratio(),
        };
        // `_withinPosition`: the price never leaves the position.
        let limit = if increasing {
            limit.min(self.upper_sqrt_ratio)
        } else {
            limit.max(self.lower_sqrt_ratio)
        };

        let mut state_after = state;
        let outcome = self.core_swap(&mut state_after, amount, is_token1, limit)?;

        // The fee is on the calculated side of the actual fill.
        let fee_is_token1 = !is_token1;
        let calculated = if fee_is_token1 {
            outcome.delta1
        } else {
            outcome.delta0
        };
        let calculated_abs = calculated.unsigned_abs();
        let fee_rate = self.fee_at(timestamp);
        let fee_amount = if amount < 0 {
            amount_before_fee::<Evm>(calculated_abs, fee_rate).ok_or(E::AmountBeforeFeeOverflow)?
                - calculated_abs
        } else {
            compute_fee::<Evm>(calculated_abs, fee_rate)
        };
        let with_fee = calculated
            .checked_add(i128::try_from(fee_amount).map_err(|_| E::Overflow)?)
            .ok_or(E::Overflow)?;
        let (delta0, delta1) = if fee_is_token1 {
            (outcome.delta0, with_fee)
        } else {
            (with_fee, outcome.delta1)
        };

        Ok(ZeroSeedLaunchSwap {
            delta0,
            delta1,
            fee_rate,
            fee_amount,
            fee_is_token1,
            state_after,
            resources: ZeroSeedLaunchPoolResources {
                concentrated: ConcentratedPoolResources {
                    no_override_price_change: u32::from(
                        state == self.state && state_after.sqrt_ratio != state.sqrt_ratio,
                    ),
                    initialized_ticks_crossed: outcome.initialized_ticks_crossed,
                    extra_distinct_bitmap_lookups: outcome.extra_bitmap_lookups,
                },
                swaps: 1,
            },
        })
    }

    /// [`Pool::quote`] for routes that require the whole specified amount and a positive output,
    /// like a Yul router route without the partial-fill flag and with a positive minimum output.
    pub fn quote_full_fill(
        &self,
        params: QuoteParams<Address, ZeroSeedLaunchPoolState, BlockTimestamp>,
    ) -> Result<
        Quote<ZeroSeedLaunchPoolResources, ZeroSeedLaunchPoolState>,
        ZeroSeedLaunchFullFillError,
    > {
        let requested = params.token_amount.amount;
        let quote = self.quote(params)?;
        if quote.consumed_amount != requested {
            return Err(ZeroSeedLaunchFullFillError::PartialFill {
                requested,
                filled: quote.consumed_amount,
            });
        }
        if requested > 0 && quote.calculated_amount == 0 {
            return Err(ZeroSeedLaunchFullFillError::ZeroOutput);
        }
        Ok(quote)
    }

    /// Ticks the launch position initializes, with their liquidity deltas.
    fn initialized_ticks(&self) -> [(i32, i128); 2] {
        let (lower, upper) = self.launch.range.pool_bounds();
        // Liquidity is at most Core's per-tick maximum, far below i128::MAX.
        let net = self.launch.liquidity as i128;
        [(lower, net), (upper, -net)]
    }

    /// `Core.swap` on the launch pool with a zero pool fee.
    fn core_swap(
        &self,
        pool: &mut ZeroSeedLaunchPoolState,
        amount: i128,
        is_token1: bool,
        sqrt_ratio_limit: U256,
    ) -> Result<SwapOutcome, ZeroSeedLaunchPoolQuoteError> {
        let mut outcome = SwapOutcome {
            delta0: 0,
            delta1: 0,
            initialized_ticks_crossed: 0,
            extra_bitmap_lookups: 0,
        };
        if amount == 0 || pool.sqrt_ratio == sqrt_ratio_limit {
            return Ok(outcome);
        }

        let increasing = is_price_increasing(amount, is_token1);
        if (sqrt_ratio_limit < pool.sqrt_ratio) == increasing {
            return Err(ZeroSeedLaunchPoolQuoteError::SqrtRatioLimitWrongDirection);
        }

        let spacing = self.key.config.pool_type_config.0;
        let initialized = self.initialized_ticks();

        let mut amount_remaining = amount;
        let mut calculated: i128 = 0;
        let mut steps: u32 = 0;

        loop {
            let (next_tick, is_initialized) = if increasing {
                find_next_initialized_tick(&initialized, pool.tick, spacing, SKIP_AHEAD)
            } else {
                find_prev_initialized_tick(&initialized, pool.tick, spacing, SKIP_AHEAD)
            };
            let next_tick_sqrt_ratio =
                to_sqrt_ratio::<Evm>(next_tick).ok_or(ZeroSeedLaunchPoolQuoteError::Overflow)?;
            let limited = if increasing {
                next_tick_sqrt_ratio.min(sqrt_ratio_limit)
            } else {
                next_tick_sqrt_ratio.max(sqrt_ratio_limit)
            };

            let sqrt_ratio_next = if pool.liquidity == 0 {
                limited
            } else {
                let step = swap_step(
                    pool.sqrt_ratio,
                    pool.liquidity,
                    limited,
                    amount_remaining,
                    is_token1,
                    increasing,
                )?;
                amount_remaining = step.amount_remaining;
                calculated = calculated
                    .checked_add(step.calculated_delta)
                    .ok_or(ZeroSeedLaunchPoolQuoteError::Overflow)?;
                step.sqrt_ratio_next
            };
            steps += 1;

            if sqrt_ratio_next == next_tick_sqrt_ratio {
                pool.sqrt_ratio = sqrt_ratio_next;
                pool.tick = next_tick - i32::from(!increasing);
                if is_initialized {
                    let net = initialized
                        .iter()
                        .find(|(index, _)| *index == next_tick)
                        .map_or(0, |(_, net)| *net);
                    let delta = if increasing { net } else { -net };
                    pool.liquidity = pool
                        .liquidity
                        .checked_add_signed(delta)
                        .ok_or(ZeroSeedLaunchPoolQuoteError::Overflow)?;
                    outcome.initialized_ticks_crossed += 1;
                }
            } else if pool.sqrt_ratio != sqrt_ratio_next {
                pool.sqrt_ratio = sqrt_ratio_next;
                pool.tick = sqrt_ratio_to_tick::<Evm>(sqrt_ratio_next);
            }

            if amount_remaining == 0 || pool.sqrt_ratio == sqrt_ratio_limit {
                break;
            }
        }

        let specified = amount - amount_remaining;
        (outcome.delta0, outcome.delta1) = if is_token1 {
            (calculated, specified)
        } else {
            (specified, calculated)
        };
        outcome.extra_bitmap_lookups = steps
            .saturating_sub(1)
            .saturating_sub(outcome.initialized_ticks_crossed);
        Ok(outcome)
    }
}

fn swap_step(
    sqrt_ratio: U256,
    liquidity: u128,
    limited: U256,
    amount_remaining: i128,
    is_token1: bool,
    increasing: bool,
) -> Result<Step, ZeroSeedLaunchPoolQuoteError> {
    // The pool fee is 0, so the whole remaining amount moves the price and the fee helpers of
    // Core's loop are identities.
    let is_exact_out = amount_remaining < 0;
    let from_amount = if is_token1 {
        next_sqrt_ratio_from_amount1(sqrt_ratio, liquidity, amount_remaining)
            .map(|next| Evm::round_sqrt_ratio(next, false))
    } else {
        next_sqrt_ratio_from_amount0(sqrt_ratio, liquidity, amount_remaining)
            .map(|next| Evm::round_sqrt_ratio(next, true))
    };
    let hit_limit = from_amount.map_or(true, |next| {
        if increasing {
            next > limited
        } else {
            next < limited
        }
    });

    if hit_limit {
        let (specified, calculated) = if is_token1 {
            (
                amount1_delta(limited, sqrt_ratio, liquidity, !is_exact_out)?,
                amount0_delta(limited, sqrt_ratio, liquidity, is_exact_out)?,
            )
        } else {
            (
                amount0_delta(limited, sqrt_ratio, liquidity, !is_exact_out)?,
                amount1_delta(limited, sqrt_ratio, liquidity, is_exact_out)?,
            )
        };
        let (amount_remaining, calculated_delta) = if is_exact_out {
            (amount_remaining + to_i128(specified)?, to_i128(calculated)?)
        } else {
            (
                amount_remaining - to_i128(specified)?,
                -to_i128(calculated)?,
            )
        };
        return Ok(Step {
            amount_remaining,
            calculated_delta,
            sqrt_ratio_next: limited,
        });
    }

    // `hit_limit` is false only for a computed ratio.
    let next = from_amount.unwrap_or(limited);
    if next == sqrt_ratio {
        // The price did not move: Core takes the entire exact input as fees.
        return Ok(Step {
            amount_remaining: 0,
            calculated_delta: 0,
            sqrt_ratio_next: sqrt_ratio,
        });
    }

    let without_fee = if is_token1 {
        amount0_delta(next, sqrt_ratio, liquidity, is_exact_out)?
    } else {
        amount1_delta(next, sqrt_ratio, liquidity, is_exact_out)?
    };
    Ok(Step {
        amount_remaining: 0,
        calculated_delta: if is_exact_out {
            to_i128(without_fee)?
        } else {
            -to_i128(without_fee)?
        },
        sqrt_ratio_next: next,
    })
}

/// `maxLiquidityForToken0` from `math/liquidity.sol`.
fn max_liquidity_for_token0(
    lower: U256,
    upper: U256,
    amount: u128,
) -> Result<U256, ZeroSeedLaunchParameterError> {
    let numerator = muldiv(lower, upper, TWO_POW_128, false)
        .map_err(|_| ZeroSeedLaunchParameterError::Overflow)?;
    muldiv(U256::from(amount), numerator, upper - lower, false)
        .map_err(|_| ZeroSeedLaunchParameterError::Overflow)
}

/// `maxLiquidityForToken1` from `math/liquidity.sol`.
fn max_liquidity_for_token1(lower: U256, upper: U256, amount: u128) -> U256 {
    (U256::from(amount) << 128) / (upper - lower)
}

/// `concentratedMaxLiquidityPerTick` of the pool config.
#[must_use]
pub fn max_liquidity_per_tick(tick_spacing: u32) -> u128 {
    let ticks = 1 + u128::from(Evm::max_tick() as u32 / tick_spacing) * 2;
    u128::MAX / ticks
}

/// `tickToBitmapWordAndIndex`, as one contiguous raw bitmap index.
fn bitmap_raw_index(tick: i32, tick_spacing: u32) -> i64 {
    i64::from(tick).div_euclid(i64::from(tick_spacing)) + TICK_BITMAP_STORAGE_OFFSET
}

fn bitmap_raw_index_to_tick(raw_index: i64, tick_spacing: u32) -> i32 {
    // Raw indices of valid ticks map back into the tick range.
    ((raw_index - TICK_BITMAP_STORAGE_OFFSET) * i64::from(tick_spacing)) as i32
}

/// `findNextInitializedTick` over a bitmap holding only `initialized`.
fn find_next_initialized_tick(
    initialized: &[(i32, i128)],
    from_tick: i32,
    tick_spacing: u32,
    mut skip_ahead: u32,
) -> (i32, bool) {
    let mut next_tick = from_tick;
    loop {
        let raw = bitmap_raw_index(next_tick + tick_spacing as i32, tick_spacing);
        let word_end = (raw >> 8 << 8) + 255;
        let found = initialized
            .iter()
            .map(|(tick, _)| bitmap_raw_index(*tick, tick_spacing))
            .filter(|index| *index >= raw && *index <= word_end)
            .min();
        if let Some(index) = found {
            return (bitmap_raw_index_to_tick(index, tick_spacing), true);
        }
        next_tick = bitmap_raw_index_to_tick(word_end, tick_spacing);
        if next_tick >= Evm::max_tick() {
            return (Evm::max_tick(), false);
        }
        if skip_ahead == 0 {
            return (next_tick, false);
        }
        skip_ahead -= 1;
    }
}

/// `findPrevInitializedTick` over a bitmap holding only `initialized`.
fn find_prev_initialized_tick(
    initialized: &[(i32, i128)],
    from_tick: i32,
    tick_spacing: u32,
    mut skip_ahead: u32,
) -> (i32, bool) {
    let mut prev_tick = from_tick;
    loop {
        let raw = bitmap_raw_index(prev_tick, tick_spacing);
        let word_start = raw >> 8 << 8;
        let found = initialized
            .iter()
            .map(|(tick, _)| bitmap_raw_index(*tick, tick_spacing))
            .filter(|index| *index >= word_start && *index <= raw)
            .max();
        if let Some(index) = found {
            return (bitmap_raw_index_to_tick(index, tick_spacing), true);
        }
        prev_tick = bitmap_raw_index_to_tick(word_start, tick_spacing);
        if prev_tick <= Evm::min_tick() {
            return (Evm::min_tick(), false);
        }
        if skip_ahead == 0 {
            return (prev_tick, false);
        }
        skip_ahead -= 1;
        prev_tick -= 1;
    }
}

fn to_i128(value: u128) -> Result<i128, ZeroSeedLaunchPoolQuoteError> {
    i128::try_from(value).map_err(|_| ZeroSeedLaunchPoolQuoteError::Overflow)
}

impl Pool for ZeroSeedLaunchPool {
    type Address = Address;
    type Fee = <Evm as Chain>::Fee;
    type Resources = ZeroSeedLaunchPoolResources;
    type State = ZeroSeedLaunchPoolState;
    type QuoteError = ZeroSeedLaunchPoolQuoteError;
    type Meta = BlockTimestamp;
    type PoolTypeConfig = ZeroSeedLaunchPoolTypeConfig;

    fn key(&self) -> ZeroSeedLaunchPoolKey {
        self.key
    }

    fn state(&self) -> Self::State {
        self.state
    }

    /// Quotes the forwarded launch swap at block timestamp `meta`.
    ///
    /// Low level: `consumed_amount` is the specified amount that fills, which is less than
    /// requested when the swap reaches a launch bound or the limit, and may be 0. Use
    /// [`ZeroSeedLaunchPool::quote_full_fill`] to refuse partial and zero fills.
    /// `calculated_amount` includes the creator fee: the output net of it for exact input, the
    /// input grossed up by it for exact output. `fees_paid` is the creator fee.
    fn quote(
        &self,
        params: QuoteParams<Self::Address, Self::State, Self::Meta>,
    ) -> Result<Quote<Self::Resources, Self::State>, Self::QuoteError> {
        let amount = params.token_amount.amount;
        let is_token1 = is_token1(&self.key, params.token_amount.token)?;
        let swap = self.simulate_swap(
            params.override_state.unwrap_or(self.state),
            amount,
            is_token1,
            params.sqrt_ratio_limit,
            params.meta,
        )?;
        let (specified, calculated) = if is_token1 {
            (swap.delta1, swap.delta0)
        } else {
            (swap.delta0, swap.delta1)
        };
        Ok(Quote {
            is_price_increasing: is_price_increasing(amount, is_token1),
            consumed_amount: specified,
            calculated_amount: calculated.unsigned_abs(),
            execution_resources: swap.resources,
            state_after: swap.state_after,
            fees_paid: swap.fee_amount,
        })
    }

    fn has_liquidity(&self) -> bool {
        true
    }

    fn max_tick_with_liquidity(&self) -> Option<i32> {
        Some(self.launch.range.pool_bounds().1)
    }

    fn min_tick_with_liquidity(&self) -> Option<i32> {
        Some(self.launch.range.pool_bounds().0)
    }

    fn is_path_dependent(&self) -> bool {
        // The creator fee depends on the block timestamp; the Core curve itself is not
        // path dependent beyond rounding.
        true
    }
}

impl PoolState for ZeroSeedLaunchPoolState {
    fn sqrt_ratio(&self) -> U256 {
        self.sqrt_ratio
    }

    fn liquidity(&self) -> u128 {
        self.liquidity
    }
}

impl private::Sealed for ZeroSeedLaunchPool {}
impl private::Sealed for ZeroSeedLaunchPoolState {}

#[cfg(test)]
mod fee_curve_tests;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bitmap_search_matches_core_word_boundaries() {
        // Tick 0 is raw index 89_421_695 = 349_303 * 256 + 127 for every spacing.
        assert_eq!(find_next_initialized_tick(&[], 0, 100, 0), (12_800, false));
        assert_eq!(find_prev_initialized_tick(&[], 0, 100, 0), (-12_700, false));
        assert_eq!(
            find_next_initialized_tick(&[(0, 1), (100, -1)], 0, 100, 0),
            (100, true)
        );
        assert_eq!(
            find_prev_initialized_tick(&[(0, 1), (100, -1)], 99, 100, 0),
            (0, true)
        );
        assert_eq!(
            find_next_initialized_tick(&[], Evm::max_tick() - 1, 1, 0),
            (Evm::max_tick(), false)
        );
        assert_eq!(
            find_prev_initialized_tick(&[], Evm::min_tick(), 1, 0),
            (Evm::min_tick(), false)
        );
    }

    #[test]
    fn max_liquidity_per_tick_matches_core() {
        assert_eq!(
            max_liquidity_per_tick(100),
            u128::MAX / (1 + (88_722_835 / 100) * 2)
        );
    }

    #[test]
    fn fee_schedule_is_monotone_and_bounded() {
        let schedule = ZeroSeedLaunchFeeSchedule {
            trading_start: 1_000,
            fee_duration: 3_600,
            initial_fee: ZERO_SEED_LAUNCH_MAX_CREATOR_FEE,
            final_fee: 0,
            decay_factor: 18_425_445_863_997_925_462,
        };
        let mut previous = schedule.fee_at(0);
        for t in (0..6_000).chain([u64::MAX - 1, u64::MAX]) {
            let fee = schedule.fee_at(t);
            assert!(fee <= previous && fee <= schedule.initial_fee);
            previous = fee;
        }
        assert_eq!(schedule.fee_at(u64::MAX), 0);
    }
}
