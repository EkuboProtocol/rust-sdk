//! Quoting and installation math for pools of the `ZeroSeedLaunch` extension.
//!
//! A zero-seed launch mints a fixed requested supply and installs the largest liquidity it buys,
//! in one transaction, as a single token-only concentrated position from the ask price up to an
//! upper bound, with no quote seed. The rounding remainder of the requested supply, the sink
//! supply, is minted directly to `address(0)`, so the token's `totalSupply` is exactly the
//! requested supply. The pool fee is 0. The pool, the position and its liquidity never change
//! after creation: only swaps forwarded through the extension (`Core.forward` with
//! `abi.encode(PoolKey, SwapParameters)`) move the price, every swap's price limit is clamped to
//! the installed bounds and its skip-ahead is replaced by 1 ([`ZERO_SEED_LAUNCH_SKIP_AHEAD`]).
//!
//! The pool's tick spacing is derived from the requested economic range,
//! `ceil((upperTick - askTick) / 256)`, and both bounds move inward onto that grid
//! ([`align_launch_range`]), so the installed range spans at most 256 spacing steps.
//!
//! Time only lowers the creator fee: `initialFee` until `tradingStart`, then the excess over the
//! long-run floor `finalFee` shrinks by `tickToSqrtRatio(-m)` with
//! `m = floor(decayRateX32 * elapsed / 2**32)` ([`decayed_fee`]). The creator fee is charged on
//! the calculated side of the actual fill and saved separately from the position.
//!
//! One extension deployment serves every quote: each launch selects its own quote token in
//! `LaunchParameters.quoteToken`, native ETH (`address(0)`, always token0, so the launch token is
//! token1) or an ERC-20. Launches are normally created through `ZeroSeedLaunchPeriphery`, which
//! is the launch controller, records the transferable owner and namespaces the salt by owner; see
//! [`periphery_launch_token_address`].
//!
//! The model mirrors `ZeroSeedLaunch.handleForwardData` and the `Core` swap loop step by step,
//! including the tick bitmap word boundaries, so it reproduces the contract's deltas, creator fee
//! and post-swap `Core` state exactly. [`preview_installation`] mirrors `previewInstallation`,
//! which `create` runs on the same inputs.
//!
//! Target: `EkuboProtocol/evm-contracts@853b608ec26d4c80bdad6e394cb8ba686e1ae615` against its
//! Q0.64-fee `Core`. The SDK knows no deployment of this contract: callers supply the instance
//! they have configured, and nothing here approves an instance or a quote token on its own.

use core::str::FromStr;
use derive_more::{Add, AddAssign, Sub, SubAssign};
use num_traits::Zero;
use ruint::aliases::{U256, U512};
use thiserror::Error;

use crate::{
    alloy_primitives::{B256, Keccak256},
    chain::{Chain, evm::Evm},
    math::{
        delta::{AmountDeltaError, amount0_delta, amount1_delta},
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

/// Source commit of the contract this module models.
pub const ZERO_SEED_LAUNCH_SOURCE_COMMIT: &str = "853b608ec26d4c80bdad6e394cb8ba686e1ae615";

/// `MAX_SUPPLY`: the largest requested supply in base units, `10**30` (one trillion tokens at the
/// fixed 18 decimals).
pub const ZERO_SEED_LAUNCH_MAX_SUPPLY: u128 = 1_000_000_000_000_000_000_000_000_000_000;

/// Decimals of every launch token. Not a parameter.
pub const ZERO_SEED_LAUNCH_DECIMALS: u8 = 18;

/// `LAUNCH_RANGE_STEPS`: spacing steps an installed range spans at most.
pub const ZERO_SEED_LAUNCH_RANGE_STEPS: u32 = 256;

/// `MAX_LAUNCH_TICK_SPACING`: the largest spacing [`align_launch_range`] produces, for the full
/// tick range. Below Core's maximum tick spacing, so no clamp exists.
pub const ZERO_SEED_LAUNCH_MAX_TICK_SPACING: u32 = 693_148;

/// `LAUNCH_SKIP_AHEAD`: the skip-ahead the extension sets on every forwarded swap, whatever the
/// caller sends.
pub const ZERO_SEED_LAUNCH_SKIP_AHEAD: u32 = 1;

/// Highest creator fee rate, Q0.64: `type(uint64).max = 2**64 - 1`, just under 100%, never
/// exactly 100%. Every `uint64` initial and final fee is accepted; only `final <= initial` is
/// checked. A bound of the type, not a suggested rate.
pub const ZERO_SEED_LAUNCH_MAX_CREATOR_FEE: u64 = u64::MAX;

/// 2**64: the Q0.64 unit, exactly 100%. Not encodable as a `u64` fee.
pub const ZERO_SEED_LAUNCH_Q64: u128 = 1 << 64;

/// Consumer default initial creator fee: 50% (`2**63`). A creation parameter choice, not a
/// contract constant.
pub const ZERO_SEED_LAUNCH_DEFAULT_INITIAL_FEE: u64 = 1 << 63;

/// Consumer default final creator fee: 0.3% (`floor(2**64 * 3 / 1000)`). A creation parameter
/// choice, not a contract constant.
pub const ZERO_SEED_LAUNCH_DEFAULT_FINAL_FEE: u64 = 55_340_232_221_128_654;

/// Largest tick magnitude the EVM tick helper supports, `MAX_TICK_MAGNITUDE` of the contracts.
pub const ZERO_SEED_LAUNCH_MAX_TICK_MAGNITUDE: u64 = 88_722_835;

/// `MAX_DECAY_PRODUCT` of `math/feeDecay.sol`: `(MAX_TICK_MAGNITUDE + 1) * 2**32 - 1 =
/// 381061679028371455`, the largest `decayRateX32 * elapsed` whose magnitude the tick helper
/// supports.
pub const ZERO_SEED_LAUNCH_MAX_DECAY_PRODUCT: u64 =
    ((ZERO_SEED_LAUNCH_MAX_TICK_MAGNITUDE + 1) << 32) - 1;

/// Consumer default `decayRateX32`: a one-day half-life of the excess over the floor,
/// [`decay_rate_x32_for_half_life`] of 86400. A creation parameter choice, not a contract
/// constant.
pub const ZERO_SEED_LAUNCH_DEFAULT_DECAY_RATE_X32: u64 = 68_913_100_933;

/// `floor(2 * ln 2 / ln 1.000001 * 2**32 * 10**30)`: ticks per half-life of the excess, Q32.32,
/// scaled by `10**30`. The normative integer for every half-life conversion; never use a float.
pub const ZERO_SEED_LAUNCH_HALF_LIFE_X32_E30: &str =
    "5954091920683119788732747343471285361579197626";

/// Creation code of `LaunchToken` at the target, without constructor arguments.
pub static LAUNCH_TOKEN_CREATION_CODE: [u8; 3172] =
    decode_hex(include_str!("zero_seed_launch/LaunchToken.creation.hex"));

/// Keccak of [`LAUNCH_TOKEN_CREATION_CODE`], `pins.creationCode.LaunchToken` of the contract
/// vectors.
pub const LAUNCH_TOKEN_CREATION_CODE_KECCAK: &str =
    "0xb92240f5b935a76e949aab04e7e9e4a0a28adc3ff1a89a349c67dcaab13ea432";

/// Offset `Core` adds to compressed ticks to index its tick bitmaps.
const TICK_BITMAP_STORAGE_OFFSET: i64 = 89_421_695;

// Gas estimates of the forwarded swap frame (test locker, token settlement included), from the
// in-test warm gas of the contract vectors at the target: a second buy costs 34,078 and a sell
// 34,167. They exclude the 21,000 transaction base, calldata, the router and any account
// abstraction overhead. A swap that writes a zero storage slot, such as the first creator fee
// after a claim or the first launch tokens a holder receives, costs about 20,000 more per slot,
// which the pool state cannot predict; the first buy of a launch measured 102,296. Calibrate
// against execution before relying on them.

/// A forwarded launch swap that loads one tick bitmap word.
pub const ZERO_SEED_LAUNCH_SWAP_GAS_UNCALIBRATED: u64 = 34_100;
/// Extra gas per crossed bound or additional swap step. With skip-ahead 1 a swap across the whole
/// range takes at most two steps.
pub const ZERO_SEED_LAUNCH_EXTRA_BITMAP_LOOKUP_GAS_UNCALIBRATED: u64 = 4_300;

const fn decode_hex<const N: usize>(hex: &str) -> [u8; N] {
    const fn nibble(c: u8) -> u8 {
        match c {
            b'0'..=b'9' => c - b'0',
            b'a'..=b'f' => c - b'a' + 10,
            b'A'..=b'F' => c - b'A' + 10,
            _ => panic!("invalid hex digit"),
        }
    }
    let bytes = hex.as_bytes();
    assert!(bytes.len() == 2 * N || (bytes.len() == 2 * N + 1 && bytes[2 * N] == b'\n'));
    let mut out = [0u8; N];
    let mut i = 0;
    while i < N {
        out[i] = (nibble(bytes[2 * i]) << 4) | nibble(bytes[2 * i + 1]);
        i += 1;
    }
    out
}

/// Why `previewInstallation` or `create` refuses a launch, by contract error, or why the SDK
/// refuses to support it.
#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, Error)]
pub enum ZeroSeedLaunchParameterError {
    /// `UnsupportedQuoteToken`: a nonzero quote without code.
    #[error("quote token has no code")]
    UnsupportedQuoteToken,
    /// An ERC-20 quote without a reviewed `(chain, address, runtime keccak)` entry of the caller's
    /// list. SDK support policy, not a contract refusal.
    #[error("quote token is not reviewed")]
    QuoteNotReviewed,
    /// `InvalidMetadata`: name or symbol is not a canonical packed 1..31 byte string.
    #[error("name or symbol is not a canonical packed string of 1 to 31 bytes")]
    InvalidMetadata,
    /// `InvalidSupply`: supply 0 or above [`ZERO_SEED_LAUNCH_MAX_SUPPLY`].
    #[error("supply is 0 or above 10**30")]
    InvalidSupply,
    /// `InvalidTicks`: not `MIN_TICK <= askTick < upperTick <= MAX_TICK`.
    #[error("invalid launch ticks")]
    InvalidTicks,
    /// `InvalidFeeSchedule`: final fee above the initial fee.
    #[error("final fee above initial fee")]
    InvalidFeeSchedule,
    /// `InvalidTradingStart`: trading start before the block timestamp.
    #[error("trading start is in the past")]
    InvalidTradingStart,
    /// `LaunchTokenExists(token)`: the predicted launch token address has code.
    #[error("predicted launch token address has code")]
    LaunchTokenExists,
    /// `ZeroLiquidity`: the requested supply buys no liquidity.
    #[error("supply buys zero liquidity")]
    ZeroLiquidity,
    /// `LiquidityAboveTickCap(liquidity, cap)`.
    #[error("liquidity {liquidity} above the per-tick cap {cap}")]
    LiquidityAboveTickCap { liquidity: u128, cap: u128 },
    /// An installed range that the spacing rule cannot produce: misaligned, unordered, out of the
    /// tick range or wider than 256 steps. SDK refusal for inputs that do not come from the
    /// contract.
    #[error("installed range is not an aligned launch range")]
    InvalidInstalledRange,
    /// The pool key's extension is not the instance's.
    #[error("pool key extension is not the instance's extension")]
    InstanceMismatch,
    /// `InvalidRecipient` of `ZeroSeedLaunchPeriphery.claimFees`.
    #[error("invalid claim recipient")]
    InvalidRecipient,
    /// The producer timing rule of [`validate_producer_timing`]. Not a contract refusal.
    #[error("invalid or stale start/expiry context")]
    InvalidProducerTiming,
    /// An arithmetic bound of the model; the contract would revert.
    #[error("installation amount overflow")]
    Overflow,
}

type E = ZeroSeedLaunchParameterError;

// ---------------------------------------------------------------------------------------------
// Metadata and identity
// ---------------------------------------------------------------------------------------------

/// `isCanonicalPackedString`: byte 0 is the length 1..31, bytes `1..=length` the content and
/// every later byte zero.
#[must_use]
pub fn is_canonical_launch_metadata(word: &B256) -> bool {
    let length = usize::from(word[0]);
    (1..=31).contains(&length) && word[length + 1..].iter().all(|b| *b == 0)
}

/// `LibString.packOne` of 1..31 bytes, with an explicitly zero tail. Length is in bytes; content
/// is not interpreted, so any bytes, including zero bytes, round-trip. Never truncates.
pub fn pack_launch_metadata(content: &[u8]) -> Result<B256, ZeroSeedLaunchParameterError> {
    if content.is_empty() || content.len() > 31 {
        return Err(E::InvalidMetadata);
    }
    let mut word = [0u8; 32];
    word[0] = content.len() as u8;
    word[1..=content.len()].copy_from_slice(content);
    Ok(B256::from(word))
}

/// The content of a canonical packed word, `None` for a non-canonical word.
#[must_use]
pub fn unpack_launch_metadata(word: &B256) -> Option<&[u8]> {
    is_canonical_launch_metadata(word).then(|| &word[1..=usize::from(word[0])])
}

fn address_word(address: Address) -> [u8; 32] {
    let mut word = [0u8; 32];
    word[12..].copy_from_slice(address.as_slice());
    word
}

/// `keccak256(abi.encode(address, bytes32))`.
fn keccak_address_salt(address: Address, salt: B256) -> B256 {
    let mut hasher = Keccak256::new();
    hasher.update(address_word(address));
    hasher.update(salt.as_slice());
    hasher.finalize()
}

/// The salt the periphery passes to the extension for `owner`: `keccak256(abi.encode(owner,
/// user_salt))`. `LaunchCreated.parameters.salt` carries this value.
#[must_use]
pub fn periphery_launch_salt(owner: Address, user_salt: B256) -> B256 {
    keccak_address_salt(owner, user_salt)
}

/// The CREATE2 salt of a launch token: `keccak256(abi.encode(controller, salt))`, with `salt` the
/// extension-level `LaunchParameters.salt`.
#[must_use]
pub fn extension_token_salt(controller: Address, salt: B256) -> B256 {
    keccak_address_salt(controller, salt)
}

/// `keccak256(LaunchToken.creationCode ++ abi.encode(name, symbol))` over the packed words.
#[must_use]
pub fn launch_token_init_code_hash(name: B256, symbol: B256) -> B256 {
    let mut hasher = Keccak256::new();
    hasher.update(&LAUNCH_TOKEN_CREATION_CODE[..]);
    hasher.update(name.as_slice());
    hasher.update(symbol.as_slice());
    hasher.finalize()
}

/// The launch token `extension` deploys for a creation forwarded by `controller` with the
/// extension-level `salt`. Independent of the quote, supply, range, fees and logo.
#[must_use]
pub fn launch_token_address(
    extension: Address,
    controller: Address,
    salt: B256,
    name: B256,
    symbol: B256,
) -> Address {
    let mut hasher = Keccak256::new();
    hasher.update([0xff]);
    hasher.update(extension.as_slice());
    hasher.update(extension_token_salt(controller, salt).as_slice());
    hasher.update(launch_token_init_code_hash(name, symbol).as_slice());
    Address::from_slice(&hasher.finalize()[12..])
}

/// The launch token `periphery.create` deploys when `owner` calls it with `user_salt`.
#[must_use]
pub fn periphery_launch_token_address(
    extension: Address,
    periphery: Address,
    owner: Address,
    user_salt: B256,
    name: B256,
    symbol: B256,
) -> Address {
    launch_token_address(
        extension,
        periphery,
        periphery_launch_salt(owner, user_salt),
        name,
        symbol,
    )
}

// ---------------------------------------------------------------------------------------------
// Ranges
// ---------------------------------------------------------------------------------------------

/// `alignLaunchRange` of `src/math/launchRange.sol`, after the contract's `InvalidTicks` check:
/// `(spacing, aligned_ask, aligned_upper)` with `spacing = ceil((upper - ask) / 256)`,
/// `aligned_ask = ceil(ask / spacing) * spacing` and
/// `aligned_upper = floor(upper / spacing) * spacing`, mathematical signed ceiling and floor.
pub fn align_launch_range(
    ask_tick: i32,
    upper_tick: i32,
) -> Result<(u32, i32, i32), ZeroSeedLaunchParameterError> {
    if ask_tick < Evm::min_tick() || upper_tick > Evm::max_tick() || ask_tick >= upper_tick {
        return Err(E::InvalidTicks);
    }
    let (ask, upper) = (i64::from(ask_tick), i64::from(upper_tick));
    let spacing = (upper - ask + i64::from(ZERO_SEED_LAUNCH_RANGE_STEPS) - 1)
        / i64::from(ZERO_SEED_LAUNCH_RANGE_STEPS);
    let aligned_ask = -(-ask).div_euclid(spacing) * spacing;
    let aligned_upper = upper.div_euclid(spacing) * spacing;
    // The bounds move inward, so both stay in the tick range; the spacing is at most 693148.
    Ok((spacing as u32, aligned_ask as i32, aligned_upper as i32))
}

/// The installed range of a launch: derived spacing and aligned economic bounds, as
/// `Installation.tickSpacing`, `askTick` and `upperTick` report them.
///
/// Ticks are log base 1.000001 of raw quote units per raw launch-token unit, so neither decimals
/// nor token order change their meaning. For a token0 launch the position is
/// `[ask_tick, upper_tick]` and the pool starts at `ask_tick`; for a token1 launch it is
/// `[-upper_tick, -ask_tick]` and the pool starts at `-ask_tick`. `LaunchCreated.parameters`
/// carries the requested bounds instead; [`Self::from_requested`] aligns them.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ZeroSeedLaunchRange {
    /// Whether the launch token is token1 of the pool, i.e. the quote token address is lower.
    pub launch_token_is_token1: bool,
    /// Pool tick spacing derived from the requested width.
    pub tick_spacing: u32,
    /// Installed economic lower bound and starting price: the requested ask rounded up.
    pub ask_tick: i32,
    /// Installed economic upper bound, where buys stop: the requested upper rounded down.
    pub upper_tick: i32,
}

impl ZeroSeedLaunchRange {
    /// The installed range for requested economic bounds, with the contract's `InvalidTicks`.
    pub fn from_requested(
        launch_token_is_token1: bool,
        ask_tick: i32,
        upper_tick: i32,
    ) -> Result<Self, ZeroSeedLaunchParameterError> {
        let (tick_spacing, ask_tick, upper_tick) = align_launch_range(ask_tick, upper_tick)?;
        Ok(Self {
            launch_token_is_token1,
            tick_spacing,
            ask_tick,
            upper_tick,
        })
    }

    /// Whether the range is one the spacing rule can install: spacing 1..=693148, bounds in the
    /// tick range, aligned, ordered and at most 256 steps apart.
    pub fn validate(&self) -> Result<(), ZeroSeedLaunchParameterError> {
        let spacing = i64::from(self.tick_spacing);
        let (ask, upper) = (i64::from(self.ask_tick), i64::from(self.upper_tick));
        if self.tick_spacing == 0
            || self.tick_spacing > ZERO_SEED_LAUNCH_MAX_TICK_SPACING
            || self.ask_tick < Evm::min_tick()
            || self.upper_tick > Evm::max_tick()
            || ask >= upper
            || ask % spacing != 0
            || upper % spacing != 0
            || (upper - ask) / spacing > i64::from(ZERO_SEED_LAUNCH_RANGE_STEPS)
        {
            return Err(E::InvalidInstalledRange);
        }
        Ok(())
    }

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

    /// `PositionId` of the launch position: salt 0, then the pool tick bounds.
    #[must_use]
    pub fn position_id(&self) -> B256 {
        let (lower, upper) = self.pool_bounds();
        let mut word = [0u8; 32];
        word[24..28].copy_from_slice(&lower.to_be_bytes());
        word[28..].copy_from_slice(&upper.to_be_bytes());
        B256::from(word)
    }

    /// Core's fixed sqrt ratios of the pool bounds. Only for validated ranges.
    fn sqrt_ratios(&self) -> (U256, U256) {
        let (lower, upper) = self.pool_bounds();
        (
            to_sqrt_ratio::<Evm>(lower).expect("validated lower bound"),
            to_sqrt_ratio::<Evm>(upper).expect("validated upper bound"),
        )
    }
}

// ---------------------------------------------------------------------------------------------
// Fees
// ---------------------------------------------------------------------------------------------

/// Creator fee schedule, as in `LaunchParameters` and `Launch`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ZeroSeedLaunchFeeSchedule {
    /// First timestamp at which swaps are accepted; the decay starts here.
    pub trading_start: u64,
    /// Unsigned Q32.32 ticks per second (`2**32` is one tick per second). Every value is valid;
    /// 0 keeps the fee flat at `initial_fee`.
    pub decay_rate_x32: u64,
    /// Creator fee until `trading_start`, Q0.64.
    pub initial_fee: u64,
    /// The long-run floor the fee approaches, Q0.64, reached only by rounding or saturation.
    pub final_fee: u64,
}

impl ZeroSeedLaunchFeeSchedule {
    /// `feeAt`: the creator fee at `timestamp`, Q0.64: `initial_fee` until `trading_start`
    /// (inclusive), then [`decayed_fee`] of the elapsed seconds.
    #[must_use]
    pub fn fee_at(&self, timestamp: u64) -> u64 {
        if timestamp <= self.trading_start {
            return self.initial_fee;
        }
        decayed_fee(
            self.initial_fee,
            self.final_fee,
            self.decay_rate_x32,
            timestamp - self.trading_start,
        )
    }

    /// The contract's `InvalidFeeSchedule` check: `final_fee <= initial_fee`. Every rate is valid.
    #[must_use]
    pub fn is_valid(&self) -> bool {
        self.final_fee <= self.initial_fee
    }
}

fn half_life_x32_e30() -> U256 {
    U256::from_str(ZERO_SEED_LAUNCH_HALF_LIFE_X32_E30).expect("static constant")
}

/// `decayRateX32` for a half-life of the excess of `seconds`:
/// `floor(HALF_LIFE_X32_E30 / (seconds * 10**30))`. `None` for 0 seconds. A half-life above
/// about `5.95e15` seconds gives 0, a flat fee.
#[must_use]
pub fn decay_rate_x32_for_half_life(seconds: u64) -> Option<u64> {
    if seconds == 0 {
        return None;
    }
    let rate = half_life_x32_e30() / (U256::from(seconds) * U256::from(10).pow(U256::from(30)));
    Some(rate.to::<u64>())
}

/// The half-life of the excess for `decay_rate_x32`, in whole microseconds, floored. `None` for
/// rate 0 (no decay). Display only: the fee follows [`decayed_fee`], not this value.
#[must_use]
pub fn half_life_micros(decay_rate_x32: u64) -> Option<u128> {
    if decay_rate_x32 == 0 {
        return None;
    }
    let micros =
        half_life_x32_e30() / (U256::from(decay_rate_x32) * U256::from(10).pow(U256::from(24)));
    // At most HALF_LIFE_X32_E30 / 10**24 < 2**73.
    Some(micros.to::<u128>())
}

/// The last elapsed second at which the curve is still evaluated:
/// `floor(MAX_DECAY_PRODUCT / decay_rate_x32)`. From the next second the fee is exactly
/// `final_fee` by numerical saturation; this is not a schedule end. `None` for rate 0.
#[must_use]
pub fn saturation_elapsed_seconds(decay_rate_x32: u64) -> Option<u64> {
    (decay_rate_x32 != 0).then(|| ZERO_SEED_LAUNCH_MAX_DECAY_PRODUCT / decay_rate_x32)
}

/// `tickToSqrtRatio(-magnitude).toFixed()` of the contracts: the compact (94-bit mantissa, rounded
/// down) sqrt ratio as 64.128 fixed point, at most `2**128`. `None` above
/// [`ZERO_SEED_LAUNCH_MAX_TICK_MAGNITUDE`], where the helper reverts.
#[must_use]
pub fn tick_rate_factor_q128(magnitude: u64) -> Option<U256> {
    if magnitude > ZERO_SEED_LAUNCH_MAX_TICK_MAGNITUDE {
        return None;
    }
    to_sqrt_ratio::<Evm>(-(magnitude as i32))
}

/// `decayedFee` from `math/feeDecay.sol`, in its normative order: rate 0 is `initial_fee`;
/// `elapsed > MAX_DECAY_PRODUCT / rate` (integer division, before any multiply) is `final_fee`;
/// else `m = (rate * elapsed) >> 32` and
/// `final_fee + floor((initial_fee - final_fee) * tick_rate_factor_q128(m) / 2**128)`. Creation
/// requires `final_fee <= initial_fee`; for other inputs the subtraction wraps as in the
/// contract's `unchecked` block.
#[must_use]
pub fn decayed_fee(initial_fee: u64, final_fee: u64, decay_rate_x32: u64, elapsed: u64) -> u64 {
    if decay_rate_x32 == 0 {
        return initial_fee;
    }
    if elapsed > ZERO_SEED_LAUNCH_MAX_DECAY_PRODUCT / decay_rate_x32 {
        return final_fee;
    }
    // The guard bounds the product by MAX_DECAY_PRODUCT < 2**59.
    let magnitude = (u128::from(decay_rate_x32) * u128::from(elapsed)) >> 32;
    let factor = tick_rate_factor_q128(magnitude as u64).expect("guarded magnitude");
    let excess: U256 = (U256::from(initial_fee.wrapping_sub(final_fee)) * factor) >> 128;
    final_fee.wrapping_add(excess.to::<u64>())
}

// ---------------------------------------------------------------------------------------------
// Parameters and installation
// ---------------------------------------------------------------------------------------------

/// `LaunchParameters`, the static eleven-word tuple `create` and `previewInstallation` take.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ZeroSeedLaunchParameters {
    /// Canonical packed name, see [`pack_launch_metadata`].
    pub name: B256,
    /// Canonical packed symbol.
    pub symbol: B256,
    /// The requested supply, submitted unchanged. It is the token's `totalSupply` after
    /// creation; never rewrite it to the installed supply.
    pub supply: u128,
    /// This launch's quote, `address(0)` for native ETH.
    pub quote_token: Address,
    /// Requested economic ask; installed rounded up to the derived spacing.
    pub ask_tick: i32,
    /// Requested economic upper bound; installed rounded down.
    pub upper_tick: i32,
    pub trading_start: u64,
    pub decay_rate_x32: u64,
    pub initial_fee: u64,
    pub final_fee: u64,
    /// The extension-level salt; the periphery passes [`periphery_launch_salt`].
    pub salt: B256,
}

impl ZeroSeedLaunchParameters {
    /// The fee schedule of these parameters.
    #[must_use]
    pub fn fee_schedule(&self) -> ZeroSeedLaunchFeeSchedule {
        ZeroSeedLaunchFeeSchedule {
            trading_start: self.trading_start,
            decay_rate_x32: self.decay_rate_x32,
            initial_fee: self.initial_fee,
            final_fee: self.final_fee,
        }
    }

    /// `_validate` without the quote code check, in the contract's order: metadata, supply,
    /// ticks, fee schedule, trading start. `now` is the block timestamp of the call.
    pub fn validate(&self, now: u64) -> Result<(), ZeroSeedLaunchParameterError> {
        if !is_canonical_launch_metadata(&self.name) || !is_canonical_launch_metadata(&self.symbol)
        {
            return Err(E::InvalidMetadata);
        }
        validate_supply(self.supply)?;
        align_launch_range(self.ask_tick, self.upper_tick)?;
        if !self.fee_schedule().is_valid() {
            return Err(E::InvalidFeeSchedule);
        }
        if self.trading_start < now {
            return Err(E::InvalidTradingStart);
        }
        Ok(())
    }
}

fn validate_supply(supply: u128) -> Result<(), ZeroSeedLaunchParameterError> {
    if supply == 0 || supply > ZERO_SEED_LAUNCH_MAX_SUPPLY {
        return Err(E::InvalidSupply);
    }
    Ok(())
}

/// The installation of a supply into an installed range: what `previewInstallation` reports
/// besides the token address and pool key, plus the sink.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ZeroSeedLaunchInstallation {
    /// The installed range (`Installation.tickSpacing`, `askTick`, `upperTick`).
    pub range: ZeroSeedLaunchRange,
    /// Launch position lower bound, pool tick.
    pub tick_lower: i32,
    /// Launch position upper bound, pool tick.
    pub tick_upper: i32,
    /// Pool tick at creation.
    pub initial_tick: i32,
    /// Liquidity of the launch position: the largest the requested supply buys, as
    /// `LaunchCreated.liquidity` reports it.
    pub liquidity: u128,
    /// `Installation.installedSupply`: the exact launch-token amount `Core` takes for
    /// `liquidity`, rounded up, `0 < installed_supply <= supply`.
    pub installed_supply: u128,
    /// `supply - installed_supply`, minted directly to `address(0)` at creation. Never spendable
    /// and not an ERC-20 burn: `totalSupply` stays the requested supply.
    pub sink_supply: u128,
}

/// `Installation` of `previewInstallation`: the token, pool key and installation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ZeroSeedLaunchPreview {
    pub token: Address,
    pub pool_key: ZeroSeedLaunchPoolKey,
    pub position_id: B256,
    pub installation: ZeroSeedLaunchInstallation,
}

/// Same-block observations `previewInstallation` reads besides its arguments.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ZeroSeedLaunchChainObservation {
    /// Whether `parameters.quoteToken` has code.
    pub quote_has_code: bool,
    /// Whether the predicted launch token address has code.
    pub predicted_token_has_code: bool,
}

/// `previewInstallation(controller, parameters)` of `extension` at block timestamp `now`, in the
/// contract's order: quote code, [`ZeroSeedLaunchParameters::validate`], token collision,
/// alignment and installation. `create` installs the same. Contract semantics only: NOT instance
/// or quote approval, and not an execution guarantee.
pub fn preview_installation(
    extension: Address,
    controller: Address,
    parameters: &ZeroSeedLaunchParameters,
    now: u64,
    observation: ZeroSeedLaunchChainObservation,
) -> Result<ZeroSeedLaunchPreview, ZeroSeedLaunchParameterError> {
    if !parameters.quote_token.is_zero() && !observation.quote_has_code {
        return Err(E::UnsupportedQuoteToken);
    }
    parameters.validate(now)?;
    if observation.predicted_token_has_code {
        return Err(E::LaunchTokenExists);
    }
    let token = launch_token_address(
        extension,
        controller,
        parameters.salt,
        parameters.name,
        parameters.symbol,
    );
    let token_is_token0 = token < parameters.quote_token;
    let range = ZeroSeedLaunchRange::from_requested(
        !token_is_token0,
        parameters.ask_tick,
        parameters.upper_tick,
    )?;
    let installation = install_supply(&range, parameters.supply)?;
    let (token0, token1) = if token_is_token0 {
        (token, parameters.quote_token)
    } else {
        (parameters.quote_token, token)
    };
    Ok(ZeroSeedLaunchPreview {
        token,
        pool_key: ZeroSeedLaunchPoolKey {
            token0,
            token1,
            config: PoolConfig {
                extension,
                fee: 0,
                pool_type_config: TickSpacing(range.tick_spacing),
            },
        },
        position_id: range.position_id(),
        installation,
    })
}

/// The installation `create` performs for `supply` in an installed `range`: the largest
/// liquidity whose rounded-up debit fits the supply, the exact debit and the sink. Refuses a
/// supply outside `1..=10**30` (`InvalidSupply`), `ZeroLiquidity` and `LiquidityAboveTickCap`.
pub fn install_supply(
    range: &ZeroSeedLaunchRange,
    supply: u128,
) -> Result<ZeroSeedLaunchInstallation, ZeroSeedLaunchParameterError> {
    validate_supply(supply)?;
    range.validate()?;
    let liquidity = max_liquidity_for_supply(range, supply)
        .min(U256::from(u128::MAX))
        .to::<u128>();
    if liquidity == 0 {
        return Err(E::ZeroLiquidity);
    }
    let cap = max_liquidity_per_tick(range.tick_spacing);
    if liquidity > cap {
        return Err(E::LiquidityAboveTickCap { liquidity, cap });
    }
    let (lower, upper) = range.sqrt_ratios();
    // Token-only: all token0 from the lower bound, or all token1 below the upper bound.
    let installed_supply = if range.launch_token_is_token1 {
        amount1_delta(lower, upper, liquidity, true)
    } else {
        amount0_delta(lower, upper, liquidity, true)
    }
    .map_err(|_| E::Overflow)?;
    let sink_supply = supply.checked_sub(installed_supply).ok_or(E::Overflow)?;
    let (tick_lower, tick_upper) = range.pool_bounds();
    Ok(ZeroSeedLaunchInstallation {
        range: *range,
        tick_lower,
        tick_upper,
        initial_tick: range.initial_tick(),
        liquidity,
        installed_supply,
        sink_supply,
    })
}

/// `_maxLiquidity`, unsaturated: `floor(S * lower * upper / (2**128 * (upper - lower)))` for a
/// token0 launch, `floor(S * 2**128 / (upper - lower))` for a token1 launch, over the fixed sqrt
/// ratios of a validated range.
///
/// Core takes `ceil(ceil(L * 2**128 * (upper - lower) / upper) / lower)` token0 for liquidity
/// `L`, and `ceil(ceil(n / u) / l) = ceil(n / (u * l))` for positive integers, so `debit(L) <= S`
/// exactly when `L` is at most this floor. The product is computed directly in 512 bits (the
/// contract factors the compact ratios instead; both are the same integer).
#[must_use]
pub fn max_liquidity_for_supply(range: &ZeroSeedLaunchRange, supply: u128) -> U256 {
    let (lower, upper) = range.sqrt_ratios();
    if range.launch_token_is_token1 {
        return (U256::from(supply) << 128) / (upper - lower);
    }
    let numerator = U512::from(supply) * U512::from(lower) * U512::from(upper);
    let denominator = U512::from(upper - lower) << 128;
    // Below 2**213 for every pair of valid ticks.
    U256::from(numerator / denominator)
}

/// Core's rounded-up launch-token debit for `liquidity` in a validated range, unbounded:
/// `ceil(ceil(L * 2**128 * (upper - lower) / upper) / lower)` (token0) or
/// `ceil(L * (upper - lower) / 2**128)` (token1). For supply envelopes, e.g. `debit(1)` is the
/// least installable supply.
#[must_use]
pub fn launch_token_debit(range: &ZeroSeedLaunchRange, liquidity: U256) -> U512 {
    let (lower, upper) = range.sqrt_ratios();
    let diff = U512::from(upper - lower);
    let liquidity = U512::from(liquidity);
    if range.launch_token_is_token1 {
        (liquidity * diff).div_ceil(U512::from(1) << 128)
    } else {
        let numerator: U512 = (liquidity << 128) * diff;
        numerator
            .div_ceil(U512::from(upper))
            .div_ceil(U512::from(lower))
    }
}

/// `concentratedMaxLiquidityPerTick` of the pool config:
/// `floor((2**128 - 1) / (1 + 2 * floor(88722835 / spacing)))`.
#[must_use]
pub fn max_liquidity_per_tick(tick_spacing: u32) -> u128 {
    let ticks = 1 + u128::from(Evm::max_tick() as u32 / tick_spacing) * 2;
    u128::MAX / ticks
}

// ---------------------------------------------------------------------------------------------
// Producer and claim checks
// ---------------------------------------------------------------------------------------------

/// The reference producer timing rule of the contract vectors, not a contract constraint:
/// `build_time + 300 <= trading_start <= build_time + 86400`,
/// `build_time < execution_expiry <= trading_start`, and at `now` (re-checked at build, use and
/// owner review): `build_time <= now < execution_expiry` and `now + 300 <= trading_start`.
pub fn validate_producer_timing(
    build_time: u64,
    execution_expiry: u64,
    trading_start: u64,
    now: u64,
) -> Result<(), ZeroSeedLaunchParameterError> {
    let min_start = build_time.checked_add(300).ok_or(E::Overflow)?;
    let max_start = build_time.checked_add(86400).ok_or(E::Overflow)?;
    let fresh_min = now.checked_add(300).ok_or(E::Overflow)?;
    if now < build_time
        || now >= execution_expiry
        || trading_start < min_start
        || trading_start > max_start
        || trading_start < fresh_min
        || execution_expiry <= build_time
        || execution_expiry > trading_start
    {
        return Err(E::InvalidProducerTiming);
    }
    Ok(())
}

/// One configured deployment of the extension and its periphery. The SDK lists none: callers
/// construct it from their own explicit configuration, bound to the same chain and block as the
/// pool state.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ZeroSeedLaunchInstance {
    pub chain_id: u64,
    pub core: Address,
    pub extension: Address,
    /// `ZeroSeedLaunchPeriphery` deployed for this extension: the controller of its launches.
    pub periphery: Address,
}

/// Mirrors the six `InvalidRecipient` refusals of `ZeroSeedLaunchPeriphery.claimFees`: zero,
/// Core, the extension, the periphery, token0 and token1. For a native quote the zero address is
/// also token0. Atomic full two-asset claim, not a per-side claim.
pub fn validate_claim_recipient(
    instance: &ZeroSeedLaunchInstance,
    key: &ZeroSeedLaunchPoolKey,
    recipient: Address,
) -> Result<(), ZeroSeedLaunchParameterError> {
    if key.config.extension != instance.extension {
        return Err(E::InstanceMismatch);
    }
    if recipient.is_zero()
        || recipient == instance.core
        || recipient == instance.extension
        || recipient == instance.periphery
        || recipient == key.token0
        || recipient == key.token1
    {
        return Err(E::InvalidRecipient);
    }
    Ok(())
}

/// How a launch's quote token settles.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ZeroSeedLaunchQuoteKind {
    /// Native ETH, `address(0)`: always token0, no code, no `decimals()` and no approvals.
    Native,
    /// An ERC-20 quote, bound to the keccak of its executed runtime.
    Erc20 { quote_runtime: U256 },
}

/// A reviewed ERC-20 quote of the caller's support policy: chain, address and keccak of its
/// executed runtime. The SDK reviews none.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ZeroSeedLaunchReviewedQuote {
    pub chain_id: u64,
    pub quote: Address,
    pub runtime: U256,
}

/// Observation of one launch's quote token (`LaunchParameters.quoteToken`), read at the same
/// block as the rest of the launch.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ZeroSeedLaunchQuoteObservation {
    pub chain_id: u64,
    pub quote: Address,
    /// Keccak of the code at `quote`, `None` when it has none (always for native ETH).
    pub quote_runtime: Option<U256>,
}

impl ZeroSeedLaunchQuoteObservation {
    /// The contract's own quote check: `UnsupportedQuoteToken` for a nonzero quote without code.
    pub fn validate_code(&self) -> Result<(), ZeroSeedLaunchParameterError> {
        if !self.quote.is_zero() && self.quote_runtime.is_none() {
            return Err(E::UnsupportedQuoteToken);
        }
        Ok(())
    }

    /// Quote support policy, separate from the contract: native ETH is always eligible; an
    /// ERC-20 only with an entry of `reviewed` for this chain, address and runtime.
    pub fn supported_kind(
        &self,
        reviewed: &[ZeroSeedLaunchReviewedQuote],
    ) -> Result<ZeroSeedLaunchQuoteKind, ZeroSeedLaunchParameterError> {
        self.validate_code()?;
        let Some(runtime) = self.quote_runtime else {
            return Ok(ZeroSeedLaunchQuoteKind::Native);
        };
        // A native quote never has code; an observation claiming one is inconsistent.
        let listed = !self.quote.is_zero()
            && reviewed.iter().any(|entry| {
                entry.chain_id == self.chain_id
                    && entry.quote == self.quote
                    && entry.runtime == runtime
            });
        if !listed {
            return Err(E::QuoteNotReviewed);
        }
        Ok(ZeroSeedLaunchQuoteKind::Erc20 {
            quote_runtime: runtime,
        })
    }
}

// ---------------------------------------------------------------------------------------------
// Pool
// ---------------------------------------------------------------------------------------------

/// Unique identifier for a [`ZeroSeedLaunchPool`]. The pool fee is 0 and the extension is the
/// `ZeroSeedLaunch` contract.
pub type ZeroSeedLaunchPoolKey =
    PoolKey<Address, <Evm as Chain>::Fee, ZeroSeedLaunchPoolTypeConfig>;
/// Pool configuration for a [`ZeroSeedLaunchPool`].
pub type ZeroSeedLaunchPoolConfig =
    PoolConfig<Address, <Evm as Chain>::Fee, ZeroSeedLaunchPoolTypeConfig>;
/// Type config for a [`ZeroSeedLaunchPool`], the tick spacing of the launch pool.
pub type ZeroSeedLaunchPoolTypeConfig = ConcentratedPoolTypeConfig;

/// The launch as `LaunchCreated` and `getLaunch` report it.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ZeroSeedLaunchConfig {
    /// `LaunchParameters.quoteToken`: the launch's own quote, the pool key's other token.
    pub quote_token: Address,
    /// The installed range: the pool key's spacing and the position's aligned bounds (or
    /// [`ZeroSeedLaunchRange::from_requested`] of the event's requested bounds), with the token
    /// order from the event's `token` and pool key.
    pub range: ZeroSeedLaunchRange,
    /// The event's `liquidity`, the constant liquidity of the launch position.
    pub liquidity: u128,
    /// `tradingStart`, `decayRateX32`, `initialFee` and `finalFee`.
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
    /// Gas estimate from in-test local fixture gas. Uncalibrated: see the constants.
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
    /// The pool key's extension is not the instance's, or the quote observation is of another
    /// chain or token.
    #[error("pool does not belong to the configured instance")]
    InstanceMismatch,
    /// The launch's quote is refused by the contract or not supported: see
    /// [`ZeroSeedLaunchQuoteObservation::supported_kind`].
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
    /// The forward reverts with `TradingNotStarted`: the block timestamp is before
    /// `tradingStart`.
    #[error("trading has not started")]
    TradingNotStarted,
    /// Not a valid `Core` sqrt ratio. Stricter than the contract, which ignores an invalid limit
    /// beyond the position bounds.
    #[error("invalid price limit")]
    InvalidSqrtRatioLimit,
    /// `Core` reverts with `SqrtRatioLimitWrongDirection`.
    #[error("price limit in the wrong direction")]
    SqrtRatioLimitWrongDirection,
    /// `AmountBeforeFeeOverflow`: the exact-output gross-up does not fit a `uint128`.
    #[error("amount before fee overflow")]
    AmountBeforeFeeOverflow,
    #[error("amount delta error")]
    AmountDelta(#[from] AmountDeltaError),
    /// A delta does not fit a signed 128-bit amount (`SafeCastLib.Overflow`); the contract
    /// reverts.
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
    /// Creates a launch pool of a configured instance: a pool key whose extension is not the
    /// instance's, or a quote observation of another chain or token, refuses it
    /// (`InstanceMismatch`), as does a quote that is not native ETH or listed in `reviewed`
    /// (`UnsupportedQuoteToken`).
    ///
    /// `key` is the pool key from `LaunchCreated`, `launch` the rest of that event, `state`
    /// `Core.poolState` of the pool and `quote` the observation of the launch's own quote token,
    /// all at the block being quoted.
    pub fn new(
        key: ZeroSeedLaunchPoolKey,
        launch: ZeroSeedLaunchConfig,
        state: ZeroSeedLaunchPoolState,
        instance: &ZeroSeedLaunchInstance,
        quote: &ZeroSeedLaunchQuoteObservation,
        reviewed: &[ZeroSeedLaunchReviewedQuote],
    ) -> Result<Self, ZeroSeedLaunchPoolConstructionError> {
        type CE = ZeroSeedLaunchPoolConstructionError;
        if key.config.extension != instance.extension
            || quote.chain_id != instance.chain_id
            || quote.quote != launch.quote_token
        {
            return Err(CE::InstanceMismatch);
        }
        if quote.supported_kind(reviewed).is_err() {
            return Err(CE::UnsupportedQuoteToken);
        }
        Self::new_math(key, launch, state)
    }

    /// Pure pool math, including synthetic quote arithmetic. This is NOT asset, quote or instance
    /// approval; service routing must use `new`, never this constructor.
    pub fn new_math(
        key: ZeroSeedLaunchPoolKey,
        launch: ZeroSeedLaunchConfig,
        state: ZeroSeedLaunchPoolState,
    ) -> Result<Self, ZeroSeedLaunchPoolConstructionError> {
        type CE = ZeroSeedLaunchPoolConstructionError;
        ensure_valid_token_order(&key)?;
        let PoolConfig {
            extension,
            fee,
            pool_type_config: TickSpacing(tick_spacing),
        } = key.config;
        if !fee.is_zero() {
            return Err(CE::FeeMustBeZero);
        }
        if extension.is_zero() {
            return Err(CE::MissingExtension);
        }
        // The pool key pairs the launch token with the launch's own quote. A native quote is
        // `address(0)` and so always token0; the launch token is a CREATE2 deployment and never
        // `address(0)`.
        let (launch_token, quote_token) = if launch.range.launch_token_is_token1 {
            (key.token1, key.token0)
        } else {
            (key.token0, key.token1)
        };
        let range = launch.range;
        if quote_token != launch.quote_token
            || launch_token.is_zero()
            || range.validate().is_err()
            || range.tick_spacing != tick_spacing
            || launch.liquidity == 0
            || launch.liquidity > max_liquidity_per_tick(tick_spacing)
            || !launch.fee.is_valid()
        {
            return Err(CE::InvalidLaunchConfig);
        }
        let (lower, upper) = range.pool_bounds();
        let (lower_sqrt_ratio, upper_sqrt_ratio) = range.sqrt_ratios();

        if state.sqrt_ratio < lower_sqrt_ratio
            || state.sqrt_ratio > upper_sqrt_ratio
            || Evm::adjust_sqrt_ratio_precision(state.sqrt_ratio) != state.sqrt_ratio
        {
            return Err(CE::InvalidSqrtRatio);
        }
        let in_range = state.tick >= lower && state.tick < upper;
        if state.liquidity != if in_range { launch.liquidity } else { 0 } {
            return Err(CE::ActiveLiquidityMismatch);
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

    /// Creator fee charged at block timestamp `timestamp`, Q0.64.
    #[must_use]
    pub fn fee_at(&self, timestamp: u64) -> u64 {
        self.launch.fee.fee_at(timestamp)
    }

    /// Simulates the forward `Core.forward(extension, abi.encode(poolKey, swapParameters))` at
    /// block timestamp `timestamp`. The extension clamps the limit to the installed bounds and
    /// sets skip-ahead 1, whatever the caller sends.
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
        type QE = ZeroSeedLaunchPoolQuoteError;
        if timestamp < self.launch.fee.trading_start {
            return Err(QE::TradingNotStarted);
        }
        let increasing = is_price_increasing(amount, is_token1);
        let limit = match sqrt_ratio_limit {
            Some(limit) => {
                if limit < Evm::min_sqrt_ratio()
                    || limit > Evm::max_sqrt_ratio()
                    || Evm::adjust_sqrt_ratio_precision(limit) != limit
                {
                    return Err(QE::InvalidSqrtRatioLimit);
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
            amount_before_fee::<Evm>(calculated_abs, fee_rate).ok_or(QE::AmountBeforeFeeOverflow)?
                - calculated_abs
        } else {
            compute_fee::<Evm>(calculated_abs, fee_rate)
        };
        let with_fee = calculated
            .checked_add(i128::try_from(fee_amount).map_err(|_| QE::Overflow)?)
            .ok_or(QE::Overflow)?;
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
    /// like a router swap that refuses partial fills and requires a positive minimum output.
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

    /// `Core.swap` on the launch pool with a zero pool fee and skip-ahead 1.
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
                find_next_initialized_tick(
                    &initialized,
                    pool.tick,
                    spacing,
                    ZERO_SEED_LAUNCH_SKIP_AHEAD,
                )
            } else {
                find_prev_initialized_tick(
                    &initialized,
                    pool.tick,
                    spacing,
                    ZERO_SEED_LAUNCH_SKIP_AHEAD,
                )
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
        // The creator fee depends on the block timestamp.
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
mod tests {
    use super::*;

    #[test]
    fn bitmap_search_matches_core_word_boundaries() {
        // Tick 0 is raw index 89_421_695 = 349_303 * 256 + 127 for every spacing.
        assert_eq!(find_next_initialized_tick(&[], 0, 100, 0), (12_800, false));
        assert_eq!(find_prev_initialized_tick(&[], 0, 100, 0), (-12_700, false));
        // Skip-ahead 1 searches one more word.
        assert_eq!(find_next_initialized_tick(&[], 0, 100, 1), (38_400, false));
        assert_eq!(find_prev_initialized_tick(&[], 0, 100, 1), (-38_300, false));
        assert_eq!(
            find_next_initialized_tick(&[(0, 1), (30_000, -1)], 0, 100, 1),
            (30_000, true)
        );
        assert_eq!(
            find_prev_initialized_tick(&[(-30_000, 1), (100, -1)], 99, 100, 1),
            (-30_000, true)
        );
        assert_eq!(
            find_next_initialized_tick(&[], Evm::max_tick() - 1, 1, 1),
            (Evm::max_tick(), false)
        );
        assert_eq!(
            find_prev_initialized_tick(&[], Evm::min_tick(), 1, 1),
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
    fn metadata_packing_is_canonical() {
        let zero_seed = pack_launch_metadata(b"Zero Seed").unwrap();
        assert_eq!(unpack_launch_metadata(&zero_seed), Some(&b"Zero Seed"[..]));
        let max = pack_launch_metadata(&[0xff; 31]).unwrap();
        assert!(is_canonical_launch_metadata(&max));
        assert_eq!(
            pack_launch_metadata(b""),
            Err(ZeroSeedLaunchParameterError::InvalidMetadata)
        );
        assert_eq!(
            pack_launch_metadata(&[b'a'; 32]),
            Err(ZeroSeedLaunchParameterError::InvalidMetadata)
        );
        // Embedded zero bytes are content.
        let nul = pack_launch_metadata(&[0, 0]).unwrap();
        assert_eq!(unpack_launch_metadata(&nul), Some(&[0u8, 0][..]));
        let mut dirty = zero_seed;
        dirty[31] = 1;
        assert!(!is_canonical_launch_metadata(&dirty));
        let mut long = [0u8; 32];
        long[0] = 32;
        assert!(!is_canonical_launch_metadata(&B256::from(long)));
        assert!(!is_canonical_launch_metadata(&B256::ZERO));
    }

    /// A native quote is `address(0)`, so a launch token ordered as token0 would be `address(0)`.
    #[test]
    fn native_quote_requires_launch_token1() {
        let range = ZeroSeedLaunchRange::from_requested(false, -13_815_500, -9_210_300).unwrap();
        let launch = |quote_token: &str| ZeroSeedLaunchConfig {
            quote_token: Address::from_str(quote_token).unwrap(),
            range,
            liquidity: 1_000_000,
            fee: ZeroSeedLaunchFeeSchedule {
                trading_start: 0,
                decay_rate_x32: ZERO_SEED_LAUNCH_DEFAULT_DECAY_RATE_X32,
                initial_fee: 0,
                final_fee: 0,
            },
        };
        let state = ZeroSeedLaunchPoolState {
            sqrt_ratio: to_sqrt_ratio::<Evm>(range.ask_tick).unwrap(),
            tick: range.ask_tick,
            liquidity: 1_000_000,
        };
        let key = |token0: &str, spacing: u32| ZeroSeedLaunchPoolKey {
            token0: Address::from_str(token0).unwrap(),
            token1: Address::from_str("0x00000000000000000000000000000000000f0000").unwrap(),
            config: PoolConfig {
                extension: Address::from_str("0x5100000000000000000000000000000000000000").unwrap(),
                fee: 0,
                pool_type_config: TickSpacing(spacing),
            },
        };
        let spacing = range.tick_spacing;
        assert!(
            ZeroSeedLaunchPool::new_math(
                key("0x0000000000000000000000000000000000000001", spacing),
                launch("0x00000000000000000000000000000000000f0000"),
                state
            )
            .is_ok()
        );
        for (token0, quote, spacing) in [
            (
                "0x0000000000000000000000000000000000000000",
                "0x00000000000000000000000000000000000f0000",
                spacing,
            ),
            // The pool key must pair the launch token with the launch's own quote.
            (
                "0x0000000000000000000000000000000000000001",
                "0x0000000000000000000000000000000000000002",
                spacing,
            ),
            // The key's spacing must be the derived spacing.
            (
                "0x0000000000000000000000000000000000000001",
                "0x00000000000000000000000000000000000f0000",
                100,
            ),
        ] {
            assert_eq!(
                ZeroSeedLaunchPool::new_math(key(token0, spacing), launch(quote), state),
                Err(ZeroSeedLaunchPoolConstructionError::InvalidLaunchConfig)
            );
        }
    }

    #[test]
    fn installed_ranges_are_validated() {
        let range = ZeroSeedLaunchRange::from_requested(true, -13_815_500, -9_210_300).unwrap();
        assert_eq!(
            (range.tick_spacing, range.ask_tick, range.upper_tick),
            (17_990, -13_798_330, -9_210_880)
        );
        assert_eq!(range.validate(), Ok(()));
        for bad in [
            ZeroSeedLaunchRange {
                ask_tick: range.ask_tick + 1,
                ..range
            },
            ZeroSeedLaunchRange {
                tick_spacing: 0,
                ..range
            },
            ZeroSeedLaunchRange {
                tick_spacing: ZERO_SEED_LAUNCH_MAX_TICK_SPACING + 1,
                ..range
            },
            ZeroSeedLaunchRange {
                upper_tick: range.ask_tick,
                ..range
            },
            // 257 steps.
            ZeroSeedLaunchRange {
                tick_spacing: 1,
                ask_tick: 0,
                upper_tick: 257,
                ..range
            },
        ] {
            assert_eq!(
                bad.validate(),
                Err(ZeroSeedLaunchParameterError::InvalidInstalledRange)
            );
        }
    }

    #[test]
    fn producer_timing_rule() {
        assert_eq!(validate_producer_timing(1_000, 1_200, 1_300, 1_000), Ok(()));
        for (build, expiry, start, now) in [
            (1_000, 1_200, 1_299, 1_000),
            (1_000, 1_200, 87_401, 1_000),
            (1_000, 1_301, 1_300, 1_000),
            (1_000, 1_200, 1_300, 999),
            (1_000, 1_200, 1_300, 1_200),
            (1_000, 1_000, 1_300, 1_000),
            (1_000, 1_200, 1_300, 1_001),
        ] {
            assert_eq!(
                validate_producer_timing(build, expiry, start, now),
                Err(ZeroSeedLaunchParameterError::InvalidProducerTiming)
            );
        }
    }
}
