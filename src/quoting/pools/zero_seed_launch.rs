//! Quoting and installation math for pools of the `ZeroSeedLaunch` extension.
//!
//! A zero-seed launch mints a fixed requested supply and installs the largest liquidity it buys,
//! in one transaction, as a single token-only concentrated position from the ask price up to an
//! upper bound, with no quote seed. The rounding remainder of the requested supply, the sink
//! supply, is minted directly to `address(0)`, so the token's `totalSupply` is exactly the
//! requested supply. The pool fee is 0. The pool, the position and its liquidity never change
//! after creation: only swaps forwarded through the extension (`Core.forward` with
//! `abi.encode(PoolKey, SwapParameters)`) move the price, and every swap's price limit is clamped
//! to the position bounds. Time only lowers the creator fee from `initial_fee` at `trading_start`,
//! by the fee model of the deployment ([`ZeroSeedLaunchFeeModel`]):
//!
//! - [`ZeroSeedLaunchFeeModel::FixedBaseDurationV1`] (`evm-contracts@43d6628`, `uint32
//!   feeDuration`): the fixed 600 second half-life exponential of [`decay_q128`], rescaled to reach
//!   `final_fee` exactly after `fee_duration`.
//! - [`ZeroSeedLaunchFeeModel::TickRateV2`] (`evm-contracts@3d6378f`, `uint64 decayRateX32`): the
//!   excess over the long-run floor `final_fee` shrinks by `tickToSqrtRatio(-m)` with
//!   `m = floor(decayRateX32 * elapsed / 2**32)`; see [`tick_rate_decayed_fee`]. `final_fee` is
//!   approached, not scheduled.
//!
//! The creator fee is charged on the calculated side of the actual fill and saved separately from
//! the position.
//!
//! One extension deployment serves every quote: each launch selects its own quote token in
//! `LaunchParameters.quoteToken`, native ETH (`address(0)`, always token0, so the launch token is
//! token1) or an ERC-20. Launches are created through `ZeroSeedLaunchPeriphery`, which is the
//! launch controller, records the transferable owner and namespaces the token salt by owner; see
//! [`periphery_launch_token_address`].
//!
//! The model mirrors `ZeroSeedLaunch.handleForwardData` and the `Core` swap loop step by step,
//! including the tick bitmap word boundaries a swap with `skipAhead` 0 stops at, so it reproduces
//! the contract's deltas, creator fee and post-swap `Core` state exactly. The installation
//! functions mirror `previewInstallation`, which `create` runs on the same inputs.
//!
//! Targets: `EkuboProtocol/evm-contracts@43d6628841b3ce91dafa048b7ceef64bed55fc8e` (forward-only
//! extension with a per-launch quote, requested supply with an `address(0)` sink, fixed-base fee
//! table, full `uint64` creator-fee range, separate periphery) and
//! `EkuboProtocol/evm-contracts@3d6378f585591dc7eabeea6976932c30524bb8ea` (the same with the
//! per-launch tick-rate fee decay), against the Q0.64-fee `Core` of those commits. Not the Q0.16
//! `next` Core.

use core::str::FromStr;
use derive_more::{Add, AddAssign, Sub, SubAssign};
use num_traits::Zero;
use ruint::aliases::{U256, U512};
use thiserror::Error;

use crate::{
    alloy_primitives::{B256, Keccak256},
    chain::{
        Chain,
        evm::{EVM_MAX_TICK_SPACING, Evm},
    },
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

/// Offline observation of one extension deployment from the LOCAL harness, never a live provider
/// attestation: the chain, `Core`, the extension and its periphery with their executed runtimes.
/// An instance has no quote; every launch selects its own (see
/// [`ZeroSeedLaunchQuoteObservation`]). Callers must bind these values to the same executed
/// instance/block as the pool state.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ZeroSeedLaunchInstance {
    pub chain_id: u64,
    pub extension: Address,
    /// Keccak of the extension's executed runtime (immutable `CORE` filled in).
    pub extension_runtime: U256,
    /// `ZeroSeedLaunchPeriphery` deployed for this extension: the launch controller.
    pub periphery: Address,
    /// Keccak of the periphery's executed runtime (immutables `CORE` and `LAUNCH` filled in).
    pub periphery_runtime: U256,
    pub core: Address,
    pub core_runtime: U256,
    /// The fee math and `LaunchParameters`/`LaunchCreated` shape of the deployment's contract
    /// revision. Bound to the deployment, never inferred from an event.
    pub fee_model: ZeroSeedLaunchFeeModel,
}

/// A supported LOCAL instance: a constructor-executed fixture of the indexer's anvil chain (chain
/// 31337, no fork) at one target commit.
struct LocalInstancePin {
    fee_model: ZeroSeedLaunchFeeModel,
    extension: &'static str,
    extension_runtime: &'static str,
    periphery: &'static str,
    periphery_runtime: &'static str,
}

const LOCAL_CHAIN_ID: u64 = 31337;
const LOCAL_CORE: &str = "0x00000000000014aa86c5d3c41765bb24e11bd701";
const LOCAL_CORE_RUNTIME: &str =
    "0xc5f90c9d0dbc5037f8f9e248f4bb292e7c1824f584eb6550cb4cad525b38c71a";

/// `pins.localFixture` of `evm-contracts@43d6628` and of `evm-contracts@3d6378f`.
const LOCAL_INSTANCES: [LocalInstancePin; 2] = [
    LocalInstancePin {
        fee_model: ZeroSeedLaunchFeeModel::FixedBaseDurationV1,
        extension: "0x519c5f793d3f6cf9ee439e4cc38d8285cf08211f",
        extension_runtime: "0xd6b4c7ce8da56e9948fdb004a035d9b52dbd3690bcb03c1269bbf2a9981d8ed5",
        periphery: "0x0df4e2a76640b52e51479b435f52d0eb0e7e8ef4",
        periphery_runtime: "0x2a9329dbb064a2c031115c7c120c8b6a1f31de167f33374180e4dc73d975974b",
    },
    LocalInstancePin {
        fee_model: ZeroSeedLaunchFeeModel::TickRateV2,
        extension: "0x5135fd3e9a6056937eaf6b99454bbc2198c2263d",
        extension_runtime: "0xe08ad382497fc9825956c2b4e9ccf463014c4ed65baf50c0a59db8d7b7aedfc3",
        periphery: "0xfb2e7927d3e4984dca3e390526d43c6f5a3461e9",
        periphery_runtime: "0xf72d3cd6b99e1b64f0b08c0f6933b4f8adb92464ded48c51bfb7d2805c09d667",
    },
];

/// A reviewed ERC-20 quote: chain, address and keccak of its executed runtime.
struct ReviewedQuote {
    chain_id: u64,
    quote: &'static str,
    runtime: &'static str,
}

/// Reviewed ERC-20 quotes of live networks: none.
const LIVE_REVIEWED_QUOTES: [ReviewedQuote; 0] = [];

/// The LOCAL fixture's plain 18-decimal test ERC-20 (`test/TestToken.sol`) at the top of the
/// address space, `pins.localQuotes`. Local evidence only.
const LOCAL_FIXTURE_QUOTES: [ReviewedQuote; 1] = [ReviewedQuote {
    chain_id: LOCAL_CHAIN_ID,
    quote: "0xffffffffffffffffffffffffffffffffffffffff",
    runtime: "0xe8ccd7c4eb891208d5e04a27a31dfaf2b9bce01e083d7b36f10b6dd6ea643e63",
}];

fn static_address(s: &str) -> Address {
    Address::from_str(s).expect("static pin address")
}

fn static_hash(s: &str) -> U256 {
    U256::from_str(s).expect("static pin hash")
}

impl ZeroSeedLaunchInstance {
    /// Fail closed against the constructor-executed LOCAL fixture instances, including their fee
    /// model. There are NO approved live entries.
    pub fn validate(&self) -> Result<(), ZeroSeedLaunchParameterError> {
        let pinned = LOCAL_INSTANCES.iter().any(|pin| {
            self.chain_id == LOCAL_CHAIN_ID
                && self.fee_model == pin.fee_model
                && self.extension == static_address(pin.extension)
                && self.extension_runtime == static_hash(pin.extension_runtime)
                && self.periphery == static_address(pin.periphery)
                && self.periphery_runtime == static_hash(pin.periphery_runtime)
                && self.core == static_address(LOCAL_CORE)
                && self.core_runtime == static_hash(LOCAL_CORE_RUNTIME)
        });
        if !pinned {
            return Err(ZeroSeedLaunchParameterError::UnsupportedInstance);
        }
        Ok(())
    }
}

/// How a launch's quote token settles.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ZeroSeedLaunchQuoteKind {
    /// Native ETH, `address(0)`: always token0, no code, no `decimals()` and no approvals.
    Native,
    /// An ERC-20 quote, bound to the keccak of its executed runtime.
    Erc20 { quote_runtime: U256 },
}

/// Offline observation of one launch's quote token (`LaunchParameters.quoteToken`), read at the
/// same block as the rest of the launch. Not an RPC read or a live attestation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ZeroSeedLaunchQuoteObservation {
    pub chain_id: u64,
    pub quote: Address,
    /// Keccak of the code at `quote`, `None` when it has none (always for native ETH).
    pub quote_runtime: Option<U256>,
}

impl ZeroSeedLaunchQuoteObservation {
    /// The contract's own quote check: `UnsupportedQuoteToken` for a nonzero quote without code.
    /// It screens nothing else.
    pub fn validate_code(&self) -> Result<(), ZeroSeedLaunchParameterError> {
        if !self.quote.is_zero() && self.quote_runtime.is_none() {
            return Err(ZeroSeedLaunchParameterError::UnsupportedQuoteToken);
        }
        Ok(())
    }

    /// Quote support policy, separate from instance support and from the contract: native ETH is
    /// always eligible; an ERC-20 only with a reviewed `(chain, address, runtime keccak)` entry.
    /// The live list is empty; only the LOCAL fixture's test ERC-20 is listed.
    pub fn supported_kind(&self) -> Result<ZeroSeedLaunchQuoteKind, ZeroSeedLaunchParameterError> {
        self.validate_code()?;
        let Some(runtime) = self.quote_runtime else {
            return Ok(ZeroSeedLaunchQuoteKind::Native);
        };
        // A native quote never has code; an observation claiming one is inconsistent.
        let reviewed = !self.quote.is_zero()
            && LIVE_REVIEWED_QUOTES
                .iter()
                .chain(LOCAL_FIXTURE_QUOTES.iter())
                .any(|entry| {
                    entry.chain_id == self.chain_id
                        && static_address(entry.quote) == self.quote
                        && static_hash(entry.runtime) == runtime
                });
        if !reviewed {
            return Err(ZeroSeedLaunchParameterError::QuoteNotReviewed);
        }
        Ok(ZeroSeedLaunchQuoteKind::Erc20 {
            quote_runtime: runtime,
        })
    }
}

/// Finite LOCAL producer/decoder context, separate from pure `fee_at` and pool math.
/// Integer types express the unsigned domains; every addition is checked.
#[derive(Clone, Copy, Debug)]
pub struct ZeroSeedLaunchLocalPreview<'a> {
    pub instance: &'a ZeroSeedLaunchInstance,
    /// The account that calls `periphery.create`, and so the initial launch owner.
    pub owner: Address,
    /// `LaunchParameters.salt` as passed to the periphery, before owner namespacing.
    pub salt: B256,
    pub name: &'a str,
    pub symbol: &'a str,
    pub decimals: u8,
    /// Observed keccak of the code at `parameters.quote_token`, `None` without code (same local
    /// snapshot).
    pub quote_runtime: Option<U256>,
    /// Observed code presence at the predicted token address (same local snapshot).
    pub predicted_token_has_code: bool,
    pub build_time: u64,
    pub execution_expiry: u64,
}

impl ZeroSeedLaunchLocalPreview<'_> {
    /// The launch token address `periphery.create` deploys for this owner, salt and metadata. It
    /// does not depend on the quote.
    #[must_use]
    pub fn predicted_token(&self) -> Address {
        periphery_launch_token_address(
            self.instance.extension,
            self.instance.periphery,
            self.owner,
            self.salt,
            self.name,
            self.symbol,
            self.decimals,
        )
    }

    /// The observation of the launch's quote for `parameters`.
    #[must_use]
    pub fn quote(&self, parameters: &ZeroSeedLaunchParameters) -> ZeroSeedLaunchQuoteObservation {
        ZeroSeedLaunchQuoteObservation {
            chain_id: self.instance.chain_id,
            quote: parameters.quote_token,
            quote_runtime: self.quote_runtime,
        }
    }

    /// `previewInstallation` of the periphery for this owner, salt and metadata, which `create`
    /// runs on the same inputs, in the contract's order: quote code, metadata, scalar parameters,
    /// token collision, then the SDK's token order check, bound alignment and the installation.
    /// Contract semantics only: NOT supported-instance, quote-support or timing approval, and
    /// usable with any observed instance.
    pub fn contract_preview(
        &self,
        parameters: &ZeroSeedLaunchParameters,
        now: u64,
    ) -> Result<ZeroSeedLaunchInstallation, ZeroSeedLaunchParameterError> {
        self.validate_fee_model(parameters)?;
        self.quote(parameters).validate_code()?;
        self.validate_metadata()?;
        validate_scalar_parameters(parameters, now)?;
        self.validate_token(parameters)?;
        validate_bounds_alignment(&parameters.range)?;
        install_requested(parameters)
    }

    /// The parameters must have the `LaunchParameters` shape of the instance's contract revision:
    /// a `feeDuration` for v1, a `decayRateX32` for v2.
    fn validate_fee_model(
        &self,
        parameters: &ZeroSeedLaunchParameters,
    ) -> Result<(), ZeroSeedLaunchParameterError> {
        if parameters.fee.decay.model() != self.instance.fee_model {
            return Err(ZeroSeedLaunchParameterError::FeeModelMismatch);
        }
        Ok(())
    }

    fn validate_metadata(&self) -> Result<(), ZeroSeedLaunchParameterError> {
        if self.name.len() > 31 || self.symbol.len() > 31 {
            return Err(ZeroSeedLaunchParameterError::MetadataTooLong);
        }
        Ok(())
    }

    fn validate_token(
        &self,
        parameters: &ZeroSeedLaunchParameters,
    ) -> Result<(), ZeroSeedLaunchParameterError> {
        if self.predicted_token_has_code {
            return Err(ZeroSeedLaunchParameterError::LaunchTokenExists);
        }
        // The launch token is token1 exactly when the launch's own quote sorts below it; a native
        // quote always does.
        if parameters.range.launch_token_is_token1
            != (parameters.quote_token < self.predicted_token())
        {
            return Err(ZeroSeedLaunchParameterError::TokenOrderMismatch);
        }
        Ok(())
    }

    /// Re-run at build, use and owner review with fresh `now`; never rewrite signed start or
    /// requested supply. Checks the supported instance, the contract's quote, metadata and token
    /// checks, quote support and the LOCAL timing rule.
    pub fn validate(
        &self,
        parameters: &ZeroSeedLaunchParameters,
        now: u64,
    ) -> Result<(), ZeroSeedLaunchParameterError> {
        type E = ZeroSeedLaunchParameterError;
        self.instance.validate()?;
        self.validate_fee_model(parameters)?;
        let quote = self.quote(parameters);
        quote.validate_code()?;
        self.validate_metadata()?;
        self.validate_token(parameters)?;
        quote.supported_kind()?;
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

/// The installation `create` performs for these parameters, for display: computed liquidity,
/// installed supply and sink supply. Submit `parameters` unchanged, with the requested supply;
/// creation recomputes the same values from the same inputs. Rechecks fresh local context. Not
/// calldata, an execution guarantee or live authorization.
pub fn preview_installation(
    parameters: &ZeroSeedLaunchParameters,
    now: u64,
    context: &ZeroSeedLaunchLocalPreview<'_>,
) -> Result<ZeroSeedLaunchInstallation, ZeroSeedLaunchParameterError> {
    context.validate(parameters, now)?;
    preview_installation_math(parameters, now)
}

/// Mirrors the six `InvalidRecipient` refusals of `ZeroSeedLaunchPeriphery.claimFees`: zero,
/// Core, the extension, the periphery, token0 and token1. For a native quote the zero address is
/// also token0. Atomic full two-asset claim, not a per-side claim. Any quote of the instance's
/// launches is accepted here; quote support is checked per launch.
pub fn validate_claim_recipient(
    instance: &ZeroSeedLaunchInstance,
    key: &ZeroSeedLaunchPoolKey,
    recipient: Address,
) -> Result<(), ZeroSeedLaunchParameterError> {
    instance.validate()?;
    if key.config.extension != instance.extension {
        return Err(ZeroSeedLaunchParameterError::UnsupportedInstance);
    }
    if recipient.is_zero()
        || recipient == instance.core
        || recipient == instance.extension
        || recipient == instance.periphery
        || recipient == key.token0
        || recipient == key.token1
    {
        return Err(ZeroSeedLaunchParameterError::InvalidRecipient);
    }
    Ok(())
}

/// Creation code of `MintableERC20` at the target, without constructor arguments.
pub static MINTABLE_ERC20_CREATION_CODE: [u8; 4419] =
    decode_hex(include_str!("zero_seed_launch/MintableERC20.creation.hex"));

/// Keccak of [`MINTABLE_ERC20_CREATION_CODE`].
pub const MINTABLE_ERC20_CREATION_CODE_KECCAK: &str =
    "0x25da7fd323fdbf874dde8aaef1bce445ec035022d8518cb3046f65a0427a2f52";

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

fn address_word(address: Address) -> [u8; 32] {
    let mut word = [0u8; 32];
    word[12..].copy_from_slice(address.as_slice());
    word
}

fn usize_word(value: usize) -> [u8; 32] {
    let mut word = [0u8; 32];
    word[24..].copy_from_slice(&(value as u64).to_be_bytes());
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
/// user_salt))`.
#[must_use]
pub fn periphery_launch_salt(owner: Address, user_salt: B256) -> B256 {
    keccak_address_salt(owner, user_salt)
}

/// The CREATE2 salt of a launch token: `keccak256(abi.encode(controller, salt))`, with `salt` the
/// extension-level `LaunchParameters.salt` (for the periphery, [`periphery_launch_salt`]).
#[must_use]
pub fn extension_token_salt(controller: Address, salt: B256) -> B256 {
    keccak_address_salt(controller, salt)
}

/// `keccak256(MintableERC20.creationCode ++ abi.encode(extension, name, symbol, decimals))`.
#[must_use]
pub fn launch_token_init_code_hash(
    extension: Address,
    name: &str,
    symbol: &str,
    decimals: u8,
) -> B256 {
    let padded = |len: usize| len.div_ceil(32) * 32;
    let mut hasher = Keccak256::new();
    hasher.update(&MINTABLE_ERC20_CREATION_CODE[..]);
    hasher.update(address_word(extension));
    hasher.update(usize_word(4 * 32));
    hasher.update(usize_word(4 * 32 + 32 + padded(name.len())));
    let mut decimals_word = [0u8; 32];
    decimals_word[31] = decimals;
    hasher.update(decimals_word);
    for text in [name, symbol] {
        hasher.update(usize_word(text.len()));
        hasher.update(text.as_bytes());
        hasher.update(&[0u8; 32][..padded(text.len()) - text.len()]);
    }
    hasher.finalize()
}

/// The launch token `extension` deploys for a creation forwarded by `controller` with the
/// extension-level `salt`: `CREATE2(extension, extension_token_salt(controller, salt),
/// launch_token_init_code_hash(..))`.
#[must_use]
pub fn launch_token_address(
    extension: Address,
    controller: Address,
    salt: B256,
    name: &str,
    symbol: &str,
    decimals: u8,
) -> Address {
    let mut hasher = Keccak256::new();
    hasher.update([0xff]);
    hasher.update(extension.as_slice());
    hasher.update(extension_token_salt(controller, salt).as_slice());
    hasher.update(launch_token_init_code_hash(extension, name, symbol, decimals).as_slice());
    Address::from_slice(&hasher.finalize()[12..])
}

/// The launch token `periphery.create` deploys when `owner` calls it with `user_salt`.
#[must_use]
pub fn periphery_launch_token_address(
    extension: Address,
    periphery: Address,
    owner: Address,
    user_salt: B256,
    name: &str,
    symbol: &str,
    decimals: u8,
) -> Address {
    launch_token_address(
        extension,
        periphery,
        periphery_launch_salt(owner, user_salt),
        name,
        symbol,
        decimals,
    )
}

/// Highest creator fee rate, Q0.64: `type(uint64).max = 2**64 - 1`, just under 100%, never
/// exactly 100%. The contract accepts every `uint64` initial and final fee and checks only the
/// schedule shape; exactly 100% (`2**64`) is not encodable. A bound of the type, not a suggested
/// rate.
pub const ZERO_SEED_LAUNCH_MAX_CREATOR_FEE: u64 = u64::MAX;

/// `skipAhead` of the forwarded swaps this model quotes, as the contract tests' lockers and
/// `LaunchTestRouter` send them.
const SKIP_AHEAD: u32 = 0;

/// Offset `Core` adds to compressed ticks to index its tick bitmaps.
const TICK_BITMAP_STORAGE_OFFSET: i64 = 89_421_695;

const TWO_POW_128: U256 = U256::from_limbs([0, 0, 1, 0]);

// Gas estimates fitted to the in-test gas of the forwarded swap frame (test locker
// `forwardSwap`, token settlement included) of the parity vectors generated at
// `EkuboProtocol/evm-contracts@d6aeb58d845aa29454f3ed8df15e84a306a6f26d`, not refitted since.
// Against the parity vectors regenerated at the target (fixed-base fee table, native ETH settled
// by value, plain 18- and six-decimal ERC-20 quotes, test locker frame) the estimate's error on the
// 370 fills that are not a launch's first fill or a known zero-slot write is -39.5% to +26.8%
// (mean +1.5%). They exclude
// the 21,000 transaction base, calldata, the router and any account abstraction overhead. A swap
// that writes a zero storage slot, such as the first creator fee after a claim or the first launch
// tokens a holder receives, costs about 20,000 more per slot, which the pool state cannot predict;
// the first swap of a launch costs about 50,000-70,000 more. Calibrate against execution before
// relying on them.

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

/// 2**64: the Q0.64 unit, exactly 100%. Not encodable as a `u64` fee.
pub const ZERO_SEED_LAUNCH_Q64: u128 = 1 << 64;

/// `round(2**128 * 2**(-2**i / 600))` for bit `i` of the elapsed seconds: the fixed-base Q128
/// table of `math/feeDecay.sol`, a 600 second half-life. Only nonzero constants exist.
pub const ZERO_SEED_LAUNCH_DECAY_TABLE_Q128: [u128; 17] = [
    339_889_484_297_159_900_493_648_602_831_395_569_057,
    339_497_055_287_118_257_930_533_248_299_650_400_736,
    338_713_556_013_920_184_336_129_943_844_147_573_651,
    337_151_977_828_609_613_753_562_640_265_082_287_810,
    334_050_386_396_171_404_885_545_237_344_599_070_716,
    327_932_539_264_834_336_949_184_815_807_600_758_235,
    316_030_922_441_737_935_988_095_136_387_330_274_498,
    293_507_844_215_098_455_952_964_317_090_465_751_204,
    253_162_852_354_938_356_992_240_649_094_357_060_196,
    188_347_784_201_757_897_225_807_540_435_664_088_841,
    104_251_325_552_682_051_605_813_724_741_512_712_010,
    31_939_177_389_160_626_453_527_783_486_618_815_759,
    2_997_836_947_964_109_484_105_344_435_429_137_776,
    26_410_496_811_510_722_015_611_852_309_540_293,
    2_049_810_421_099_131_403_277_778_219_901,
    12_347_753_427_443_481_862_030,
    448_060,
];

/// Elapsed seconds from which [`decay_q128`] is exactly 0: `2**17`, one past the table. Without
/// the cutoff higher bits would alias to their low 17 bits.
pub const ZERO_SEED_LAUNCH_DECAY_ZERO_FROM: u64 = 1 << 17;

/// `decayQ128` from `math/feeDecay.sol`: `2**(-elapsed / 600)` in Q128.
///
/// 0 from [`ZERO_SEED_LAUNCH_DECAY_ZERO_FROM`] on; otherwise start at 2**128 and, for every set
/// bit `i` of `elapsed` in ascending order, multiply by `ZERO_SEED_LAUNCH_DECAY_TABLE_Q128[i]`
/// and floor to Q128. The operation order is normative. The running value is at most 2**128 and
/// every constant is below it, so each product fits 256 bits. Non-increasing in `elapsed`.
#[must_use]
pub fn decay_q128(elapsed: u64) -> U256 {
    if elapsed >= ZERO_SEED_LAUNCH_DECAY_ZERO_FROM {
        return U256::ZERO;
    }
    let mut result = TWO_POW_128;
    for (bit, constant) in ZERO_SEED_LAUNCH_DECAY_TABLE_Q128.iter().enumerate() {
        if (elapsed >> bit) & 1 != 0 {
            result = (result * U256::from(*constant)) >> 128;
        }
    }
    result
}

/// The fee math and ABI shape of a `ZeroSeedLaunch` contract revision. A property of the
/// deployment ([`ZeroSeedLaunchInstance::fee_model`]): a deployment keeps its model forever.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(rename_all = "snake_case"))]
pub enum ZeroSeedLaunchFeeModel {
    /// `evm-contracts@43d6628`: `uint32 feeDuration`, the fixed-base table of [`decayed_fee`].
    /// `LaunchCreated` topic `0x3a4e8111…098f`, `create` `0x662af306`.
    #[cfg_attr(feature = "serde", serde(rename = "fixed_base_duration_v1"))]
    FixedBaseDurationV1,
    /// `evm-contracts@3d6378f`: `uint64 decayRateX32`, the tick-rate decay of
    /// [`tick_rate_decayed_fee`]. `LaunchCreated` topic `0x8f81ce1b…5888`, `create` `0xf91810d2`.
    #[cfg_attr(feature = "serde", serde(rename = "tick_rate_v2"))]
    TickRateV2,
}

/// The decay parameter of a launch, the 10th field of `LaunchParameters` and 3rd of `Launch`. Its
/// variant must be the fee model of the launch's deployment.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(tag = "model"))]
pub enum ZeroSeedLaunchFeeDecay {
    /// [`ZeroSeedLaunchFeeModel::FixedBaseDurationV1`]: seconds from `trading_start` to
    /// `final_fee`. Not zero.
    #[cfg_attr(feature = "serde", serde(rename = "fixed_base_duration_v1"))]
    FixedBaseDuration { fee_duration: u32 },
    /// [`ZeroSeedLaunchFeeModel::TickRateV2`]: unsigned Q32.32 ticks per second (`2**32` is one
    /// tick per second). Every value is valid; 0 keeps the fee flat at `initial_fee`.
    #[cfg_attr(feature = "serde", serde(rename = "tick_rate_v2"))]
    TickRate { decay_rate_x32: u64 },
}

impl ZeroSeedLaunchFeeDecay {
    /// The fee model whose `LaunchParameters` carry this parameter.
    #[must_use]
    pub fn model(&self) -> ZeroSeedLaunchFeeModel {
        match self {
            Self::FixedBaseDuration { .. } => ZeroSeedLaunchFeeModel::FixedBaseDurationV1,
            Self::TickRate { .. } => ZeroSeedLaunchFeeModel::TickRateV2,
        }
    }
}

/// Creator fee schedule, as in `LaunchParameters`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ZeroSeedLaunchFeeSchedule {
    /// First timestamp at which swaps are accepted; the decay starts here.
    pub trading_start: u64,
    /// `feeDuration` (v1) or `decayRateX32` (v2).
    #[cfg_attr(feature = "serde", serde(flatten))]
    pub decay: ZeroSeedLaunchFeeDecay,
    /// Creator fee until `trading_start`, Q0.64.
    pub initial_fee: u64,
    /// Q0.64. v1: the creator fee from `trading_start + fee_duration` on. v2: the long-run floor
    /// the fee approaches, reached only by rounding or saturation.
    pub final_fee: u64,
}

impl ZeroSeedLaunchFeeSchedule {
    /// `feeAt`: the creator fee at `timestamp`, Q0.64.
    ///
    /// `initial_fee` until `trading_start` (inclusive), then [`decayed_fee`] (v1) or
    /// [`tick_rate_decayed_fee`] (v2) of the elapsed seconds. Elapsed time is not narrowed, as in
    /// the contract.
    #[must_use]
    pub fn fee_at(&self, timestamp: u64) -> u64 {
        if timestamp <= self.trading_start {
            return self.initial_fee;
        }
        let elapsed = timestamp - self.trading_start;
        match self.decay {
            ZeroSeedLaunchFeeDecay::FixedBaseDuration { fee_duration } => {
                decayed_fee(self.initial_fee, self.final_fee, fee_duration, elapsed)
            }
            ZeroSeedLaunchFeeDecay::TickRate { decay_rate_x32 } => {
                tick_rate_decayed_fee(self.initial_fee, self.final_fee, decay_rate_x32, elapsed)
            }
        }
    }

    /// `feeDuration` of a v1 schedule.
    #[must_use]
    pub fn fee_duration(&self) -> Option<u32> {
        match self.decay {
            ZeroSeedLaunchFeeDecay::FixedBaseDuration { fee_duration } => Some(fee_duration),
            ZeroSeedLaunchFeeDecay::TickRate { .. } => None,
        }
    }

    /// `decayRateX32` of a v2 schedule.
    #[must_use]
    pub fn decay_rate_x32(&self) -> Option<u64> {
        match self.decay {
            ZeroSeedLaunchFeeDecay::FixedBaseDuration { .. } => None,
            ZeroSeedLaunchFeeDecay::TickRate { decay_rate_x32 } => Some(decay_rate_x32),
        }
    }

    /// `InvalidFeeSchedule` of the schedule's model: `final_fee > initial_fee`, and for v1 also a
    /// zero duration. A v2 rate of 0 is valid.
    #[must_use]
    pub fn is_valid(&self) -> bool {
        self.final_fee <= self.initial_fee
            && !matches!(
                self.decay,
                ZeroSeedLaunchFeeDecay::FixedBaseDuration { fee_duration: 0 }
            )
    }
}

/// Largest tick magnitude the EVM tick helper supports, `MAX_TICK_MAGNITUDE` of the contracts.
pub const ZERO_SEED_LAUNCH_MAX_TICK_MAGNITUDE: u64 = 88_722_835;

/// `MAX_DECAY_PRODUCT` of `math/feeDecay.sol` (v2): `(MAX_TICK_MAGNITUDE + 1) * 2**32 - 1`, the
/// largest `decayRateX32 * elapsed` whose magnitude the tick helper supports.
pub const ZERO_SEED_LAUNCH_MAX_DECAY_PRODUCT: u64 =
    ((ZERO_SEED_LAUNCH_MAX_TICK_MAGNITUDE + 1) << 32) - 1;

/// Consumer default `decayRateX32` (v2): a one-day half-life of the excess over the floor,
/// [`decay_rate_x32_for_half_life`] of 86400. A creation parameter choice, not a contract
/// constant.
pub const ZERO_SEED_LAUNCH_DEFAULT_DECAY_RATE_X32: u64 = 68_913_100_933;

/// `floor(2 * ln 2 / ln 1.000001 * 2**32 * 10**30)`: ticks per half-life of the excess, Q32.32,
/// scaled by `10**30`. The normative integer for every half-life conversion; never use a float.
pub const ZERO_SEED_LAUNCH_HALF_LIFE_X32_E30: &str =
    "5954091920683119788732747343471285361579197626";

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

/// The half-life of the excess for `decay_rate_x32`, in whole microseconds, floored:
/// `floor(HALF_LIFE_X32_E30 * 10**6 / (decay_rate_x32 * 10**30))`. `None` for rate 0 (no decay).
/// Display only: the fee follows [`tick_rate_decayed_fee`], not this value.
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

/// The last elapsed second at which the v2 curve is still evaluated:
/// `floor(MAX_DECAY_PRODUCT / decay_rate_x32)`. From the next second the fee is exactly
/// `final_fee` by numerical saturation; this is not a schedule end. `None` for rate 0.
#[must_use]
pub fn saturation_elapsed_seconds(decay_rate_x32: u64) -> Option<u64> {
    (decay_rate_x32 != 0).then(|| ZERO_SEED_LAUNCH_MAX_DECAY_PRODUCT / decay_rate_x32)
}

/// `toFixed(tickToSqrtRatio(-magnitude))` of the contracts: the compact (94-bit mantissa, rounded
/// down) sqrt ratio as 64.128 fixed point, at most `2**128`. `None` above
/// [`ZERO_SEED_LAUNCH_MAX_TICK_MAGNITUDE`], where the helper reverts `InvalidTick`.
#[must_use]
pub fn tick_rate_factor_q128(magnitude: u64) -> Option<U256> {
    if magnitude > ZERO_SEED_LAUNCH_MAX_TICK_MAGNITUDE {
        return None;
    }
    to_sqrt_ratio::<Evm>(-(magnitude as i32))
}

/// `decayedFee` from `math/feeDecay.sol` at `evm-contracts@3d6378f` (v2), in its normative order:
/// rate 0 is `initial_fee`; `elapsed > MAX_DECAY_PRODUCT / rate` (integer division, before any
/// multiply) is `final_fee`; else `m = (rate * elapsed) >> 32` and
/// `final_fee + floor((initial_fee - final_fee) * tick_rate_factor_q128(m) / 2**128)`. Creation
/// requires `final_fee <= initial_fee`; for other inputs the subtraction wraps as in the contract's
/// `unchecked` block.
#[must_use]
pub fn tick_rate_decayed_fee(
    initial_fee: u64,
    final_fee: u64,
    decay_rate_x32: u64,
    elapsed: u64,
) -> u64 {
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

/// `decayedFee` from `math/feeDecay.sol`.
///
/// `initial_fee` at 0 elapsed, `final_fee` from `duration` on, and in between, with
/// `E = decay_q128(duration)`,
/// `final_fee + floor((initial_fee - final_fee) * (decay_q128(elapsed) - E) / (2**128 - E))`.
/// `decay_q128` is non-increasing, so `decay_q128(elapsed) >= E` below the duration, and
/// `E < 2**128` for a positive duration. The numerator is below 2**192 and the quotient at most
/// `initial_fee - final_fee`. Creation requires `final_fee <= initial_fee`; for other inputs the
/// subtraction wraps as in the contract's `unchecked` block.
#[must_use]
pub fn decayed_fee(initial_fee: u64, final_fee: u64, duration: u32, elapsed: u64) -> u64 {
    if elapsed == 0 {
        return initial_fee;
    }
    if elapsed >= u64::from(duration) {
        return final_fee;
    }
    let endpoint = decay_q128(u64::from(duration));
    let excess = U256::from(initial_fee.wrapping_sub(final_fee)) * (decay_q128(elapsed) - endpoint)
        / (TWO_POW_128 - endpoint);
    final_fee.wrapping_add(excess.to::<u64>())
}

/// The launch inputs `previewInstallation` and `create` validate.
///
/// The token name, symbol, decimals and salt only determine the token address, so they are not
/// part of this model: take the token address, and with it `range.launch_token_is_token1`, from
/// `previewInstallation` or [`periphery_launch_token_address`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ZeroSeedLaunchParameters {
    /// `LaunchParameters.supply`: the requested supply, submitted unchanged to `create`. It is the
    /// token's `totalSupply` after creation and `LaunchCreated.parameters.supply`. Never rewrite
    /// it to the installed supply.
    pub supply: u128,
    /// `LaunchParameters.quoteToken`: this launch's quote, `address(0)` for native ETH.
    pub quote_token: Address,
    pub range: ZeroSeedLaunchRange,
    pub fee: ZeroSeedLaunchFeeSchedule,
}

/// The plan `previewInstallation` returns, without the token address and pool key. `create`
/// computes the same installation from the same inputs.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ZeroSeedLaunchInstallation {
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
    /// `liquidity`, rounded up, `0 < installed_supply <= supply`. The whole circulating
    /// inventory, all inside the position.
    pub installed_supply: u128,
    /// `supply - installed_supply`, minted directly to `address(0)` at creation. Never spendable
    /// and not an ERC-20 burn: `totalSupply` stays the requested supply.
    pub sink_supply: u128,
}

/// Why `previewInstallation` or `create` refuses a launch, by contract error, or why the SDK
/// refuses to support it.
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
    /// The range's token order disagrees with the predicted token and the launch's quote.
    #[error("launch token order does not match the predicted token and quote")]
    TokenOrderMismatch,
    /// `UnsupportedQuoteToken`: preview and creation refuse a nonzero quote without code.
    #[error("quote token is not supported")]
    UnsupportedQuoteToken,
    /// An ERC-20 quote without a reviewed `(chain, address, runtime keccak)` entry. SDK support
    /// policy, not a contract refusal.
    #[error("quote token is not reviewed")]
    QuoteNotReviewed,
    /// `InvalidParameters`: supply, tick spacing or range out of bounds.
    #[error("invalid launch parameters")]
    InvalidParameters,
    /// `InvalidFeeSchedule`: final fee above the initial fee, or (v1 only) zero duration.
    #[error("invalid fee schedule")]
    InvalidFeeSchedule,
    /// The fee decay parameter is not of the instance's fee model: a v1 instance takes a
    /// `feeDuration`, a v2 instance a `decayRateX32`. SDK refusal; the contract cannot decode the
    /// other shape.
    #[error("fee decay parameter does not match the instance's fee model")]
    FeeModelMismatch,
    /// `InvalidTradingStart`: trading start before the creation block.
    #[error("trading start is in the past")]
    InvalidTradingStart,
    /// Core `BoundsTickSpacing`: a bound is not a multiple of the tick spacing.
    #[error("range bounds are not aligned to the tick spacing")]
    BoundsTickSpacing,
    /// `ZeroLiquidity`: the requested supply buys no liquidity.
    #[error("supply buys zero liquidity")]
    ZeroLiquidity,
    /// `LiquidityAboveTickCap(liquidity, cap)`.
    #[error("liquidity {liquidity} above the per-tick cap {cap}")]
    LiquidityAboveTickCap { liquidity: u128, cap: u128 },
    /// The token amount for the liquidity does not fit Core's signed delta.
    #[error("installation amount overflow")]
    Overflow,
}

/// `_validate` of `previewInstallation` and `create` without the quote and metadata checks, plus
/// Core's bound alignment check.
///
/// Pure arithmetic validation, NOT supported-instance, quote support or producer timing approval.
/// `now` is the timestamp of the block the contract call executes in.
pub fn validate_launch_parameters_math(
    parameters: &ZeroSeedLaunchParameters,
    now: u64,
) -> Result<(), ZeroSeedLaunchParameterError> {
    validate_scalar_parameters(parameters, now)?;
    validate_bounds_alignment(&parameters.range)
}

fn validate_scalar_parameters(
    parameters: &ZeroSeedLaunchParameters,
    now: u64,
) -> Result<(), ZeroSeedLaunchParameterError> {
    type E = ZeroSeedLaunchParameterError;
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
    // Every `u64` fee rate and decay rate is valid; only the schedule shape is checked.
    let fee = &parameters.fee;
    if !fee.is_valid() {
        return Err(E::InvalidFeeSchedule);
    }
    if fee.trading_start < now {
        return Err(E::InvalidTradingStart);
    }
    Ok(())
}

/// Core's `BoundsTickSpacing` check of the position. Only for validated ranges.
fn validate_bounds_alignment(
    range: &ZeroSeedLaunchRange,
) -> Result<(), ZeroSeedLaunchParameterError> {
    let spacing = range.tick_spacing as i32;
    let (lower, upper) = range.pool_bounds();
    if lower % spacing != 0 || upper % spacing != 0 {
        return Err(ZeroSeedLaunchParameterError::BoundsTickSpacing);
    }
    Ok(())
}

/// `previewInstallation`: the largest liquidity the requested `parameters.supply` buys, the
/// exact supply that liquidity takes and the sink remainder. Pure arithmetic: the quote, metadata
/// and token-address checks are in [`ZeroSeedLaunchLocalPreview::contract_preview`].
pub fn preview_installation_math(
    parameters: &ZeroSeedLaunchParameters,
    now: u64,
) -> Result<ZeroSeedLaunchInstallation, ZeroSeedLaunchParameterError> {
    validate_launch_parameters_math(parameters, now)?;
    install_requested(parameters)
}

/// The installation `create` performs: it runs the preview calculation on the same requested
/// supply, so this is [`preview_installation_math`] for the creation block's timestamp. Liquidity
/// is not an input and the supply is never rewritten.
pub fn installation_math(
    parameters: &ZeroSeedLaunchParameters,
    now: u64,
) -> Result<ZeroSeedLaunchInstallation, ZeroSeedLaunchParameterError> {
    preview_installation_math(parameters, now)
}

/// Max liquidity for the requested supply, then `_installedSupply`. Only for validated parameters.
fn install_requested(
    parameters: &ZeroSeedLaunchParameters,
) -> Result<ZeroSeedLaunchInstallation, ZeroSeedLaunchParameterError> {
    let (lower, upper) = range_sqrt_ratios(&parameters.range);
    let liquidity = if parameters.range.launch_token_is_token1 {
        max_liquidity_for_token1(lower, upper, parameters.supply)
    } else {
        max_liquidity_for_token0(lower, upper, parameters.supply)
    };
    let installation = install(&parameters.range, liquidity.min(U256::from(u128::MAX)).to())?;
    let sink_supply = parameters
        .supply
        .checked_sub(installation.installed_supply)
        .ok_or(ZeroSeedLaunchParameterError::Overflow)?;
    Ok(ZeroSeedLaunchInstallation {
        sink_supply,
        ..installation
    })
}

/// `_installedSupply`: the token amount `Core` takes for `liquidity` at the initial price, rounded
/// up. `sink_supply` is left 0 for the caller.
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
        sink_supply: 0,
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
    /// `LaunchParameters.quoteToken`: the launch's own quote, the pool key's other token.
    pub quote_token: Address,
    /// `LaunchParameters.askTick`, `upperTick` and `tickSpacing`, and the token order from the
    /// event's `token` and pool key.
    pub range: ZeroSeedLaunchRange,
    /// The event's `liquidity`, the computed constant liquidity of the launch position.
    pub liquidity: u128,
    /// `LaunchParameters.tradingStart`, `feeDuration` (v1) or `decayRateX32` (v2), `initialFee`
    /// and `finalFee`.
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
    /// The instance is not the supported one, or the pool key's extension is not its extension.
    #[error("unsupported launch instance")]
    UnsupportedInstance,
    /// The launch's fee decay parameter is not of the instance's fee model.
    #[error("launch fee model does not match the instance")]
    FeeModelMismatch,
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
    /// Creates a supported LOCAL launch pool: missing or mismatched instance provenance, or a pool
    /// key whose extension is not the instance's, refuses it (`UnsupportedInstance`), as does a
    /// launch quote that is not observed as `quote` or not supported (`UnsupportedQuoteToken`).
    ///
    /// `key` is the pool key from `LaunchCreated`, `launch` the rest of that event, `state`
    /// `Core.poolState` of the pool and `quote` the observation of the launch's own quote token,
    /// all at the block being quoted. No live instance or live ERC-20 quote is supported.
    pub fn new(
        key: ZeroSeedLaunchPoolKey,
        launch: ZeroSeedLaunchConfig,
        state: ZeroSeedLaunchPoolState,
        instance: &ZeroSeedLaunchInstance,
        quote: &ZeroSeedLaunchQuoteObservation,
    ) -> Result<Self, ZeroSeedLaunchPoolConstructionError> {
        type E = ZeroSeedLaunchPoolConstructionError;
        instance.validate().map_err(|_| E::UnsupportedInstance)?;
        if key.config.extension != instance.extension {
            return Err(E::UnsupportedInstance);
        }
        if launch.fee.decay.model() != instance.fee_model {
            return Err(E::FeeModelMismatch);
        }
        if quote.chain_id != instance.chain_id
            || quote.quote != launch.quote_token
            || quote.supported_kind().is_err()
        {
            return Err(E::UnsupportedQuoteToken);
        }
        Self::new_math(key, launch, state)
    }

    /// Pure pool math, including synthetic quote arithmetic. This is NOT asset, quote or instance
    /// approval; service routing must use `new`, never this constructor. No RPC, calldata or plan
    /// production.
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
        // The pool key pairs the launch token with the launch's own quote. A native quote is
        // `address(0)` and so always token0; the launch token is a CREATE2 deployment and never
        // `address(0)`.
        let (launch_token, quote_token) = if launch.range.launch_token_is_token1 {
            (key.token1, key.token0)
        } else {
            (key.token0, key.token1)
        };
        if quote_token != launch.quote_token || launch_token.is_zero() {
            return Err(E::InvalidLaunchConfig);
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
            || !fee_schedule.is_valid()
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

/// The extension's token0 `_maxLiquidity`: the largest liquidity whose token0 debit fits
/// `amount`, `floor(amount * lower * upper / (2**128 * (upper - lower)))` over the fixed sqrt
/// ratios.
///
/// Core takes `ceil(ceil(L * 2**128 * (upper - lower) / upper) / lower)` for liquidity `L`, and
/// `ceil(ceil(n / u) / l) = ceil(n / (u * l))` for positive integers, so `debit(L) <= amount`
/// exactly when `L` is at most this floor. The product is below `2**127 * 2**192 * 2**192`, so it is
/// computed directly in 512 bits (the contract factors the compact ratios instead; both are the
/// same integer). The quotient is below `2**213`; the caller saturates it at `u128::MAX` like the
/// contract, which then refuses it at the per-tick cap. Unlike the shared `maxLiquidityForToken0`
/// helper, `lower * upper / 2**128` is never floored first.
fn max_liquidity_for_token0(lower: U256, upper: U256, amount: u128) -> U256 {
    let numerator = U512::from(amount) * U512::from(lower) * U512::from(upper);
    let denominator = U512::from(upper - lower) << 128;
    // Below `2**213` for every pair of valid ticks (adjacent ticks at the top of the range maximize
    // `lower * upper / (upper - lower)`), so it always fits.
    U256::from(numerator / denominator)
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

    /// Independent vectors from Foundry `cast abi-encode`, `cast keccak` and
    /// `cast compute-address` over the embedded creation code: six decimals, an empty name and a
    /// controller-namespaced salt, none of which the receipts exercise.
    #[test]
    fn token_prediction_matches_cast() {
        let extension = Address::from_str("0x5114703a4cf4256f0acb68f992c861d8c4d1b173").unwrap();
        let controller = Address::from_str("0xb27e16c3d01850191c1e027f7a3372cd2e1fb324").unwrap();
        let salt = B256::from(U256::from(1).to_be_bytes::<32>());
        let hash = |s| B256::from_str(s).unwrap();
        assert_eq!(
            launch_token_init_code_hash(extension, "Zero Seed", "ZERO", 6),
            hash("0x489e01af17be9fa3f51ca36008b8260e5d01bccf8bc21fd0875904f3474a6d34")
        );
        assert_eq!(
            launch_token_init_code_hash(extension, "", "A longer token symbol, 31 byte", 6),
            hash("0xb563b428ec60f9844d5d8c00b3fa21340e584a99b9c53775e309e718a49e0378")
        );
        assert_eq!(
            extension_token_salt(controller, salt),
            hash("0xe3b04b156b5b93b417dc7582589e75189e84de3e3317bc5bf8b13cfb42f15c2f")
        );
        assert_eq!(
            launch_token_address(extension, controller, salt, "Zero Seed", "ZERO", 6),
            Address::from_str("0x2f600c4d433C424a7e3B4a77F5098d32505a7f14").unwrap()
        );
    }

    /// A native quote is `address(0)`, so a launch token ordered as token0 would be `address(0)`.
    #[test]
    fn native_quote_requires_launch_token1() {
        let range = ZeroSeedLaunchRange {
            launch_token_is_token1: false,
            ask_tick: -13_815_500,
            upper_tick: -9_210_300,
            tick_spacing: 100,
        };
        let launch = |quote_token: &str| ZeroSeedLaunchConfig {
            quote_token: Address::from_str(quote_token).unwrap(),
            range,
            liquidity: 1_000_000,
            fee: ZeroSeedLaunchFeeSchedule {
                trading_start: 0,
                decay: ZeroSeedLaunchFeeDecay::FixedBaseDuration { fee_duration: 3600 },
                initial_fee: 0,
                final_fee: 0,
            },
        };
        let state = ZeroSeedLaunchPoolState {
            sqrt_ratio: to_sqrt_ratio::<Evm>(range.ask_tick).unwrap(),
            tick: range.ask_tick,
            liquidity: 1_000_000,
        };
        let key = |token0: &str| ZeroSeedLaunchPoolKey {
            token0: Address::from_str(token0).unwrap(),
            token1: Address::from_str("0x00000000000000000000000000000000000f0000").unwrap(),
            config: PoolConfig {
                extension: Address::from_str("0x5100000000000000000000000000000000000000").unwrap(),
                fee: 0,
                pool_type_config: TickSpacing(100),
            },
        };
        assert!(
            ZeroSeedLaunchPool::new_math(
                key("0x0000000000000000000000000000000000000001"),
                launch("0x00000000000000000000000000000000000f0000"),
                state
            )
            .is_ok()
        );
        assert_eq!(
            ZeroSeedLaunchPool::new_math(
                key("0x0000000000000000000000000000000000000000"),
                launch("0x00000000000000000000000000000000000f0000"),
                state
            ),
            Err(ZeroSeedLaunchPoolConstructionError::InvalidLaunchConfig)
        );
        // The pool key must pair the launch token with the launch's own quote.
        assert_eq!(
            ZeroSeedLaunchPool::new_math(
                key("0x0000000000000000000000000000000000000001"),
                launch("0x0000000000000000000000000000000000000002"),
                state
            ),
            Err(ZeroSeedLaunchPoolConstructionError::InvalidLaunchConfig)
        );
    }

    #[test]
    fn fee_schedule_is_monotone_and_bounded() {
        let schedule = ZeroSeedLaunchFeeSchedule {
            trading_start: 1_000,
            decay: ZeroSeedLaunchFeeDecay::FixedBaseDuration {
                fee_duration: 3_600,
            },
            initial_fee: ZERO_SEED_LAUNCH_MAX_CREATOR_FEE,
            final_fee: 0,
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
