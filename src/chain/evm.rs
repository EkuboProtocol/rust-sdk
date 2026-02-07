use crate::alloy_primitives::{aliases::B32, fixed_bytes, Address, FixedBytes, B256, U256};
use crate::alloy_primitives::{uint, Keccak256};
use derive_more::From;
use num_traits::Zero as _;
use thiserror::Error;

use crate::chain::Chain;

#[cfg(all(feature = "evm-alloy-0_6", not(feature = "evm-alloy-1")))]
type U96 = ruint::Uint<96, 2>;
#[cfg(feature = "evm-alloy-1")]
use crate::alloy_primitives::aliases::U96;
use crate::private;
use crate::quoting::pools::base::{
    BasePool, BasePoolConfig, BasePoolConstructionError, BasePoolKey, BasePoolQuoteError,
    BasePoolResources, BasePoolState, BasePoolTypeConfig, TickSpacing,
};
use crate::quoting::pools::boosted_fees::concentrated::{
    BoostedFeesConcentratedPool, BoostedFeesConcentratedPoolConfig,
    BoostedFeesConcentratedPoolConstructionError, BoostedFeesConcentratedPoolKey,
    BoostedFeesConcentratedPoolQuoteError, BoostedFeesConcentratedPoolResources,
    BoostedFeesConcentratedPoolState, BoostedFeesConcentratedPoolTypeConfig,
    BoostedFeesConcentratedStandalonePoolResources,
};
use crate::quoting::pools::boosted_fees::full_range::{
    BoostedFeesFullRangePool, BoostedFeesFullRangePoolConfig,
    BoostedFeesFullRangePoolConstructionError, BoostedFeesFullRangePoolKey,
    BoostedFeesFullRangePoolQuoteError, BoostedFeesFullRangePoolResources,
    BoostedFeesFullRangePoolState, BoostedFeesFullRangePoolTypeConfig,
};
use crate::quoting::pools::boosted_fees::stableswap::{
    BoostedFeesStableswapPool, BoostedFeesStableswapPoolConfig,
    BoostedFeesStableswapPoolConstructionError, BoostedFeesStableswapPoolKey,
    BoostedFeesStableswapPoolQuoteError, BoostedFeesStableswapPoolResources,
    BoostedFeesStableswapPoolState, BoostedFeesStableswapPoolTypeConfig,
};
use crate::quoting::pools::full_range::{
    FullRangePool, FullRangePoolConfig, FullRangePoolConstructionError, FullRangePoolKey,
    FullRangePoolQuoteError, FullRangePoolResources, FullRangePoolState, FullRangePoolTypeConfig,
};
use crate::quoting::pools::mev_capture::{
    MevCapturePool, MevCapturePoolConfig, MevCapturePoolConstructionError, MevCapturePoolKey,
    MevCapturePoolResources, MevCapturePoolState, MevCapturePoolTypeConfig,
    MevCaptureStandalonePoolResources,
};
use crate::quoting::pools::oracle::{
    OraclePool, OraclePoolConfig, OraclePoolConstructionError, OraclePoolKey, OraclePoolResources,
    OraclePoolState, OraclePoolTypeConfig, OracleStandalonePoolResources,
};
use crate::quoting::pools::stableswap::{
    StableswapPool, StableswapPoolConfig, StableswapPoolConstructionError, StableswapPoolKey,
    StableswapPoolQuoteError, StableswapPoolResources, StableswapPoolState,
    StableswapPoolTypeConfig,
};
use crate::quoting::pools::twamm::{
    TwammPool, TwammPoolConfig, TwammPoolConstructionError, TwammPoolKey, TwammPoolQuoteError,
    TwammPoolResources, TwammPoolState, TwammPoolTypeConfig, TwammStandalonePoolResources,
};
use crate::quoting::types::{PoolConfig, PoolKey, TokenAmount};

// Re-export pool types for ergonomic, chain-scoped usage.
pub type EvmBasePool = BasePool<Evm>;
pub type EvmBasePoolConstructionError = BasePoolConstructionError;
pub type EvmBasePoolConfig = BasePoolConfig<Evm>;
pub type EvmBasePoolKey = BasePoolKey<Evm>;
pub type EvmBasePoolQuoteError = BasePoolQuoteError;
pub type EvmBasePoolResources = BasePoolResources;
pub type EvmBasePoolState = BasePoolState;
pub type EvmBasePoolTypeConfig = BasePoolTypeConfig;

pub type EvmFullRangePool = FullRangePool;
pub type EvmFullRangePoolConstructionError = FullRangePoolConstructionError;
pub type EvmFullRangePoolConfig = FullRangePoolConfig;
pub type EvmFullRangePoolKey = FullRangePoolKey;
pub type EvmFullRangePoolQuoteError = FullRangePoolQuoteError;
pub type EvmFullRangePoolResources = FullRangePoolResources;
pub type EvmFullRangePoolState = FullRangePoolState;
pub type EvmFullRangePoolTypeConfig = FullRangePoolTypeConfig;

pub type EvmStableswapPool = StableswapPool;
pub type EvmStableswapPoolConstructionError = StableswapPoolConstructionError;
pub type EvmStableswapPoolConfig = StableswapPoolConfig;
pub type EvmStableswapPoolKey = StableswapPoolKey;
pub type EvmStableswapPoolQuoteError = StableswapPoolQuoteError;
pub type EvmStableswapPoolResources = StableswapPoolResources;
pub type EvmStableswapPoolState = StableswapPoolState;
pub type EvmStableswapPoolTypeConfig = StableswapPoolTypeConfig;

pub type EvmMevCapturePool = MevCapturePool;
pub type EvmMevCapturePoolConstructionError = MevCapturePoolConstructionError;
pub type EvmMevCapturePoolConfig = MevCapturePoolConfig;
pub type EvmMevCapturePoolKey = MevCapturePoolKey;
pub type EvmMevCapturePoolQuoteError = BasePoolQuoteError;
pub type EvmMevCapturePoolResources = MevCapturePoolResources;
pub type EvmMevCaptureStandalonePoolResources = MevCaptureStandalonePoolResources;
pub type EvmMevCapturePoolState = MevCapturePoolState;
pub type EvmMevCapturePoolTypeConfig = MevCapturePoolTypeConfig;

pub type EvmOraclePool = OraclePool<Evm>;
pub type EvmOraclePoolConstructionError =
    OraclePoolConstructionError<FullRangePoolConstructionError>;
pub type EvmOraclePoolConfig = OraclePoolConfig<Evm>;
pub type EvmOraclePoolKey = OraclePoolKey<Evm>;
pub type EvmOraclePoolQuoteError = FullRangePoolQuoteError;
pub type EvmOraclePoolResources = OraclePoolResources<FullRangePoolResources>;
pub type EvmOracleStandalonePoolResources = OracleStandalonePoolResources;
pub type EvmOraclePoolState = OraclePoolState<FullRangePoolState>;
pub type EvmOraclePoolTypeConfig = OraclePoolTypeConfig<Evm>;

pub type EvmTwammPool = TwammPool<Evm>;
pub type EvmTwammPoolConstructionError = TwammPoolConstructionError<FullRangePoolConstructionError>;
pub type EvmTwammPoolConfig = TwammPoolConfig<Evm>;
pub type EvmTwammPoolKey = TwammPoolKey<Evm>;
pub type EvmTwammPoolQuoteError = TwammPoolQuoteError<FullRangePoolQuoteError>;
pub type EvmTwammPoolResources = TwammPoolResources<FullRangePoolResources>;
pub type EvmTwammStandalonePoolResources = TwammStandalonePoolResources;
pub type EvmTwammPoolState = TwammPoolState<FullRangePoolState>;
pub type EvmTwammPoolTypeConfig = TwammPoolTypeConfig<Evm>;

pub type EvmBoostedFeesConcentratedPoolConstructionError =
    BoostedFeesConcentratedPoolConstructionError;
pub type EvmBoostedFeesConcentratedPoolTypeConfig = BoostedFeesConcentratedPoolTypeConfig;
pub type EvmBoostedFeesConcentratedPoolKey = BoostedFeesConcentratedPoolKey;
pub type EvmBoostedFeesConcentratedPoolConfig<P> = BoostedFeesConcentratedPoolConfig<P>;
pub type EvmBoostedFeesConcentratedPool = BoostedFeesConcentratedPool;
pub type EvmBoostedFeesConcentratedPoolResources = BoostedFeesConcentratedPoolResources;
pub type EvmBoostedFeesConcentratedStandalonePoolResources =
    BoostedFeesConcentratedStandalonePoolResources;
pub type EvmBoostedFeesConcentratedPoolState = BoostedFeesConcentratedPoolState;
pub type EvmBoostedFeesConcentratedPoolQuoteError = BoostedFeesConcentratedPoolQuoteError;

pub type EvmBoostedFeesFullRangePool = BoostedFeesFullRangePool;
pub type EvmBoostedFeesFullRangePoolConstructionError = BoostedFeesFullRangePoolConstructionError;
pub type EvmBoostedFeesFullRangePoolConfig = BoostedFeesFullRangePoolConfig;
pub type EvmBoostedFeesFullRangePoolKey = BoostedFeesFullRangePoolKey;
pub type EvmBoostedFeesFullRangePoolQuoteError = BoostedFeesFullRangePoolQuoteError;
pub type EvmBoostedFeesFullRangePoolResources = BoostedFeesFullRangePoolResources;
pub type EvmBoostedFeesFullRangePoolState = BoostedFeesFullRangePoolState;
pub type EvmBoostedFeesFullRangePoolTypeConfig = BoostedFeesFullRangePoolTypeConfig;

pub type EvmBoostedFeesStableswapPool = BoostedFeesStableswapPool;
pub type EvmBoostedFeesStableswapPoolConstructionError = BoostedFeesStableswapPoolConstructionError;
pub type EvmBoostedFeesStableswapPoolConfig = BoostedFeesStableswapPoolConfig;
pub type EvmBoostedFeesStableswapPoolKey = BoostedFeesStableswapPoolKey;
pub type EvmBoostedFeesStableswapPoolResources = BoostedFeesStableswapPoolResources;
pub type EvmBoostedFeesStableswapPoolState = BoostedFeesStableswapPoolState;
pub type EvmBoostedFeesStableswapPoolQuoteError = BoostedFeesStableswapPoolQuoteError;
pub type EvmBoostedFeesStableswapPoolTypeConfig = BoostedFeesStableswapPoolTypeConfig;

pub const EVM_NATIVE_TOKEN_ADDRESS: Address = Address::ZERO;
pub const EVM_MAX_TICK_SPACING: TickSpacing = TickSpacing(698605);
pub const EVM_FULL_RANGE_TICK_SPACING: u32 = 0;
pub const EVM_MAX_STABLESWAP_AMPLIFICATION_FACTOR: u8 = 26;

pub const EVM_MIN_TICK: i32 = -88722835;
pub const EVM_MAX_TICK: i32 = 88722835;

pub const EVM_MIN_SQRT_RATIO: U256 = U256::from_limbs([447090492618908, 1, 0, 0]);
pub const EVM_MAX_SQRT_RATIO: U256 =
    U256::from_limbs([0, 7567914946021818368, 18446296994052723738, 0]);

pub const EVM_FEE_DENOMINATOR: U256 = U256::from_limbs([0, 1, 0, 0]);
pub const EVM_FEE_BITS: u8 = 64;

const TWO_POW_160: U256 = U256::from_limbs([0, 0, 0x100000000, 0]);
const TWO_POW_128: U256 = U256::from_limbs([0, 0, 1, 0]);
const TWO_POW_96: U256 = U256::from_limbs([0, 0x0100000000, 0, 0]);
const TWO_POW_95: U256 = U256::from_limbs([0, 0x80000000, 0, 0]);
const TWO_POW_94: U256 = U256::from_limbs([0, 0x40000000, 0, 0]);
const TWO_POW_192: U256 = U256::from_limbs([0, 0, 0, 1]);

const BIT_MASK: U96 = uint!(0xc00000000000000000000000_U96);
const NOT_BIT_MASK: U96 = uint!(0x3fffffffffffffffffffffff_U96);

/// Chain implementation for EVM-compatible networks.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub struct Evm;

/// Pool config alias for EVM.
pub type EvmPoolConfig =
    PoolConfig<<Evm as Chain>::Address, <Evm as Chain>::Fee, EvmPoolTypeConfig>;
/// Pool key alias for EVM.
pub type EvmPoolKey = PoolKey<<Evm as Chain>::Address, <Evm as Chain>::Fee, EvmPoolTypeConfig>;
/// Token amount alias for EVM.
pub type EvmTokenAmount = TokenAmount<<Evm as Chain>::Address>;

/// Pool type configuration variants for EVM.
#[derive(Clone, Copy, From, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum EvmPoolTypeConfig {
    /// Full range pool config.
    FullRange(FullRangePoolTypeConfig),
    /// Stableswap config for pegged assets.
    Stableswap(StableswapPoolTypeConfig),
    /// Concentrated liquidity config (tick spacing).
    Concentrated(BasePoolTypeConfig),
}

#[cfg(feature = "evm-alloy-1")]
const EVM_POOL_TYPE_CONFIG_CONCENTRATED_MASK: B32 = fixed_bytes!("0x80000000");
#[cfg(all(feature = "evm-alloy-0_6", not(feature = "evm-alloy-1")))]
const EVM_POOL_TYPE_CONFIG_CONCENTRATED_MASK: B32 = fixed_bytes!("80000000");

#[cfg(feature = "evm-alloy-1")]
const EVM_POOL_TYPE_CONFIG_TICK_SPACING_MASK: B32 = fixed_bytes!("0x7fffffff");
#[cfg(all(feature = "evm-alloy-0_6", not(feature = "evm-alloy-1")))]
const EVM_POOL_TYPE_CONFIG_TICK_SPACING_MASK: B32 = fixed_bytes!("7fffffff");

/// Order identifier emitted by the TWAMM extension.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct EvmOrderKey {
    /// The smaller token address.
    pub token0: Address,
    /// The larger token address.
    pub token1: Address,
    /// Order details (fee, sell direction, start/end timestamps).
    pub config: EvmOrderConfig,
}

/// Details of a TWAMM order.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct EvmOrderConfig {
    /// Fee tier of the TWAMM pool.
    pub fee: u64,
    /// Whether the order is selling token1.
    pub is_token1: bool,
    /// Order start time in seconds.
    pub start_time: u64,
    /// Order end time in seconds.
    pub end_time: u64,
}

/// Errors when parsing pool type configuration.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Error)]
pub enum EvmPoolTypeConfigParseError {
    #[error("stableswap center tick is not between min and max tick")]
    InvalidCenterTick,
    #[error("stableswap amplification factor exceeds the maximum allowed value")]
    InvalidStableswapAmplification,
    #[error("tick spacing exceeds the maximum allowed value")]
    InvalidTickSpacing,
}

/// Errors when parsing pool configuration.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Error)]
pub enum EvmPoolConfigParseError {
    #[error("invalid pool type config")]
    InvalidPoolTypeConfig(#[from] EvmPoolTypeConfigParseError),
}

impl Chain for Evm {
    type Address = Address;
    type Fee = u64;
    type FullRangePool = FullRangePool;
    type FullRangePoolConstructionError = FullRangePoolConstructionError;

    fn max_tick_spacing() -> TickSpacing {
        EVM_MAX_TICK_SPACING
    }

    fn min_tick() -> i32 {
        EVM_MIN_TICK
    }

    fn max_tick() -> i32 {
        EVM_MAX_TICK
    }

    fn min_sqrt_ratio() -> U256 {
        EVM_MIN_SQRT_RATIO
    }

    fn max_sqrt_ratio() -> U256 {
        EVM_MAX_SQRT_RATIO
    }

    fn min_sqrt_ratio_full_range() -> U256 {
        EVM_MIN_SQRT_RATIO
    }

    fn max_sqrt_ratio_full_range() -> U256 {
        EVM_MAX_SQRT_RATIO
    }

    fn adjust_sqrt_ratio_precision(ratio: U256) -> U256 {
        if ratio >= TWO_POW_160 {
            (ratio >> 98) << 98
        } else if ratio >= TWO_POW_128 {
            (ratio >> 66) << 66
        } else if ratio >= TWO_POW_96 {
            (ratio >> 34) << 34
        } else {
            (ratio >> 2) << 2
        }
    }

    fn fee_denominator() -> U256 {
        EVM_FEE_DENOMINATOR
    }

    fn fee_bits() -> u8 {
        EVM_FEE_BITS
    }

    fn new_full_range_pool(
        token0: Self::Address,
        token1: Self::Address,
        fee: Self::Fee,
        extension: Self::Address,
        sqrt_ratio: U256,
        active_liquidity: u128,
    ) -> Result<Self::FullRangePool, Self::FullRangePoolConstructionError> {
        FullRangePool::new(
            PoolKey {
                token0,
                token1,
                config: PoolConfig {
                    fee,
                    pool_type_config: FullRangePoolTypeConfig,
                    extension,
                },
            },
            FullRangePoolState {
                sqrt_ratio,
                liquidity: active_liquidity,
            },
        )
    }
}

impl EvmPoolKey {
    /// Reconstructs a pool key from a TWAMM order key.
    pub fn from_order_key(order_key: EvmOrderKey, twamm_address: Address) -> Self {
        Self {
            token0: order_key.token0,
            token1: order_key.token1,
            config: PoolConfig {
                extension: twamm_address,
                fee: order_key.config.fee,
                pool_type_config: EvmPoolTypeConfig::FullRange(FullRangePoolTypeConfig),
            },
        }
    }

    /// Computes the on-chain pool id (keccak256 of token0, token1 and config).
    pub fn pool_id(&self) -> B256 {
        let mut hasher = Keccak256::new();

        hasher.update(self.token0.into_word());
        hasher.update(self.token1.into_word());
        hasher.update(B256::from(self.config));

        hasher.finalize()
    }
}

impl From<B256> for EvmOrderConfig {
    fn from(FixedBytes(raw): B256) -> Self {
        Self {
            fee: u64::from_be_bytes(raw[0..8].try_into().unwrap()),
            is_token1: raw[8] != 0,
            start_time: u64::from_be_bytes(raw[16..24].try_into().unwrap()),
            end_time: u64::from_be_bytes(raw[24..32].try_into().unwrap()),
        }
    }
}

impl From<EvmOrderConfig> for B256 {
    fn from(config: EvmOrderConfig) -> Self {
        let mut raw = [0u8; 32];

        raw[0..8].copy_from_slice(&config.fee.to_be_bytes());
        raw[8] = u8::from(config.is_token1);
        raw[16..24].copy_from_slice(&config.start_time.to_be_bytes());
        raw[24..32].copy_from_slice(&config.end_time.to_be_bytes());

        raw.into()
    }
}

impl TryFrom<B32> for EvmPoolTypeConfig {
    type Error = EvmPoolTypeConfigParseError;

    fn try_from(value: B32) -> Result<Self, Self::Error> {
        if value == B32::ZERO {
            return Ok(Self::FullRange(FullRangePoolTypeConfig));
        }

        if value.bit_and(EVM_POOL_TYPE_CONFIG_CONCENTRATED_MASK) == B32::ZERO {
            let mut center_tick_bytes = [0u8; 4];
            center_tick_bytes[1..].copy_from_slice(&value.0[1..]);
            if value.0[1] & 0x80 != 0 {
                center_tick_bytes[0] = 0xff;
            }
            let center_tick = i32::from_be_bytes(center_tick_bytes) * 16;

            if !(EVM_MIN_TICK..=EVM_MAX_TICK).contains(&center_tick) {
                return Err(EvmPoolTypeConfigParseError::InvalidCenterTick);
            }

            let amplification_factor = value.0[0];

            if amplification_factor > EVM_MAX_STABLESWAP_AMPLIFICATION_FACTOR {
                return Err(EvmPoolTypeConfigParseError::InvalidStableswapAmplification);
            }

            Ok(Self::Stableswap(StableswapPoolTypeConfig {
                center_tick,
                amplification_factor,
            }))
        } else {
            let tick_spacing =
                u32::from_be_bytes(value.bit_and(EVM_POOL_TYPE_CONFIG_TICK_SPACING_MASK).0);

            if tick_spacing > EVM_MAX_TICK_SPACING.0 || tick_spacing.is_zero() {
                return Err(EvmPoolTypeConfigParseError::InvalidTickSpacing);
            }

            Ok(Self::Concentrated(TickSpacing(tick_spacing)))
        }
    }
}

impl From<EvmPoolTypeConfig> for B32 {
    fn from(value: EvmPoolTypeConfig) -> Self {
        match value {
            EvmPoolTypeConfig::FullRange(_) => Self::ZERO,
            EvmPoolTypeConfig::Stableswap(StableswapPoolTypeConfig {
                center_tick,
                amplification_factor,
            }) => {
                let mut compressed = (center_tick / 16).to_be_bytes();
                compressed[0] = amplification_factor;

                Self(compressed)
            }
            EvmPoolTypeConfig::Concentrated(TickSpacing(tick_spacing)) => {
                let mut compressed = tick_spacing.to_be_bytes();
                compressed[0] |= 0x80;

                Self(compressed)
            }
        }
    }
}

impl From<EvmPoolConfig> for B256 {
    fn from(value: EvmPoolConfig) -> Self {
        value
            .extension
            .0
            .concat_const::<_, 28>(FixedBytes(value.fee.to_be_bytes()))
            .concat_const(value.pool_type_config.into())
    }
}

impl TryFrom<B256> for EvmPoolConfig {
    type Error = EvmPoolConfigParseError;

    fn try_from(FixedBytes(bytes): B256) -> Result<Self, Self::Error> {
        Ok(PoolConfig {
            extension: Address::from_slice(&bytes[..20]),
            fee: u64::from_be_bytes(bytes[20..28].try_into().expect("slice with correct length")),
            pool_type_config: EvmPoolTypeConfig::try_from(B32::from_slice(&bytes[28..32]))?,
        })
    }
}

impl private::Sealed for Evm {}

/// Converts a compressed sqrt ratio into a fixed-point sqrt ratio.
pub fn float_sqrt_ratio_to_fixed(sqrt_ratio_float: U96) -> U256 {
    U256::from(sqrt_ratio_float & NOT_BIT_MASK)
        << u8::try_from(uint!(2_U96) + ((sqrt_ratio_float & BIT_MASK) >> 89_u8)).unwrap()
}

/// Converts a fixed-point sqrt ratio into the compressed contract representation.
pub fn fixed_sqrt_ratio_to_contract_sqrt_ratio(sqrt_ratio: U256) -> U256 {
    if sqrt_ratio >= TWO_POW_192 {
        panic!("failed to convert sqrt ratio limit");
    } else if sqrt_ratio >= TWO_POW_160 {
        (sqrt_ratio >> 98) + U256::from(BIT_MASK)
    } else if sqrt_ratio >= TWO_POW_128 {
        (sqrt_ratio >> 66) + TWO_POW_95
    } else if sqrt_ratio >= TWO_POW_96 {
        (sqrt_ratio >> 34) + TWO_POW_94
    } else {
        sqrt_ratio >> 2
    }
}

#[cfg(test)]
mod tests {
    use crate::alloy_primitives::address;

    use crate::chain::tests::ChainTest;

    use super::*;

    #[cfg(feature = "evm-alloy-1")]
    const ONE_ADDRESS: Address = address!("0x0000000000000000000000000000000000000001");
    #[cfg(all(feature = "evm-alloy-0_6", not(feature = "evm-alloy-1")))]
    const ONE_ADDRESS: Address = address!("0000000000000000000000000000000000000001");

    #[cfg(feature = "evm-alloy-1")]
    const ORDER_CONFIG_RAW: B256 =
        fixed_bytes!("0x01020304050607080100000000000000112233445566778899aabbccddeeff00");
    #[cfg(all(feature = "evm-alloy-0_6", not(feature = "evm-alloy-1")))]
    const ORDER_CONFIG_RAW: B256 =
        fixed_bytes!("01020304050607080100000000000000112233445566778899aabbccddeeff00");

    #[cfg(feature = "evm-alloy-1")]
    const POOL_TOKEN0: Address = address!("0x37c8671A16E257eC501711Cc1d7eb8AF8544A69f");
    #[cfg(all(feature = "evm-alloy-0_6", not(feature = "evm-alloy-1")))]
    const POOL_TOKEN0: Address = address!("37c8671A16E257eC501711Cc1d7eb8AF8544A69f");

    #[cfg(feature = "evm-alloy-1")]
    const POOL_TOKEN1: Address = address!("0xeE8F2aA3e6864493BEae55E27bb5d8a7B57021F8");
    #[cfg(all(feature = "evm-alloy-0_6", not(feature = "evm-alloy-1")))]
    const POOL_TOKEN1: Address = address!("eE8F2aA3e6864493BEae55E27bb5d8a7B57021F8");

    #[cfg(feature = "evm-alloy-1")]
    const POOL_CONFIG_RAW: B256 =
        fixed_bytes!("0x000000000000000000000000000000000000000040000000000000000d000000");
    #[cfg(all(feature = "evm-alloy-0_6", not(feature = "evm-alloy-1")))]
    const POOL_CONFIG_RAW: B256 =
        fixed_bytes!("000000000000000000000000000000000000000040000000000000000d000000");

    #[cfg(feature = "evm-alloy-1")]
    const POOL_ID: B256 =
        fixed_bytes!("0xa7dfc779e04825212b0daf2a2272e9574a1cc54cd3ff26f590a1b2789677b3c9");
    #[cfg(all(feature = "evm-alloy-0_6", not(feature = "evm-alloy-1")))]
    const POOL_ID: B256 =
        fixed_bytes!("a7dfc779e04825212b0daf2a2272e9574a1cc54cd3ff26f590a1b2789677b3c9");

    impl ChainTest for Evm {
        fn zero_address() -> Self::Address {
            Address::ZERO
        }

        fn one_address() -> Self::Address {
            ONE_ADDRESS
        }
    }

    #[test]
    fn order_config_round_trips_from_b256() {
        let config = EvmOrderConfig::from(ORDER_CONFIG_RAW);

        assert_eq!(config.fee, 0x0102_0304_0506_0708);
        assert!(config.is_token1);
        assert_eq!(config.start_time, 0x1122_3344_5566_7788);
        assert_eq!(config.end_time, 0x99aa_bbcc_ddee_ff00);

        let encoded: B256 = config.into();
        assert_eq!(encoded, ORDER_CONFIG_RAW);
    }

    #[test]
    fn stableswap_round_trip_positive_and_negative_ticks() {
        let cases = [
            (0, 1u8),
            (10, 26u8),
            (-1, 5u8),
            (1_000_000, 0u8),
            (-1_000_000, EVM_MAX_STABLESWAP_AMPLIFICATION_FACTOR),
            (-27_631_040, 14),
        ];

        for (center_tick, amplification) in cases {
            let encoded: B32 = EvmPoolTypeConfig::Stableswap(StableswapPoolTypeConfig {
                center_tick,
                amplification_factor: amplification,
            })
            .into();
            let decoded = EvmPoolTypeConfig::try_from(encoded).unwrap();

            assert_eq!(
                decoded,
                EvmPoolTypeConfig::Stableswap(StableswapPoolTypeConfig {
                    center_tick: center_tick - center_tick % 16,
                    amplification_factor: amplification
                })
            );
        }
    }

    #[test]
    fn stableswap_rejects_amplification_over_max() {
        let mut raw = [0u8; 4];
        raw[0] = EVM_MAX_STABLESWAP_AMPLIFICATION_FACTOR + 1;
        raw[3] = 1; // center tick = 1

        let b32 = B32::from(u32::from_be_bytes(raw));
        assert_eq!(
            EvmPoolTypeConfig::try_from(b32).unwrap_err(),
            EvmPoolTypeConfigParseError::InvalidStableswapAmplification
        );
    }

    #[test]
    fn concentrated_round_trip_and_limits() {
        let ok = [1u32, EVM_MAX_TICK_SPACING.0];

        for spacing in ok {
            let config = EvmPoolTypeConfig::Concentrated(TickSpacing(spacing));
            let encoded: B32 = config.into();
            let decoded = EvmPoolTypeConfig::try_from(encoded).unwrap();
            assert_eq!(
                decoded,
                EvmPoolTypeConfig::Concentrated(TickSpacing(spacing))
            );
        }

        for spacing in [0u32, EVM_MAX_TICK_SPACING.0 + 1] {
            let mut spacing_bytes = spacing.to_be_bytes();
            spacing_bytes[0] |= 0x80;
            let b32 = B32::from(u32::from_be_bytes(spacing_bytes));
            assert_eq!(
                EvmPoolTypeConfig::try_from(b32).unwrap_err(),
                EvmPoolTypeConfigParseError::InvalidTickSpacing
            );
        }
    }

    #[test]
    fn pool_id() {
        let pool_key = PoolKey {
            token0: POOL_TOKEN0,
            token1: POOL_TOKEN1,
            config: POOL_CONFIG_RAW.try_into().unwrap(),
        };

        // https://sepolia.etherscan.io/tx/0xcc9c476c9a1ec9a28ecd1666c998c35e1255ce739993b1be68f4401c67f80ee9#eventlog
        assert_eq!(pool_key.pool_id(), POOL_ID);
    }

    #[test]
    fn float_sqrt_ratio_to_fixed() {
        // https://github.com/EkuboProtocol/evm-contracts/blob/ce72f5df636d69b94718f4d4d6c0dc6bf5fe9d23/test/types/sqrtRatio.t.sol#L65
        assert_eq!(
            super::float_sqrt_ratio_to_fixed(uint!(0x3ffffffffffffffff9ba1f6d_U96)),
            uint!(79228162514264337593122979252_U256)
        );
    }

    #[test]
    fn fixed_sqrt_ratio_to_contract_sqrt_ratio_round_trips_with_float_conversion() {
        let expected_contract_sqrt_ratio = uint!(0x3ffffffffffffffff9ba1f6d_U96);
        let contract_sqrt_ratio = super::fixed_sqrt_ratio_to_contract_sqrt_ratio(uint!(
            79228162514264337593122979252_U256
        ));
        assert_eq!(
            contract_sqrt_ratio,
            U256::from(expected_contract_sqrt_ratio)
        );

        let fixed_sqrt_ratio = super::float_sqrt_ratio_to_fixed(expected_contract_sqrt_ratio);
        assert_eq!(
            fixed_sqrt_ratio,
            Evm::adjust_sqrt_ratio_precision(uint!(79228162514264337593122979252_U256))
        );
    }

    #[test]
    #[should_panic(expected = "failed to convert sqrt ratio limit")]
    fn fixed_sqrt_ratio_to_contract_sqrt_ratio_rejects_too_large_ratio() {
        let _ = super::fixed_sqrt_ratio_to_contract_sqrt_ratio(TWO_POW_192);
    }
}
