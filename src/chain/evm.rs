use alloy_primitives::{aliases::B32, fixed_bytes, Address, FixedBytes, B256, U256};
use derive_more::From;
use num_traits::Zero as _;
use thiserror::Error;

use crate::chain::Chain;
use crate::private;
use crate::quoting::pools::base::{
    BasePool, BasePoolConstructionError, BasePoolQuoteError, BasePoolResources, BasePoolState,
    BasePoolTypeConfig, TickSpacing,
};
use crate::quoting::pools::full_range::{
    FullRangePool, FullRangePoolConstructionError, FullRangePoolQuoteError, FullRangePoolResources,
    FullRangePoolState, FullRangePoolTypeConfig,
};
use crate::quoting::pools::mev_capture::{
    MevCapturePool, MevCapturePoolConstructionError, MevCapturePoolResources, MevCapturePoolState,
    MevCapturePoolTypeConfig,
};
use crate::quoting::pools::oracle::{
    OraclePool, OraclePoolConstructionError, OraclePoolResources, OraclePoolState,
};
use crate::quoting::pools::stableswap::{
    StableswapPool, StableswapPoolConstructionError, StableswapPoolQuoteError,
    StableswapPoolResources, StableswapPoolTypeConfig,
};
use crate::quoting::pools::twamm::{
    TwammPool, TwammPoolConstructionError, TwammPoolQuoteError, TwammPoolResources, TwammPoolState,
};
use crate::quoting::types::{PoolConfig, PoolKey};

// Re-export pool types for ergonomic, chain-scoped usage.
pub type EvmBasePool = BasePool<Evm>;
pub type EvmBasePoolConstructionError = BasePoolConstructionError;
pub type EvmBasePoolQuoteError = BasePoolQuoteError;
pub type EvmBasePoolResources = BasePoolResources;
pub type EvmBasePoolState = BasePoolState;
pub type EvmBasePoolTypeConfig = BasePoolTypeConfig;

pub type EvmFullRangePool = FullRangePool;
pub type EvmFullRangePoolConstructionError = FullRangePoolConstructionError;
pub type EvmFullRangePoolQuoteError = FullRangePoolQuoteError;
pub type EvmFullRangePoolResources = FullRangePoolResources;
pub type EvmFullRangePoolState = FullRangePoolState;
pub type EvmFullRangePoolTypeConfig = FullRangePoolTypeConfig;

pub type EvmStableswapPool = StableswapPool;
pub type EvmStableswapPoolConstructionError = StableswapPoolConstructionError;
pub type EvmStableswapPoolQuoteError = StableswapPoolQuoteError;
pub type EvmStableswapPoolResources = StableswapPoolResources;
pub type EvmStableswapPoolState = FullRangePoolState;
pub type EvmStableswapPoolTypeConfig = StableswapPoolTypeConfig;

pub type EvmMevCapturePool = MevCapturePool;
pub type EvmMevCapturePoolConstructionError = MevCapturePoolConstructionError;
pub type EvmMevCapturePoolQuoteError = BasePoolQuoteError;
pub type EvmMevCapturePoolResources = MevCapturePoolResources;
pub type EvmMevCapturePoolState = MevCapturePoolState;
pub type EvmMevCapturePoolTypeConfig = MevCapturePoolTypeConfig;

pub type EvmOraclePool = OraclePool<Evm>;
pub type EvmOraclePoolConstructionError =
    OraclePoolConstructionError<FullRangePoolConstructionError>;
pub type EvmOraclePoolQuoteError = FullRangePoolQuoteError;
pub type EvmOraclePoolResources = OraclePoolResources<FullRangePoolResources>;
pub type EvmOraclePoolState = OraclePoolState<FullRangePoolState>;
pub type EvmOraclePoolTypeConfig = FullRangePoolTypeConfig;

pub type EvmTwammPool = TwammPool<Evm>;
pub type EvmTwammPoolConstructionError = TwammPoolConstructionError<FullRangePoolConstructionError>;
pub type EvmTwammPoolQuoteError = TwammPoolQuoteError<FullRangePoolQuoteError>;
pub type EvmTwammPoolResources = TwammPoolResources<FullRangePoolResources>;
pub type EvmTwammPoolState = TwammPoolState<FullRangePoolState>;
pub type EvmTwammPoolTypeConfig = FullRangePoolTypeConfig;

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

/// Chain implementation for EVM-compatible networks.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub struct Evm;

/// Pool config alias for EVM.
pub type EvmPoolConfig = PoolConfig<<Evm as Chain>::Address, <Evm as Chain>::Fee, PoolTypeConfig>;
/// Pool key alias for EVM.
pub type EvmPoolKey = PoolKey<<Evm as Chain>::Address, <Evm as Chain>::Fee, PoolTypeConfig>;
/// Pool type config alias for EVM.
pub type EvmPoolTypeConfig = PoolTypeConfig;

/// Pool type configuration variants for EVM.
#[derive(From, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum PoolTypeConfig {
    /// Full range pool config.
    FullRange(FullRangePoolTypeConfig),
    /// Stableswap config for pegged assets.
    Stableswap(StableswapPoolTypeConfig),
    /// Concentrated liquidity config (tick spacing).
    Concentrated(BasePoolTypeConfig),
}

/// Errors when parsing pool type configuration.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Error)]
pub enum PoolTypeConfigParseError {
    #[error("stableswap center tick is not between min and max tick")]
    InvalidCenterTick,
    #[error("stableswap amplification factor exceeds the maximum allowed value")]
    InvalidStableswapAmplification,
    #[error("tick spacing exceeds the maximum allowed value")]
    InvalidTickSpacing,
}

/// Errors when parsing pool configuration.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Error)]
pub enum PoolConfigParseError {
    #[error("invalid pool type config")]
    InvalidPoolTypeConfig(#[from] PoolTypeConfigParseError),
}

impl TryFrom<B32> for PoolTypeConfig {
    type Error = PoolTypeConfigParseError;

    fn try_from(value: B32) -> Result<Self, Self::Error> {
        if value == B32::ZERO {
            return Ok(Self::FullRange(FullRangePoolTypeConfig));
        }

        if value.bit_and(fixed_bytes!("0x80000000")) == B32::ZERO {
            let mut center_tick_bytes = [0u8; 4];
            center_tick_bytes[1..].copy_from_slice(&value.0[1..]);
            if value.0[1] & 0x80 != 0 {
                center_tick_bytes[0] = 0xff;
            }
            let center_tick = i32::from_be_bytes(center_tick_bytes);

            if !(EVM_MIN_TICK..=EVM_MAX_TICK).contains(&center_tick) {
                return Err(PoolTypeConfigParseError::InvalidCenterTick);
            }

            let amplification_factor = value.0[0];

            if amplification_factor > EVM_MAX_STABLESWAP_AMPLIFICATION_FACTOR {
                return Err(PoolTypeConfigParseError::InvalidStableswapAmplification);
            }

            Ok(Self::Stableswap(StableswapPoolTypeConfig {
                center_tick,
                amplification_factor,
            }))
        } else {
            let tick_spacing = u32::from_be_bytes(value.bit_and(fixed_bytes!("0x7fffffff")).0);

            if tick_spacing > EVM_MAX_TICK_SPACING.0 || tick_spacing.is_zero() {
                return Err(PoolTypeConfigParseError::InvalidTickSpacing);
            }

            Ok(Self::Concentrated(TickSpacing(tick_spacing)))
        }
    }
}

impl From<PoolTypeConfig> for B32 {
    fn from(value: PoolTypeConfig) -> Self {
        match value {
            PoolTypeConfig::FullRange(_) => Self::ZERO,
            PoolTypeConfig::Stableswap(StableswapPoolTypeConfig {
                center_tick,
                amplification_factor,
            }) => {
                let mut compressed = center_tick.to_be_bytes();
                compressed[0] = amplification_factor;

                Self(compressed)
            }
            PoolTypeConfig::Concentrated(TickSpacing(tick_spacing)) => {
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
    type Error = PoolConfigParseError;

    fn try_from(FixedBytes(bytes): B256) -> Result<Self, Self::Error> {
        Ok(PoolConfig {
            extension: Address::from_slice(&bytes[..20]),
            fee: u64::from_be_bytes(bytes[20..28].try_into().expect("slice with correct length")),
            pool_type_config: PoolTypeConfig::try_from(B32::from_slice(&bytes[28..32]))?,
        })
    }
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

impl private::Sealed for Evm {}

#[cfg(test)]
mod tests {
    use alloy_primitives::address;

    use crate::chain::tests::ChainTest;

    use super::*;

    impl ChainTest for Evm {
        fn zero_address() -> Self::Address {
            Address::ZERO
        }

        fn one_address() -> Self::Address {
            address!("0x0000000000000000000000000000000000000001")
        }
    }

    #[test]
    fn stableswap_round_trip_positive_and_negative_ticks() {
        let cases = [
            (0, 1u8),
            (10, 26u8),
            (-1, 5u8),
            (1_000_000, 0u8),
            (-1_000_000, EVM_MAX_STABLESWAP_AMPLIFICATION_FACTOR),
        ];

        for (center_tick, amplification) in cases {
            let encoded: B32 = PoolTypeConfig::Stableswap(StableswapPoolTypeConfig {
                center_tick,
                amplification_factor: amplification,
            })
            .into();
            let decoded = PoolTypeConfig::try_from(encoded).unwrap();

            assert_eq!(
                decoded,
                PoolTypeConfig::Stableswap(StableswapPoolTypeConfig {
                    center_tick,
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
            PoolTypeConfig::try_from(b32).unwrap_err(),
            PoolTypeConfigParseError::InvalidStableswapAmplification
        );
    }

    #[test]
    fn concentrated_round_trip_and_limits() {
        let ok = [1u32, EVM_MAX_TICK_SPACING.0];

        for spacing in ok {
            let config = PoolTypeConfig::Concentrated(TickSpacing(spacing));
            let encoded: B32 = config.into();
            let decoded = PoolTypeConfig::try_from(encoded).unwrap();
            assert_eq!(decoded, PoolTypeConfig::Concentrated(TickSpacing(spacing)));
        }

        for spacing in [0u32, EVM_MAX_TICK_SPACING.0 + 1] {
            let mut spacing_bytes = spacing.to_be_bytes();
            spacing_bytes[0] |= 0x80;
            let b32 = B32::from(u32::from_be_bytes(spacing_bytes));
            assert_eq!(
                PoolTypeConfig::try_from(b32).unwrap_err(),
                PoolTypeConfigParseError::InvalidTickSpacing
            );
        }
    }
}
