use alloy_primitives::{aliases::B32, fixed_bytes, Address, FixedBytes, B256, U256};
use derive_more::From;
use num_traits::Zero as _;
use thiserror::Error;

use crate::{
    chain::Chain,
    private,
    quoting::{
        pools::{
            base::{BasePoolTypeConfig, TickSpacing},
            full_range::{
                FullRangePool, FullRangePoolConstructionError, FullRangePoolState,
                FullRangePoolTypeConfig,
            },
            stableswap::StableswapPoolTypeConfig,
        },
        types::{PoolConfig, PoolKey},
    },
};

/// Chain implementation for EVM-compatible networks.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub struct Evm;

impl Evm {
    pub const NATIVE_TOKEN_ADDRESS: Address = Address::ZERO;

    pub const MAX_TICK_SPACING: TickSpacing = TickSpacing(698605);
    pub const FULL_RANGE_TICK_SPACING: u32 = 0;

    pub const MAX_STABLESWAP_AMPLIFICATION_FACTOR: u8 = 26;

    pub const MIN_TICK: i32 = -88722835;
    pub const MAX_TICK: i32 = 88722835;

    pub const MIN_SQRT_RATIO: U256 = U256::from_limbs([447090492618908, 1, 0, 0]);
    pub const MAX_SQRT_RATIO: U256 =
        U256::from_limbs([0, 7567914946021818368, 18446296994052723738, 0]);

    pub const FEE_DENOMINATOR: U256 = U256::from_limbs([0, 1, 0, 0]);
    pub const FEE_BITS: u8 = 64;
}

const TWO_POW_160: U256 = U256::from_limbs([0, 0, 0x100000000, 0]);
const TWO_POW_128: U256 = U256::from_limbs([0, 0, 1, 0]);
const TWO_POW_96: U256 = U256::from_limbs([0, 0x0100000000, 0, 0]);

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

impl TryFrom<B32> for PoolTypeConfig {
    type Error = PoolTypeConfigParseError;

    fn try_from(value: B32) -> Result<Self, Self::Error> {
        if value == B32::ZERO {
            return Ok(Self::FullRange(FullRangePoolTypeConfig));
        }

        if value.bit_and(fixed_bytes!("0x80000000")) == B32::ZERO {
            let center_tick = i32::from_be_bytes((value.bit_and(fixed_bytes!("0x00ffffff"))).0);

            if center_tick < Evm::MIN_TICK || center_tick > Evm::MAX_TICK {
                return Err(PoolTypeConfigParseError::InvalidCenterTick);
            }

            let amplification_factor = value.0[0];

            if amplification_factor > Evm::MAX_STABLESWAP_AMPLIFICATION_FACTOR {
                return Err(PoolTypeConfigParseError::InvalidStableswapAmplification);
            }

            Ok(Self::Stableswap(StableswapPoolTypeConfig {
                center_tick,
                amplification_factor,
            }))
        } else {
            let tick_spacing = u32::from_be_bytes(value.bit_and(fixed_bytes!("0x7fffffff")).0);

            if tick_spacing > Evm::MAX_TICK_SPACING.0 || tick_spacing.is_zero() {
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

impl From<PoolConfig<<Evm as Chain>::Address, <Evm as Chain>::Fee, PoolTypeConfig>> for B256 {
    fn from(
        value: PoolConfig<<Evm as Chain>::Address, <Evm as Chain>::Fee, PoolTypeConfig>,
    ) -> Self {
        value
            .extension
            .0
            .concat_const::<_, 28>(FixedBytes(value.fee.to_be_bytes()))
            .concat_const(value.pool_type_config.into())
    }
}

impl Chain for Evm {
    type Address = Address;
    type Fee = u64;
    type FullRangePool = FullRangePool;
    type FullRangePoolConstructionError = FullRangePoolConstructionError;

    fn max_tick_spacing() -> TickSpacing {
        Self::MAX_TICK_SPACING
    }

    fn min_tick() -> i32 {
        Self::MIN_TICK
    }

    fn max_tick() -> i32 {
        Self::MAX_TICK
    }

    fn min_sqrt_ratio() -> U256 {
        Self::MIN_SQRT_RATIO
    }

    fn max_sqrt_ratio() -> U256 {
        Self::MAX_SQRT_RATIO
    }

    fn min_sqrt_ratio_full_range() -> U256 {
        Self::MIN_SQRT_RATIO
    }

    fn max_sqrt_ratio_full_range() -> U256 {
        Self::MAX_SQRT_RATIO
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
        Self::FEE_DENOMINATOR
    }

    fn fee_bits() -> u8 {
        Self::FEE_BITS
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
}
