use core::fmt::Debug;

use alloc::vec;
use derive_more::From;
use num_traits::{ToPrimitive as _, Zero};

use crate::{
    math::uint::U256,
    quoting::{
        base_pool::{BasePool, BasePoolError, BasePoolState, BasePoolTypeConfig, TickSpacing},
        full_range_pool::{
            FullRangePool, FullRangePoolError, FullRangePoolState, FullRangePoolTypeConfig,
        },
        types::{Config, Pool, PoolKey, Tick},
    },
};

pub trait Chain: Sized + Clone + PartialEq + Eq + Debug {
    type Fee: Clone + Copy + PartialEq + Eq + Debug + Into<U256> + Zero + Send + Sync;
    type PoolTypeConfig;

    type FullRangePool: Pool<Self, Meta = ()>;
    type FullRangePoolError: Debug;

    fn max_tick_spacing() -> u32;

    fn min_tick() -> i32;
    fn max_tick() -> i32;

    fn min_sqrt_ratio() -> U256;
    fn max_sqrt_ratio() -> U256;

    fn min_sqrt_ratio_full_range() -> U256;
    fn max_sqrt_ratio_full_range() -> U256;

    fn adjust_sqrt_ratio_precision(sqrt_ratio: U256) -> U256;

    fn fee_denominator() -> U256;
    fn fee_bits() -> u8;

    fn new_full_range_pool(
        token0: U256,
        token1: U256,
        fee: Self::Fee,
        extension: U256,
        sqrt_ratio: U256,
        active_liquidity: u128,
    ) -> Result<Self::FullRangePool, Self::FullRangePoolError>;
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct Starknet;
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct Evm;

impl Starknet {
    pub const MAX_TICK_SPACING: u32 = 354892;

    pub const MIN_TICK: i32 = -88722883;
    pub const MAX_TICK: i32 = 88722883;
    pub const MIN_TICK_AT_MAX_TICK_SPACING: i32 = -88368108;
    pub const MAX_TICK_AT_MAX_TICK_SPACING: i32 = 88368108;

    pub const MIN_SQRT_RATIO: U256 = U256([4363438787445, 1, 0, 0]);
    pub const MAX_SQRT_RATIO: U256 = U256([
        17632034473660873000,
        8013356184008655433,
        18446739710271796309,
        0,
    ]);
    pub const MIN_SQRT_RATIO_AT_MAX_TICK_SPACING: U256 = U256([3580400339970425059, 1, 0, 0]);
    pub const MAX_SQRT_RATIO_AT_MAX_TICK_SPACING: U256 = U256([
        6538062197914670769,
        14200015713685041661,
        15448319606494512814,
        0,
    ]);

    pub const FEE_DENOMINATOR: U256 = U256([0, 0, 1, 0]);
    pub const FEE_BITS: u8 = 128;
}

impl Evm {
    pub const NATIVE_TOKEN_ADDRESS: U256 = U256::zero();

    pub const MAX_TICK_SPACING: u32 = 698605;
    pub const FULL_RANGE_TICK_SPACING: u32 = 0;

    pub const MAX_STABLESWAP_AMPLIFICATION_FACTOR: u8 = 26;

    pub const MIN_TICK: i32 = -88722835;
    pub const MAX_TICK: i32 = 88722835;

    pub const MIN_SQRT_RATIO: U256 = U256([447090492618908, 1, 0, 0]);
    pub const MAX_SQRT_RATIO: U256 = U256([0, 7567914946021818368, 18446296994052723738, 0]);

    pub const FEE_DENOMINATOR: U256 = U256([0, 1, 0, 0]);
    pub const FEE_BITS: u8 = 64;
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum StarknetFullRangePoolError {
    BasePoolError(BasePoolError),
    ActiveLiquidityDoesNotFitSignedInteger,
}

#[derive(From)]
pub enum StarknetPoolTypeConfig {
    Base(BasePoolTypeConfig),
}

impl Chain for Starknet {
    type Fee = u128;
    type PoolTypeConfig = StarknetPoolTypeConfig;
    type FullRangePool = BasePool<Self>;
    type FullRangePoolError = StarknetFullRangePoolError;

    fn max_tick_spacing() -> u32 {
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
        Self::MIN_SQRT_RATIO_AT_MAX_TICK_SPACING
    }

    fn max_sqrt_ratio_full_range() -> U256 {
        Self::MAX_SQRT_RATIO_AT_MAX_TICK_SPACING
    }

    fn adjust_sqrt_ratio_precision(sqrt_ratio: U256) -> U256 {
        sqrt_ratio
    }

    fn fee_denominator() -> U256 {
        Self::FEE_DENOMINATOR
    }

    fn fee_bits() -> u8 {
        Self::FEE_BITS
    }

    fn new_full_range_pool(
        token0: U256,
        token1: U256,
        fee: Self::Fee,
        extension: U256,
        sqrt_ratio: U256,
        active_liquidity: u128,
    ) -> Result<Self::FullRangePool, Self::FullRangePoolError> {
        let signed_liquidity: i128 = active_liquidity
            .to_i128()
            .ok_or(StarknetFullRangePoolError::ActiveLiquidityDoesNotFitSignedInteger)?;

        let (active_tick_index, sorted_ticks, liquidity) = if active_liquidity.is_zero() {
            (None, vec![], 0)
        } else {
            let (active_tick_index, liquidity) =
                if sqrt_ratio < Starknet::MIN_SQRT_RATIO_AT_MAX_TICK_SPACING {
                    (None, 0)
                } else if sqrt_ratio <= Starknet::MAX_SQRT_RATIO_AT_MAX_TICK_SPACING {
                    (Some(0), active_liquidity)
                } else {
                    (Some(1), 0)
                };
            (
                active_tick_index,
                vec![
                    Tick {
                        index: Starknet::MIN_TICK_AT_MAX_TICK_SPACING,
                        liquidity_delta: signed_liquidity,
                    },
                    Tick {
                        index: Starknet::MAX_TICK_AT_MAX_TICK_SPACING,
                        liquidity_delta: -signed_liquidity,
                    },
                ],
                liquidity,
            )
        };

        BasePool::new(
            PoolKey {
                token0,
                token1,
                config: Config {
                    fee,
                    pool_type_config: TickSpacing(Starknet::MAX_TICK_SPACING),
                    extension,
                },
            },
            BasePoolState {
                sqrt_ratio,
                liquidity,
                active_tick_index,
            },
            sorted_ticks,
        )
        .map_err(StarknetFullRangePoolError::BasePoolError)
    }
}

const TWO_POW_160: U256 = U256([0, 0, 0x100000000, 0]);
const TWO_POW_128: U256 = U256([0, 0, 1, 0]);
const TWO_POW_96: U256 = U256([0, 0x0100000000, 0, 0]);

#[derive(From)]
pub enum EvmPoolTypeConfig {
    Base(BasePoolTypeConfig),
    FullRange(FullRangePoolTypeConfig),
}

impl Chain for Evm {
    type Fee = u64;
    type FullRangePool = FullRangePool;
    type FullRangePoolError = FullRangePoolError;
    type PoolTypeConfig = EvmPoolTypeConfig;

    fn max_tick_spacing() -> u32 {
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
        token0: U256,
        token1: U256,
        fee: Self::Fee,
        extension: U256,
        sqrt_ratio: U256,
        active_liquidity: u128,
    ) -> Result<Self::FullRangePool, Self::FullRangePoolError> {
        FullRangePool::new(
            PoolKey {
                token0,
                token1,
                config: Config {
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

#[cfg(test)]
pub mod tests {
    use super::*;

    pub trait NamedChain: Chain {
        fn name() -> &'static str;
    }

    impl NamedChain for Starknet {
        fn name() -> &'static str {
            "starknet"
        }
    }

    impl NamedChain for Evm {
        fn name() -> &'static str {
            "evm"
        }
    }

    #[derive(Clone, Copy)]
    pub enum ChainEnum {
        Starknet,
        Evm,
    }

    pub const CHAINS: [ChainEnum; 2] = [ChainEnum::Starknet, ChainEnum::Evm];

    macro_rules! run_for_all_chains {
        ($chain_ty:ident, $chain_enum:ident => $body:block) => {{
            type $chain_ty = crate::chain::Starknet;
            let $chain_enum = crate::chain::tests::ChainEnum::Starknet;
            $body
        }
        {
            type $chain_ty = crate::chain::Evm;
            let $chain_enum = crate::chain::tests::ChainEnum::Evm;
            $body
        }};
    }

    macro_rules! chain_test {
        ($name:ident, $body:block) => {
            #[test]
            fn $name() {
                crate::chain::tests::run_for_all_chains!(ChainTy, _chain => $body);
            }
        };
    }

    pub(crate) use chain_test;
    pub(crate) use run_for_all_chains;
}
