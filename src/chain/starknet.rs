use alloc::vec;
use num_traits::{ToPrimitive as _, Zero as _};
use ruint::aliases::U256;
use starknet_types_core::felt::Felt;
use thiserror::Error;

use crate::{
    chain::Chain,
    private,
    quoting::{
        pools::base::{BasePool, BasePoolConstructionError, BasePoolState, TickSpacing},
        types::{PoolConfig, PoolKey, Tick},
    },
};

/// Chain implementation for Starknet.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub struct Starknet;

impl Starknet {
    pub const MAX_TICK_SPACING: TickSpacing = TickSpacing(354892);

    pub const MIN_TICK: i32 = -88722883;
    pub const MAX_TICK: i32 = 88722883;
    pub const MIN_TICK_AT_MAX_TICK_SPACING: i32 = -88368108;
    pub const MAX_TICK_AT_MAX_TICK_SPACING: i32 = 88368108;

    pub const MIN_SQRT_RATIO: U256 = U256::from_limbs([4363438787445, 1, 0, 0]);
    pub const MAX_SQRT_RATIO: U256 = U256::from_limbs([
        17632034473660873000,
        8013356184008655433,
        18446739710271796309,
        0,
    ]);
    pub const MIN_SQRT_RATIO_AT_MAX_TICK_SPACING: U256 =
        U256::from_limbs([3580400339970425059, 1, 0, 0]);
    pub const MAX_SQRT_RATIO_AT_MAX_TICK_SPACING: U256 = U256::from_limbs([
        6538062197914670769,
        14200015713685041661,
        15448319606494512814,
        0,
    ]);

    pub const FEE_DENOMINATOR: U256 = U256::from_limbs([0, 0, 1, 0]);
    pub const FEE_BITS: u8 = 128;
}

/// Errors constructing a Starknet full range pool from inputs.
#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, Error)]
pub enum FullRangePoolConstructionError {
    #[error("base pool error")]
    BasePoolConstructionError(#[from] BasePoolConstructionError),
    #[error("active liquidity does not fit into signed integer")]
    ActiveLiquidityDoesNotFitSignedInteger,
}

impl Chain for Starknet {
    type Fee = u128;

    type FullRangePool = BasePool<Self>;
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
        token0: Self::Address,
        token1: Self::Address,
        fee: Self::Fee,
        extension: Self::Address,
        sqrt_ratio: U256,
        active_liquidity: u128,
    ) -> Result<Self::FullRangePool, Self::FullRangePoolConstructionError> {
        let signed_liquidity = active_liquidity
            .to_i128()
            .ok_or(FullRangePoolConstructionError::ActiveLiquidityDoesNotFitSignedInteger)?;

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
                config: PoolConfig {
                    fee,
                    pool_type_config: Starknet::MAX_TICK_SPACING,
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
        .map_err(FullRangePoolConstructionError::BasePoolConstructionError)
    }

    type Address = Felt;
}

impl private::Sealed for Starknet {}

#[cfg(test)]
mod tests {
    use crate::chain::tests::ChainTest;

    use super::*;

    impl ChainTest for Starknet {
        fn zero_address() -> Self::Address {
            Felt::ZERO
        }

        fn one_address() -> Self::Address {
            Felt::ONE
        }
    }
}
