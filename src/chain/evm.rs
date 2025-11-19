use ruint::aliases::U256;

use crate::{
    chain::Chain,
    quoting::{
        full_range_pool::{
            FullRangePool, FullRangePoolError, FullRangePoolState, FullRangePoolTypeConfig,
        },
        types::{Config, PoolKey},
    },
};

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct Evm;

impl Evm {
    pub const NATIVE_TOKEN_ADDRESS: U256 = U256::ZERO;

    pub const MAX_TICK_SPACING: u32 = 698605;
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

impl Chain for Evm {
    type Fee = u64;
    type FullRangePool = FullRangePool;
    type FullRangePoolError = FullRangePoolError;

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
