use crate::{math::uint::U256, quoting::types::Pool};
use core::fmt::Debug;
use num_traits::Zero;

#[cfg(feature = "evm")]
pub mod evm;
#[cfg(feature = "starknet")]
pub mod starknet;

pub trait Chain: Sized + Clone + PartialEq + Eq + Debug {
    type Fee: Clone + Copy + PartialEq + Eq + Debug + Into<u128> + Zero + Send + Sync;

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

#[cfg(test)]
pub mod tests {
    #[derive(Clone, Copy)]
    pub enum ChainEnum {
        Starknet,
        Evm,
    }

    pub const CHAINS: [ChainEnum; 2] = [ChainEnum::Starknet, ChainEnum::Evm];

    macro_rules! run_for_all_chains {
        ($chain_ty:ident, $chain_enum:ident => $body:block) => {{
            type $chain_ty = crate::chain::starknet::Starknet;
            let $chain_enum = crate::chain::tests::ChainEnum::Starknet;
            $body
        }
        {
            type $chain_ty = crate::chain::evm::Evm;
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
