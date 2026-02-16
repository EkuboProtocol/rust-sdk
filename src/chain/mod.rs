use crate::{
    private,
    quoting::{pools::concentrated::TickSpacing, types::Pool},
};
use core::hash::Hash;
use core::{
    error::Error,
    fmt::{Debug, Display},
};
use num_traits::Zero;
use ruint::aliases::U256;

#[cfg(feature = "evm")]
pub mod evm;
#[cfg(feature = "starknet")]
pub mod starknet;

pub trait Chain:
    private::Sealed + Sized + Send + Sync + Clone + Debug + PartialEq + Eq + Hash
{
    type Address: Debug + Display + Copy + Ord + Send + Sync + Hash;
    type Fee: Debug + Display + Copy + Eq + Send + Sync + Into<u128> + Zero + Hash;

    type FullRangePool: Pool<Address = Self::Address, Fee = Self::Fee, Meta = ()>;
    type FullRangePoolConstructionError: Error;

    fn max_tick_spacing() -> TickSpacing;

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
        token0: Self::Address,
        token1: Self::Address,
        fee: Self::Fee,
        extension: Self::Address,
        sqrt_ratio: U256,
        active_liquidity: u128,
    ) -> Result<Self::FullRangePool, Self::FullRangePoolConstructionError>;
}

#[cfg(test)]
pub mod tests {
    use super::*;

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

    pub const CHAINS: [ChainEnum; 2] = [ChainEnum::Starknet, ChainEnum::Evm];

    #[derive(Clone, Copy)]
    pub enum ChainEnum {
        Starknet,
        Evm,
    }

    pub trait ChainTest: Chain {
        fn zero_address() -> Self::Address;
        fn one_address() -> Self::Address;
    }
}
