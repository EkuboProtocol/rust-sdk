use crate::{
    chain::{starknet::Starknet, Chain},
    quoting::pools::base::{
        BasePool, BasePoolConstructionError, BasePoolKey, BasePoolQuoteError, BasePoolResources,
        BasePoolState, BasePoolTypeConfig,
    },
    quoting::types::PoolConfig,
};

pub type SplinePool = BasePool<Starknet>;
pub type SplinePoolConfig =
    PoolConfig<<Starknet as Chain>::Address, <Starknet as Chain>::Fee, BasePoolTypeConfig>;
pub type SplinePoolConstructionError = BasePoolConstructionError;
pub type SplinePoolKey = BasePoolKey<Starknet>;
pub type SplinePoolState = BasePoolState;
pub type SplinePoolResources = BasePoolResources;
pub type SplinePoolQuoteError = BasePoolQuoteError;
