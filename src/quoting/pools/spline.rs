use crate::{
    chain::{starknet::Starknet, Chain},
    quoting::pools::concentrated::{
        ConcentratedPool, ConcentratedPoolConstructionError, ConcentratedPoolKey,
        ConcentratedPoolQuoteError, ConcentratedPoolResources, ConcentratedPoolState,
        ConcentratedPoolTypeConfig,
    },
    quoting::types::PoolConfig,
};

pub type SplinePool = ConcentratedPool<Starknet>;
pub type SplinePoolConfig =
    PoolConfig<<Starknet as Chain>::Address, <Starknet as Chain>::Fee, ConcentratedPoolTypeConfig>;
pub type SplinePoolConstructionError = ConcentratedPoolConstructionError;
pub type SplinePoolKey = ConcentratedPoolKey<Starknet>;
pub type SplinePoolState = ConcentratedPoolState;
pub type SplinePoolResources = ConcentratedPoolResources;
pub type SplinePoolQuoteError = ConcentratedPoolQuoteError;
