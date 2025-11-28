use crate::{
    chain::starknet::Starknet,
    quoting::pools::base::{BasePool, BasePoolQuoteError, BasePoolResources, BasePoolState},
};

pub type SplinePool = BasePool<Starknet>;
pub type SplinePoolState = BasePoolState;
pub type SplinePoolResources = BasePoolResources;
pub type SplinePoolQuoteError = BasePoolQuoteError;
