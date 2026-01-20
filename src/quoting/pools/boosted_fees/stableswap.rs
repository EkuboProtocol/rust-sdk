use crate::quoting::pools::stableswap::{
    StableswapPool, StableswapPoolConfig, StableswapPoolConstructionError, StableswapPoolKey,
    StableswapPoolQuoteError, StableswapPoolResources, StableswapPoolState,
    StableswapPoolTypeConfig,
};

pub type BoostedFeesStableswapPool = StableswapPool;
pub type BoostedFeesStableswapPoolKey = StableswapPoolKey;
pub type BoostedFeesStableswapPoolConfig = StableswapPoolConfig;
pub type BoostedFeesStableswapPoolTypeConfig = StableswapPoolTypeConfig;
pub type BoostedFeesStableswapPoolState = StableswapPoolState;
pub type BoostedFeesStableswapPoolResources = StableswapPoolResources;
pub type BoostedFeesStableswapPoolConstructionError = StableswapPoolConstructionError;
pub type BoostedFeesStableswapPoolQuoteError = StableswapPoolQuoteError;
