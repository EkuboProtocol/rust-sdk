use crate::quoting::base_pool::{BasePool, BasePoolQuoteError, BasePoolResources, BasePoolState};
use crate::quoting::types::{Pool, Quote, QuoteParams};

pub struct OraclePool {
    base_pool: BasePool,
}

impl OraclePool {
    pub fn new(base_pool: BasePool) -> Self {
        OraclePool { base_pool }
    }
}

impl Pool for OraclePool {
    type Resources = BasePoolResources;
    type Error = BasePoolQuoteError;
    type State = BasePoolState;

    fn quote(
        &self,
        params: QuoteParams<Self::State>,
    ) -> Result<Quote<Self::Resources, Self::State>, Self::Error> {
        self.base_pool.quote(params)
    }

    fn has_liquidity(&self) -> bool {
        self.base_pool.has_liquidity()
    }
}
