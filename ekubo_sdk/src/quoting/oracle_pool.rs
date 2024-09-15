use crate::quoting::base_pool::BasePool;
use crate::quoting::types::{Pool, Quote, QuoteError, QuoteParams};

pub struct OraclePool {
    base_pool: BasePool,
}

impl OraclePool {
    pub fn new(base_pool: BasePool) -> Self {
        OraclePool { base_pool }
    }
}

impl Pool for OraclePool {
    fn quote(&self, params: QuoteParams) -> Result<Quote, QuoteError> {
        self.base_pool.quote(params)
    }

    fn has_liquidity(&self) -> bool {
        self.base_pool.has_liquidity()
    }
}
