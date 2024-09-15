use crate::quoting::base_pool::{BasePool, BasePoolQuoteError, BasePoolResources, BasePoolState};
use crate::quoting::types::{Pool, Quote, QuoteParams};
use core::ops::Add;

#[derive(Clone)]
pub struct OraclePoolState {
    base_pool_state: BasePoolState,
    last_snapshot_time: u64,
}

pub struct OraclePoolResources {
    base_pool_resources: BasePoolResources,
    snapshot_updated: bool,
}

impl Default for OraclePoolResources {
    fn default() -> Self {
        OraclePoolResources {
            base_pool_resources: Default::default(),
            snapshot_updated: false,
        }
    }
}

impl Add for OraclePoolResources {
    type Output = OraclePoolResources;

    fn add(self, rhs: Self) -> Self::Output {
        OraclePoolResources {
            base_pool_resources: self.base_pool_resources + rhs.base_pool_resources,
            snapshot_updated: self.snapshot_updated || rhs.snapshot_updated,
        }
    }
}

impl OraclePool {
    pub fn new(base_pool: BasePool, last_snapshot_time: u64) -> Self {
        OraclePool {
            base_pool,
            last_snapshot_time,
        }
    }
}

pub struct OraclePool {
    base_pool: BasePool,
    last_snapshot_time: u64,
}

impl Pool for OraclePool {
    type Resources = OraclePoolResources;
    type Error = BasePoolQuoteError;
    type State = OraclePoolState;

    fn quote(
        &self,
        params: QuoteParams<Self::State>,
    ) -> Result<Quote<Self::Resources, Self::State>, Self::Error> {
        let block_time = params.meta.block.time;
        let pool_time = params
            .override_state
            .clone()
            .map_or(self.last_snapshot_time, |os| os.last_snapshot_time);

        let result = self.base_pool.quote(QuoteParams {
            sqrt_ratio_limit: params.sqrt_ratio_limit,
            meta: params.meta,
            override_state: params.override_state.map(|s| s.base_pool_state),
            token_amount: params.token_amount,
        })?;

        Ok(Quote {
            calculated_amount: result.calculated_amount,
            consumed_amount: result.consumed_amount,
            execution_resources: OraclePoolResources {
                snapshot_updated: pool_time != block_time,
                base_pool_resources: result.execution_resources,
            },
            fees_paid: result.fees_paid,
            is_price_increasing: result.is_price_increasing,
            state_after: OraclePoolState {
                base_pool_state: result.state_after,
                last_snapshot_time: block_time,
            },
        })
    }

    fn has_liquidity(&self) -> bool {
        self.base_pool.has_liquidity()
    }
}
