use crate::math::uint::U256;
use crate::quoting::base_pool::{
    BasePool, BasePoolQuoteError, BasePoolResources, BasePoolState,
    MAX_SQRT_RATIO_AT_MAX_TICK_SPACING, MAX_TICK_AT_MAX_TICK_SPACING, MAX_TICK_SPACING,
    MIN_SQRT_RATIO_AT_MAX_TICK_SPACING, MIN_TICK_AT_MAX_TICK_SPACING,
};
use crate::quoting::types::{BlockTimestamp, NodeKey, Pool, Quote, QuoteParams, Tick};
use alloc::vec;
use core::ops::Add;
use num_traits::{ToPrimitive, Zero};

#[derive(Clone, Copy)]
pub struct OraclePoolState {
    pub base_pool_state: BasePoolState,
    pub last_snapshot_time: u64,
}

#[derive(Default, Clone, Copy)]
pub struct OraclePoolResources {
    pub base_pool_resources: BasePoolResources,
    pub snapshots_written: u32,
}

impl Add for OraclePoolResources {
    type Output = OraclePoolResources;

    fn add(self, rhs: Self) -> Self::Output {
        OraclePoolResources {
            base_pool_resources: self.base_pool_resources + rhs.base_pool_resources,
            snapshots_written: self.snapshots_written + rhs.snapshots_written,
        }
    }
}

pub struct OraclePool {
    base_pool: BasePool,
    last_snapshot_time: u64,
}

impl OraclePool {
    pub fn new(
        token0: U256,
        token1: U256,
        extension: U256,
        sqrt_ratio: U256,
        active_liquidity: u128,
        last_snapshot_time: u64,
    ) -> Self {
        let signed_liquidity: i128 = active_liquidity.to_i128().expect("Liquidity overflow i128");

        let (active_tick_index, sorted_ticks, liquidity) = if active_liquidity.is_zero() {
            (None, vec![], 0)
        } else {
            let (active_tick_index, liquidity) = if sqrt_ratio < MIN_SQRT_RATIO_AT_MAX_TICK_SPACING
            {
                (None, 0)
            } else if sqrt_ratio <= MAX_SQRT_RATIO_AT_MAX_TICK_SPACING {
                (Some(0), active_liquidity)
            } else {
                (Some(1), 0)
            };
            (
                active_tick_index,
                vec![
                    Tick {
                        index: MIN_TICK_AT_MAX_TICK_SPACING,
                        liquidity_delta: signed_liquidity,
                    },
                    Tick {
                        index: MAX_TICK_AT_MAX_TICK_SPACING,
                        liquidity_delta: -signed_liquidity,
                    },
                ],
                liquidity,
            )
        };

        OraclePool {
            base_pool: BasePool::new(
                NodeKey {
                    token0,
                    token1,
                    fee: 0,
                    tick_spacing: MAX_TICK_SPACING,
                    extension,
                },
                BasePoolState {
                    sqrt_ratio,
                    liquidity,
                    active_tick_index,
                },
                sorted_ticks,
            ),
            last_snapshot_time,
        }
    }
}

impl Pool for OraclePool {
    type Resources = OraclePoolResources;
    type State = OraclePoolState;
    type QuoteError = BasePoolQuoteError;
    type Meta = BlockTimestamp;

    fn get_key(&self) -> &NodeKey {
        self.base_pool.get_key()
    }

    fn get_state(&self) -> Self::State {
        OraclePoolState {
            base_pool_state: self.base_pool.get_state(),
            last_snapshot_time: self.last_snapshot_time,
        }
    }

    fn quote(
        &self,
        params: QuoteParams<Self::State, Self::Meta>,
    ) -> Result<Quote<Self::Resources, Self::State>, Self::QuoteError> {
        let block_time = params.meta;
        let pool_time = params
            .override_state
            .map_or(self.last_snapshot_time, |os| os.last_snapshot_time);

        let result = self.base_pool.quote(QuoteParams {
            sqrt_ratio_limit: params.sqrt_ratio_limit,
            override_state: params.override_state.map(|s| s.base_pool_state),
            token_amount: params.token_amount,
            meta: (),
        })?;

        Ok(Quote {
            calculated_amount: result.calculated_amount,
            consumed_amount: result.consumed_amount,
            execution_resources: OraclePoolResources {
                snapshots_written: if pool_time != block_time { 1 } else { 0 },
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

#[cfg(test)]
mod tests {
    use crate::math::tick::to_sqrt_ratio;
    use crate::math::uint::U256;
    use crate::quoting::base_pool::{
        MAX_SQRT_RATIO_AT_MAX_TICK_SPACING, MAX_TICK_AT_MAX_TICK_SPACING,
        MIN_SQRT_RATIO_AT_MAX_TICK_SPACING, MIN_TICK_AT_MAX_TICK_SPACING,
    };
    use crate::quoting::oracle_pool::OraclePool;
    use crate::quoting::types::{Pool, QuoteParams, TokenAmount};

    #[test]
    fn test_max_values() {
        assert_eq!(
            to_sqrt_ratio(MIN_TICK_AT_MAX_TICK_SPACING).unwrap(),
            MIN_SQRT_RATIO_AT_MAX_TICK_SPACING
        );
        assert_eq!(
            to_sqrt_ratio(MAX_TICK_AT_MAX_TICK_SPACING).unwrap(),
            MAX_SQRT_RATIO_AT_MAX_TICK_SPACING
        );
    }

    mod constructor_validation {
        use crate::math::tick::{MAX_SQRT_RATIO, MIN_SQRT_RATIO};
        use crate::math::uint::U256;
        use crate::quoting::base_pool::{
            MAX_SQRT_RATIO_AT_MAX_TICK_SPACING, MIN_SQRT_RATIO_AT_MAX_TICK_SPACING,
        };
        use crate::quoting::oracle_pool::OraclePool;
        use crate::quoting::types::Pool;

        #[test]
        fn test_max_price_constructor() {
            assert_eq!(
                OraclePool::new(
                    U256::one(),
                    U256::one() + 1,
                    U256::zero(),
                    MAX_SQRT_RATIO,
                    1,
                    0,
                )
                .get_state()
                .base_pool_state
                .liquidity,
                0
            );
        }

        #[test]
        fn test_min_price_constructor() {
            assert_eq!(
                OraclePool::new(
                    U256::one(),
                    U256::one() + 1,
                    U256::zero(),
                    MIN_SQRT_RATIO,
                    1,
                    0,
                )
                .get_state()
                .base_pool_state
                .liquidity,
                0
            );
        }

        #[test]
        fn test_min_sqrt_ratio_at_max_tick_spacing() {
            assert_eq!(
                OraclePool::new(
                    U256::one(),
                    U256::one() + 1,
                    U256::zero(),
                    MIN_SQRT_RATIO_AT_MAX_TICK_SPACING,
                    1,
                    0,
                )
                .get_state()
                .base_pool_state
                .liquidity,
                1
            );
        }

        #[test]
        fn test_max_sqrt_ratio_at_max_tick_spacing() {
            assert_eq!(
                OraclePool::new(
                    U256::one(),
                    U256::one() + 1,
                    U256::zero(),
                    MAX_SQRT_RATIO_AT_MAX_TICK_SPACING,
                    1,
                    0,
                )
                .get_state()
                .base_pool_state
                .liquidity,
                1
            );
        }
    }

    const TOKEN0: U256 = U256([1, 0, 0, 0]);
    const TOKEN1: U256 = U256([2, 0, 0, 0]);
    const EXTENSION: U256 = U256([3, 0, 0, 0]);

    #[test]
    fn test_quote_token1_input_update() {
        let pool = OraclePool::new(
            TOKEN0,
            TOKEN1,
            EXTENSION,
            to_sqrt_ratio(0).unwrap(),
            1_000_000_000,
            1,
        );

        let params = QuoteParams {
            token_amount: TokenAmount {
                amount: 1000,
                token: TOKEN1,
            },
            sqrt_ratio_limit: None,
            override_state: None,
            meta: 2,
        };

        let quote = pool.quote(params).expect("Failed to get quote");

        assert_eq!(quote.calculated_amount, 999);
        assert_eq!(quote.consumed_amount, 1000);
        assert_eq!(
            quote
                .execution_resources
                .base_pool_resources
                .initialized_ticks_crossed,
            0
        );
        assert_eq!(quote.execution_resources.snapshots_written, 1);
        assert_eq!(quote.state_after.last_snapshot_time, 2);
    }

    #[test]
    fn test_quote_token0_input() {
        let pool = OraclePool::new(
            TOKEN0,
            TOKEN1,
            EXTENSION,
            to_sqrt_ratio(0).unwrap(),
            1_000_000_000,
            1,
        );

        let params = QuoteParams {
            token_amount: TokenAmount {
                amount: 1000,
                token: TOKEN0,
            },
            sqrt_ratio_limit: None,
            override_state: None,
            meta: 2,
        };

        let quote = pool.quote(params).expect("Failed to get quote");

        assert_eq!(quote.calculated_amount, 999);
        assert_eq!(quote.consumed_amount, 1000);
        assert_eq!(
            quote
                .execution_resources
                .base_pool_resources
                .initialized_ticks_crossed,
            0
        );
        assert_eq!(quote.execution_resources.snapshots_written, 1);
        assert_eq!(quote.state_after.last_snapshot_time, 2);
    }
}
