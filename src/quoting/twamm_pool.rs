use crate::math::tick::{MAX_SQRT_RATIO, MIN_SQRT_RATIO};
use crate::math::twamm::sqrt_ratio::calculate_next_sqrt_ratio;
use crate::math::uint::U256;
use crate::quoting::base_pool::{
    BasePool, BasePoolQuoteError, BasePoolResources, BasePoolState,
    MAX_SQRT_RATIO_AT_MAX_TICK_SPACING, MAX_TICK_AT_MAX_TICK_SPACING, MAX_TICK_SPACING,
    MIN_SQRT_RATIO_AT_MAX_TICK_SPACING, MIN_TICK_AT_MAX_TICK_SPACING,
};
use crate::quoting::types::{NodeKey, Pool, Quote, QuoteParams, Tick, TokenAmount};
use alloc::vec;
use alloc::vec::Vec;
use core::ops::Add;
use num_traits::ToPrimitive;

#[derive(Clone, Copy)]
pub struct TwammPoolState {
    pub base_pool_state: BasePoolState,
    pub token0_sale_rate: u128,
    pub token1_sale_rate: u128,
    pub last_execution_time: u64,
}

#[derive(Clone, Copy, Default)]
pub struct TwammPoolResources {
    pub base_pool_resources: BasePoolResources,
    pub virtual_order_seconds_executed: u32,
    pub virtual_order_delta_times_crossed: u32,
}

impl Add for TwammPoolResources {
    type Output = TwammPoolResources;

    fn add(self, rhs: Self) -> Self::Output {
        TwammPoolResources {
            base_pool_resources: self.base_pool_resources + rhs.base_pool_resources,
            virtual_order_delta_times_crossed: self.virtual_order_delta_times_crossed
                + rhs.virtual_order_delta_times_crossed,
            virtual_order_seconds_executed: self.virtual_order_seconds_executed
                + rhs.virtual_order_seconds_executed,
        }
    }
}

#[derive(Clone)]
pub struct TwammSaleRateDelta {
    pub time: u64,
    pub sale_rate_delta0: u128,
    pub sale_rate_delta1: u128,
}

pub struct TwammPool {
    base_pool: BasePool,
    liquidity: u128,
    token0_sale_rate: u128,
    token1_sale_rate: u128,
    last_execution_time: u64,
    virtual_order_deltas: Vec<TwammSaleRateDelta>,
}

impl TwammPool {
    pub fn new(
        token0: U256,
        token1: U256,
        fee: u128,
        extension: U256,
        sqrt_ratio: U256,
        liquidity: u128,
        last_execution_time: u64,
        token0_sale_rate: u128,
        token1_sale_rate: u128,
        virtual_order_deltas: Vec<TwammSaleRateDelta>,
    ) -> Self {
        let signed_liquidity: i128 = liquidity.to_i128().expect("Liquidity overflow i128");
        TwammPool {
            liquidity,
            base_pool: BasePool::new(
                NodeKey {
                    token0,
                    token1,
                    fee,
                    tick_spacing: MAX_TICK_SPACING,
                    extension,
                },
                BasePoolState {
                    sqrt_ratio,
                    liquidity,
                    active_tick_index: if sqrt_ratio < MIN_SQRT_RATIO_AT_MAX_TICK_SPACING {
                        None
                    } else if sqrt_ratio <= MAX_SQRT_RATIO_AT_MAX_TICK_SPACING {
                        Some(0)
                    } else {
                        None
                    },
                },
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
            ),
            virtual_order_deltas,
            last_execution_time,
            token0_sale_rate,
            token1_sale_rate,
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum TwammPoolQuoteError {
    ExecutionTimeExceedsBlockTime,
    FailedCalculateNextSqrtRatio,
    SaleAmountOverflow,
    BasePoolQuoteError(BasePoolQuoteError),
}

impl Pool for TwammPool {
    type Resources = TwammPoolResources;
    type State = TwammPoolState;
    type QuoteError = TwammPoolQuoteError;

    fn get_key(&self) -> NodeKey {
        self.base_pool.get_key()
    }

    fn get_state(&self) -> Self::State {
        TwammPoolState {
            base_pool_state: self.base_pool.get_state(),
            last_execution_time: self.last_execution_time,
            token0_sale_rate: self.token0_sale_rate,
            token1_sale_rate: self.token1_sale_rate,
        }
    }

    fn quote(
        &self,
        params: QuoteParams<Self::State>,
    ) -> Result<Quote<Self::Resources, Self::State>, Self::QuoteError> {
        let QuoteParams {
            token_amount,
            sqrt_ratio_limit,
            override_state,
            meta,
        } = params;

        let current_time = meta.block.time;
        let initial_state = override_state.unwrap_or_else(|| self.get_state());

        let mut next_sqrt_ratio = initial_state.base_pool_state.sqrt_ratio;
        let mut token0_sale_rate = initial_state.token0_sale_rate;
        let mut token1_sale_rate = initial_state.token1_sale_rate;
        let mut last_execution_time = initial_state.last_execution_time;

        if current_time < last_execution_time {
            return Err(TwammPoolQuoteError::ExecutionTimeExceedsBlockTime);
        }

        let mut virtual_order_delta_times_crossed = 0;
        let mut next_sale_rate_delta_index = self
            .virtual_order_deltas
            .iter()
            .position(|srd| srd.time > last_execution_time)
            .unwrap_or(self.virtual_order_deltas.len());

        let mut base_pool_state_override = override_state.map(|s| s.base_pool_state);
        let mut base_pool_execution_resources: BasePoolResources = Default::default();

        let NodeKey {
            fee,
            token0,
            token1,
            tick_spacing: _,
            extension: _,
        } = self.base_pool.get_key();

        while last_execution_time != current_time {
            let sale_rate_delta = self.virtual_order_deltas.get(next_sale_rate_delta_index);

            let next_execution_time = sale_rate_delta
                .map(|srd| srd.time.min(current_time))
                .unwrap_or(current_time);

            let time_elapsed = next_execution_time - last_execution_time;
            assert!(
                time_elapsed <= u32::MAX.into(),
                "too much time has passed since execution"
            );

            let amount0: u128 =
                ((U256::from(token0_sale_rate) * U256::from(time_elapsed)) >> 32).low_u128();
            let amount1: u128 =
                ((U256::from(token1_sale_rate) * U256::from(time_elapsed)) >> 32).low_u128();

            if amount0 > 0 && amount1 > 0 {
                let current_sqrt_ratio = next_sqrt_ratio
                    .min(MAX_SQRT_RATIO_AT_MAX_TICK_SPACING)
                    .max(MIN_SQRT_RATIO_AT_MAX_TICK_SPACING);

                next_sqrt_ratio = calculate_next_sqrt_ratio(
                    current_sqrt_ratio,
                    // we explicitly do not use the liquidity state variable, we always calculate this with active liquidity
                    self.liquidity,
                    token0_sale_rate,
                    token1_sale_rate,
                    time_elapsed as u32,
                    fee,
                )
                .ok_or(TwammPoolQuoteError::FailedCalculateNextSqrtRatio)?;

                let (token, amount) = if current_sqrt_ratio < next_sqrt_ratio {
                    (token1, amount1)
                } else {
                    (token0, amount0)
                };

                let quote = self
                    .base_pool
                    .quote(QuoteParams {
                        token_amount: TokenAmount {
                            amount: amount
                                .to_i128()
                                .ok_or(TwammPoolQuoteError::SaleAmountOverflow)?,
                            token,
                        },
                        sqrt_ratio_limit: Some(next_sqrt_ratio),
                        override_state: base_pool_state_override,
                        meta,
                    })
                    .map_err(TwammPoolQuoteError::BasePoolQuoteError)?;

                base_pool_state_override = Some(quote.state_after);
                base_pool_execution_resources =
                    base_pool_execution_resources + quote.execution_resources;
            } else if amount0 > 0 || amount1 > 0 {
                let (amount, is_token1, sqrt_ratio_limit) = if amount0 != 0 {
                    (amount0, false, MIN_SQRT_RATIO)
                } else {
                    (amount1, true, MAX_SQRT_RATIO)
                };

                let token = if is_token1 {
                    self.base_pool.get_key().token1
                } else {
                    self.base_pool.get_key().token0
                };

                let quote = self
                    .base_pool
                    .quote(QuoteParams {
                        token_amount: TokenAmount {
                            amount: amount
                                .to_i128()
                                .ok_or(TwammPoolQuoteError::SaleAmountOverflow)?,
                            token,
                        },
                        sqrt_ratio_limit: Some(sqrt_ratio_limit),
                        override_state: base_pool_state_override,
                        meta,
                    })
                    .map_err(TwammPoolQuoteError::BasePoolQuoteError)?;

                base_pool_state_override = Some(quote.state_after);
                base_pool_execution_resources =
                    base_pool_execution_resources + quote.execution_resources;

                next_sqrt_ratio = quote.state_after.sqrt_ratio;
            }

            if Some(next_execution_time) == sale_rate_delta.map(|srd| srd.time) {
                token0_sale_rate += sale_rate_delta.unwrap().sale_rate_delta0;
                token1_sale_rate += sale_rate_delta.unwrap().sale_rate_delta1;
                next_sale_rate_delta_index += 1;
                virtual_order_delta_times_crossed += 1;
            }

            last_execution_time = next_execution_time;
        }

        let final_quote = self
            .base_pool
            .quote(QuoteParams {
                token_amount,
                sqrt_ratio_limit,
                meta,
                override_state: base_pool_state_override,
            })
            .map_err(TwammPoolQuoteError::BasePoolQuoteError)?;

        Ok(Quote {
            is_price_increasing: final_quote.is_price_increasing,
            consumed_amount: final_quote.consumed_amount,
            calculated_amount: final_quote.calculated_amount,
            fees_paid: final_quote.fees_paid,
            execution_resources: TwammPoolResources {
                base_pool_resources: base_pool_execution_resources
                    + final_quote.execution_resources,
                virtual_order_seconds_executed: (current_time - initial_state.last_execution_time)
                    as u32,
                virtual_order_delta_times_crossed,
            },
            state_after: TwammPoolState {
                base_pool_state: final_quote.state_after,
                token0_sale_rate,
                token1_sale_rate,
                last_execution_time: current_time,
            },
        })
    }

    fn has_liquidity(&self) -> bool {
        self.base_pool.has_liquidity()
    }
}

#[cfg(test)]
mod tests {
    use crate::math::tick::{to_sqrt_ratio, MAX_SQRT_RATIO, MIN_SQRT_RATIO};
    use crate::math::uint::U256;
    use crate::quoting::twamm_pool::TwammPool;
    use crate::quoting::types::{Block, Pool, QuoteMeta, QuoteParams, TokenAmount};
    use alloc::vec;

    const TOKEN0: U256 = U256([1, 0, 0, 0]);
    const TOKEN1: U256 = U256([2, 0, 0, 0]);

    #[test]
    fn zero_sale_rates_quote_token0() {
        let pool = TwammPool::new(
            TOKEN0,
            TOKEN1,
            0,
            U256::one(),
            to_sqrt_ratio(1).unwrap(),
            1_000_000_000,
            0,
            0,
            0,
            vec![],
        );

        let result = pool.quote(QuoteParams {
            token_amount: TokenAmount {
                amount: 1000.into(),
                token: TOKEN0,
            },
            sqrt_ratio_limit: Some(MIN_SQRT_RATIO),
            meta: QuoteMeta {
                block: Block {
                    number: 1,
                    time: 32,
                },
            },
            override_state: None,
        });

        let quote = result.expect("Quote should succeed");

        assert_eq!(quote.calculated_amount, 999);
        assert_eq!(quote.execution_resources.virtual_order_seconds_executed, 32);
        assert_eq!(
            quote.execution_resources.virtual_order_delta_times_crossed,
            0
        );
    }

    #[test]
    fn zero_sale_rates_quote_token1() {
        let pool = TwammPool::new(
            TOKEN0,
            TOKEN1,
            0,
            U256::one(),
            to_sqrt_ratio(1).unwrap(),
            100_000,
            0,
            0,
            0,
            vec![],
        );

        let result = pool.quote(QuoteParams {
            token_amount: TokenAmount {
                amount: 1000.into(),
                token: TOKEN1,
            },
            sqrt_ratio_limit: Some(MAX_SQRT_RATIO),
            meta: QuoteMeta {
                block: Block {
                    number: 1,
                    time: 32,
                },
            },
            override_state: None,
        });

        let quote = result.expect("Quote should succeed");

        assert_eq!(quote.calculated_amount, 990);
        assert_eq!(quote.execution_resources.virtual_order_seconds_executed, 32);
        assert_eq!(
            quote.execution_resources.virtual_order_delta_times_crossed,
            0
        );
    }

    #[test]
    fn non_zero_sale_rate_token0_quote_token1() {
        let pool = TwammPool::new(
            TOKEN0,
            TOKEN1,
            0,
            U256::one(),
            to_sqrt_ratio(1).unwrap(),
            1_000_000,
            0,
            0,
            1 << 32,
            vec![],
        );

        let result = pool.quote(QuoteParams {
            token_amount: TokenAmount {
                amount: 1000.into(),
                token: TOKEN0,
            },
            sqrt_ratio_limit: Some(MIN_SQRT_RATIO),
            meta: QuoteMeta {
                block: Block {
                    number: 1,
                    time: 32,
                },
            },
            override_state: None,
        });

        let quote = result.expect("Quote should succeed");

        assert_eq!(quote.calculated_amount, 998);
        assert_eq!(quote.execution_resources.virtual_order_seconds_executed, 32);
        assert_eq!(
            quote.execution_resources.virtual_order_delta_times_crossed,
            0
        );
    }

    #[test]
    fn non_zero_sale_rate_token1_quote_token1() {
        let pool = TwammPool::new(
            TOKEN0,
            TOKEN1,
            0,
            U256::one(),
            to_sqrt_ratio(1).unwrap(),
            1_000_000,
            0,
            1 << 32,
            0,
            vec![],
        );

        let result = pool.quote(QuoteParams {
            token_amount: TokenAmount {
                amount: 1000.into(),
                token: TOKEN1,
            },
            sqrt_ratio_limit: Some(MAX_SQRT_RATIO),
            meta: QuoteMeta {
                block: Block {
                    number: 1,
                    time: 32,
                },
            },
            override_state: None,
        });

        let quote = result.expect("Quote should succeed");

        assert_eq!(
            quote.calculated_amount, /*expected calculated amount*/
            999
        );
        assert_eq!(quote.execution_resources.virtual_order_seconds_executed, 32);
        assert_eq!(
            quote.execution_resources.virtual_order_delta_times_crossed,
            0
        );
    }

    #[test]
    fn non_zero_sale_rate_token0_max_price_quote_token1() {
        let pool = TwammPool::new(
            TOKEN0,
            TOKEN1,
            0,
            U256::one(),
            MAX_SQRT_RATIO,
            1_000_000,
            0,
            0,
            1 << 32,
            vec![],
        );

        let result = pool.quote(QuoteParams {
            token_amount: TokenAmount {
                amount: 1000.into(),
                token: TOKEN1,
            },
            sqrt_ratio_limit: Some(MAX_SQRT_RATIO),
            meta: QuoteMeta {
                block: Block {
                    number: 1,
                    time: 32,
                },
            },
            override_state: None,
        });

        let quote = result.expect("Quote should succeed");

        assert_eq!(
            quote.calculated_amount, /*expected calculated amount*/
            0
        );
        assert_eq!(quote.execution_resources.virtual_order_seconds_executed, 32);
        assert_eq!(
            quote.execution_resources.virtual_order_delta_times_crossed,
            0
        );
    }
}
