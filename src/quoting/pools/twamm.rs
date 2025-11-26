use crate::quoting::types::{BlockTimestamp, PoolConfig};
use crate::quoting::types::{Pool, PoolKey, Quote, QuoteParams, TokenAmount};
use crate::{chain::Chain, math::twamm::sqrt_ratio::calculate_next_sqrt_ratio};
use crate::{private, quoting::types::PoolState};

use alloc::vec::Vec;
use derive_more::{Add, AddAssign, Sub, SubAssign};
use num_traits::{ToPrimitive, Zero};
use ruint::aliases::U256;
use thiserror::Error;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct TwammPool<C: Chain> {
    full_range_pool: C::FullRangePool,
    active_liquidity: u128,
    token0_sale_rate: u128,
    token1_sale_rate: u128,
    last_execution_time: u64,
    virtual_order_deltas: Vec<TwammSaleRateDelta>,
}

pub type TwammPoolKey<C> = PoolKey<
    <C as Chain>::Address,
    <C as Chain>::Fee,
    <<C as Chain>::FullRangePool as Pool>::PoolTypeConfig,
>;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct TwammPoolState<S> {
    pub full_range_pool_state: S,
    pub token0_sale_rate: u128,
    pub token1_sale_rate: u128,
    pub last_execution_time: u64,
}

#[derive(Clone, Debug, Copy, Default, PartialEq, Eq, Hash, Add, AddAssign, Sub, SubAssign)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct TwammPoolResources<R> {
    pub full_range_pool_resources: R,
    /// The number of seconds that passed since the last virtual order execution
    pub virtual_order_seconds_executed: u32,
    /// The amount of order updates that were applied to the sale rate
    pub virtual_order_delta_times_crossed: u32,
    /// Whether the virtual orders were executed or not (for a single swap, 1 or 0)
    pub virtual_orders_executed: u32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct TwammSaleRateDelta {
    pub time: u64,
    pub sale_rate_delta0: i128,
    pub sale_rate_delta1: i128,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, Error)]
pub enum TwammPoolConstructionError<E> {
    #[error("full range pool error")]
    /// Errors from the underlying full range pool constructor.
    FullRangePoolError(#[from] E),
    #[error("sale rate deltas not ordered or not greater than last execution time")]
    /// Sale rate deltas are not ordered or not greater than last_execution_time.
    SaleRateDeltasInvalid,
    #[error("sale rate delta overflow or underflow")]
    /// Sale rate deltas overflow or underflow at some point
    SaleRateDeltasOverflowOrUnderflow,
    #[error("sale rate delta sum non-zero")]
    /// Sum of current sale rate and sale rate deltas must be zero.
    SaleRateDeltaSumNonZero,
}

impl<C: Chain> TwammPool<C> {
    pub fn new(
        token0: C::Address,
        token1: C::Address,
        fee: C::Fee,
        extension: C::Address,
        sqrt_ratio: U256,
        active_liquidity: u128,
        last_execution_time: u64,
        token0_sale_rate: u128,
        token1_sale_rate: u128,
        virtual_order_deltas: Vec<TwammSaleRateDelta>,
    ) -> Result<Self, TwammPoolConstructionError<C::FullRangePoolConstructionError>> {
        let mut last_time = last_execution_time;
        let mut sr0: u128 = token0_sale_rate;
        let mut sr1: u128 = token1_sale_rate;

        for t in virtual_order_deltas.iter() {
            if t.time <= last_time {
                return Err(TwammPoolConstructionError::SaleRateDeltasInvalid);
            }
            last_time = t.time;

            sr0 = if t.sale_rate_delta0 < 0 {
                sr0.checked_sub(t.sale_rate_delta0.unsigned_abs())
            } else {
                sr0.checked_add(t.sale_rate_delta0.unsigned_abs())
            }
            .ok_or(TwammPoolConstructionError::SaleRateDeltasOverflowOrUnderflow)?;

            sr1 = if t.sale_rate_delta1 < 0 {
                sr1.checked_sub(t.sale_rate_delta1.unsigned_abs())
            } else {
                sr1.checked_add(t.sale_rate_delta1.unsigned_abs())
            }
            .ok_or(TwammPoolConstructionError::SaleRateDeltasOverflowOrUnderflow)?;
        }

        if !(sr0.is_zero() && sr1.is_zero()) {
            return Err(TwammPoolConstructionError::SaleRateDeltaSumNonZero);
        }

        // we just force the pool state to always be within the bounds of min/max to simplify the state
        // this does not change accuracy of quote results
        // it just reduces accuracy of resource estimations in extreme cases by a negligible amount.
        let sqrt_ratio = sqrt_ratio.clamp(
            C::min_sqrt_ratio_full_range(),
            C::max_sqrt_ratio_full_range(),
        );

        Ok(TwammPool {
            active_liquidity,
            full_range_pool: C::new_full_range_pool(
                token0,
                token1,
                fee,
                extension,
                sqrt_ratio,
                active_liquidity,
            )
            .map_err(TwammPoolConstructionError::FullRangePoolError)?,
            virtual_order_deltas,
            last_execution_time,
            token0_sale_rate,
            token1_sale_rate,
        })
    }

    /// Returns the list of sale rate deltas
    pub fn sale_rate_deltas(&self) -> &Vec<TwammSaleRateDelta> {
        &self.virtual_order_deltas
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, Error)]
pub enum TwammPoolQuoteError<E> {
    #[error("execution time exceeds block time")]
    ExecutionTimeExceedsBlockTime,
    #[error("next price calculation failed")]
    FailedCalculateNextSqrtRatio,
    #[error("sale amount overflow")]
    SaleAmountOverflow,
    #[error("too much time passed since last execution")]
    TooMuchTimePassedSinceLastExecution,
    #[error("full range quote error")]
    FullRangeQuoteError(#[from] E),
}

impl<C: Chain> Pool for TwammPool<C> {
    type Address = C::Address;
    type Fee = C::Fee;
    type PoolTypeConfig = <C::FullRangePool as Pool>::PoolTypeConfig;
    type State = TwammPoolState<<C::FullRangePool as Pool>::State>;
    type Resources = TwammPoolResources<<C::FullRangePool as Pool>::Resources>;

    type QuoteError = TwammPoolQuoteError<<C::FullRangePool as Pool>::QuoteError>;
    type Meta = BlockTimestamp;

    fn key(&self) -> TwammPoolKey<C> {
        self.full_range_pool.key()
    }

    fn state(&self) -> Self::State {
        TwammPoolState {
            full_range_pool_state: self.full_range_pool.state(),
            last_execution_time: self.last_execution_time,
            token0_sale_rate: self.token0_sale_rate,
            token1_sale_rate: self.token1_sale_rate,
        }
    }

    fn quote(
        &self,
        params: QuoteParams<Self::Address, Self::State, Self::Meta>,
    ) -> Result<Quote<Self::Resources, Self::State>, Self::QuoteError> {
        let QuoteParams {
            token_amount,
            sqrt_ratio_limit,
            override_state,
            meta,
        } = params;

        let current_time = meta;
        let initial_state = override_state.unwrap_or_else(|| self.state());

        let mut next_sqrt_ratio = initial_state.full_range_pool_state.sqrt_ratio();
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

        let mut full_range_pool_state_override = override_state.map(|s| s.full_range_pool_state);
        let mut full_range_pool_execution_resources =
            <C::FullRangePool as Pool>::Resources::default();

        let PoolKey {
            token0,
            token1,
            config: PoolConfig { fee, .. },
        } = self.full_range_pool.key();

        while last_execution_time != current_time {
            let sale_rate_delta = self.virtual_order_deltas.get(next_sale_rate_delta_index);

            let next_execution_time = sale_rate_delta
                .map(|srd| srd.time.min(current_time))
                .unwrap_or(current_time);

            let time_elapsed = next_execution_time - last_execution_time;
            if time_elapsed > u32::MAX.into() {
                return Err(TwammPoolQuoteError::TooMuchTimePassedSinceLastExecution);
            }

            // we know this will never overflow because token0_sale_rate is a u128 and time_elapsed is a u32
            let amount0: u128 =
                u128::try_from((U256::from(token0_sale_rate) * U256::from(time_elapsed)) >> 32)
                    .expect("sale rate delta fits in u128");
            let amount1: u128 =
                u128::try_from((U256::from(token1_sale_rate) * U256::from(time_elapsed)) >> 32)
                    .expect("sale rate delta fits in u128");

            if amount0 > 0 && amount1 > 0 {
                let current_sqrt_ratio = next_sqrt_ratio.clamp(
                    C::min_sqrt_ratio_full_range(),
                    C::max_sqrt_ratio_full_range(),
                );

                next_sqrt_ratio = calculate_next_sqrt_ratio::<C>(
                    current_sqrt_ratio,
                    // we explicitly do not use the liquidity state variable, we always calculate this with active liquidity
                    self.active_liquidity,
                    token0_sale_rate,
                    token1_sale_rate,
                    time_elapsed as u32,
                    fee,
                );

                let (token, amount) = if current_sqrt_ratio < next_sqrt_ratio {
                    (token1, amount1)
                } else {
                    (token0, amount0)
                };

                let quote = self
                    .full_range_pool
                    .quote(QuoteParams {
                        token_amount: TokenAmount {
                            amount: amount
                                .to_i128()
                                .ok_or(TwammPoolQuoteError::SaleAmountOverflow)?,
                            token,
                        },
                        sqrt_ratio_limit: Some(next_sqrt_ratio),
                        override_state: full_range_pool_state_override,
                        meta: (),
                    })
                    .map_err(TwammPoolQuoteError::FullRangeQuoteError)?;

                full_range_pool_state_override = Some(quote.state_after);
                full_range_pool_execution_resources += quote.execution_resources;
            } else if amount0 > 0 || amount1 > 0 {
                let (amount, is_token1, sqrt_ratio_limit) = if amount0 != 0 {
                    (amount0, false, C::min_sqrt_ratio_full_range())
                } else {
                    (amount1, true, C::max_sqrt_ratio_full_range())
                };

                let token = if is_token1 {
                    self.full_range_pool.key().token1
                } else {
                    self.full_range_pool.key().token0
                };

                let quote = self
                    .full_range_pool
                    .quote(QuoteParams {
                        token_amount: TokenAmount {
                            amount: amount
                                .to_i128()
                                .ok_or(TwammPoolQuoteError::SaleAmountOverflow)?,
                            token,
                        },
                        sqrt_ratio_limit: Some(sqrt_ratio_limit),
                        override_state: full_range_pool_state_override,
                        meta: (),
                    })
                    .map_err(TwammPoolQuoteError::FullRangeQuoteError)?;

                full_range_pool_state_override = Some(quote.state_after);
                full_range_pool_execution_resources += quote.execution_resources;

                next_sqrt_ratio = quote.state_after.sqrt_ratio();
            }

            if let Some(next_delta) = sale_rate_delta {
                if next_delta.time == next_execution_time {
                    token0_sale_rate = if next_delta.sale_rate_delta0 < 0 {
                        token0_sale_rate - next_delta.sale_rate_delta0.unsigned_abs()
                    } else {
                        token0_sale_rate + next_delta.sale_rate_delta0.unsigned_abs()
                    };
                    token1_sale_rate = if next_delta.sale_rate_delta1 < 0 {
                        token1_sale_rate - next_delta.sale_rate_delta1.unsigned_abs()
                    } else {
                        token1_sale_rate + next_delta.sale_rate_delta1.unsigned_abs()
                    };
                    next_sale_rate_delta_index += 1;
                    virtual_order_delta_times_crossed += 1;
                }
            }

            last_execution_time = next_execution_time;
        }

        let final_quote = self
            .full_range_pool
            .quote(QuoteParams {
                token_amount,
                sqrt_ratio_limit,
                meta: (),
                override_state: full_range_pool_state_override,
            })
            .map_err(TwammPoolQuoteError::FullRangeQuoteError)?;

        Ok(Quote {
            is_price_increasing: final_quote.is_price_increasing,
            consumed_amount: final_quote.consumed_amount,
            calculated_amount: final_quote.calculated_amount,
            fees_paid: final_quote.fees_paid,
            execution_resources: TwammPoolResources {
                full_range_pool_resources: full_range_pool_execution_resources
                    + final_quote.execution_resources,
                virtual_order_seconds_executed: (current_time - initial_state.last_execution_time)
                    as u32,
                virtual_order_delta_times_crossed,
                virtual_orders_executed: if current_time > initial_state.last_execution_time {
                    1
                } else {
                    0
                },
            },
            state_after: TwammPoolState {
                full_range_pool_state: final_quote.state_after,
                token0_sale_rate,
                token1_sale_rate,
                last_execution_time: current_time,
            },
        })
    }

    fn has_liquidity(&self) -> bool {
        !self.active_liquidity.is_zero()
    }

    fn max_tick_with_liquidity(&self) -> Option<i32> {
        self.full_range_pool.max_tick_with_liquidity()
    }

    fn min_tick_with_liquidity(&self) -> Option<i32> {
        self.full_range_pool.min_tick_with_liquidity()
    }

    fn is_path_dependent(&self) -> bool {
        false
    }
}

impl<S: PoolState> PoolState for TwammPoolState<S> {
    fn sqrt_ratio(&self) -> U256 {
        self.full_range_pool_state.sqrt_ratio()
    }

    fn liquidity(&self) -> u128 {
        self.full_range_pool_state.liquidity()
    }
}

impl<C: Chain> private::Sealed for TwammPool<C> {}
impl<S: PoolState> private::Sealed for TwammPoolState<S> {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        chain::{
            evm::Evm,
            tests::{run_for_all_chains, ChainEnum, ChainTest},
        },
        math::tick::to_sqrt_ratio,
        quoting::types::{Pool, QuoteParams, TokenAmount},
    };
    use alloc::vec;
    use num_traits::Zero;

    fn zero_fee<C: Chain>() -> C::Fee {
        C::Fee::zero()
    }

    fn try_build_pool<C: ChainTest>(
        sqrt_ratio: U256,
        liquidity: u128,
        last_execution_time: u64,
        token0_sale_rate: u128,
        token1_sale_rate: u128,
        deltas: Vec<TwammSaleRateDelta>,
    ) -> Result<TwammPool<C>, TwammPoolConstructionError<C::FullRangePoolConstructionError>> {
        TwammPool::new(
            C::zero_address(),
            C::one_address(),
            zero_fee::<C>(),
            C::one_address(),
            sqrt_ratio,
            liquidity,
            last_execution_time,
            token0_sale_rate,
            token1_sale_rate,
            deltas,
        )
    }

    fn build_pool<C: ChainTest>(
        sqrt_ratio: U256,
        liquidity: u128,
        last_execution_time: u64,
        token0_sale_rate: u128,
        token1_sale_rate: u128,
        deltas: Vec<TwammSaleRateDelta>,
    ) -> TwammPool<C> {
        try_build_pool(
            sqrt_ratio,
            liquidity,
            last_execution_time,
            token0_sale_rate,
            token1_sale_rate,
            deltas,
        )
        .unwrap()
    }

    fn min_ratio<C: Chain>() -> U256 {
        C::min_sqrt_ratio_full_range()
    }

    fn max_ratio<C: Chain>() -> U256 {
        C::max_sqrt_ratio_full_range()
    }

    macro_rules! chain_test {
        ($name:ident, |$chain:ident| $body:block) => {
            #[test]
            fn $name() {
                run_for_all_chains!(ChainTy, chain_enum => {
                    let $chain = chain_enum;
                    $body
                });
            }
        };
        ($name:ident, $body:block) => {
            #[test]
            fn $name() {
                run_for_all_chains!(ChainTy, _chain => $body);
            }
        };
    }

    mod constructor_validation {
        use super::*;

        chain_test!(max_price_constructor, {
            let pool = build_pool::<ChainTy>(max_ratio::<ChainTy>(), 1, 0, 0, 0, vec![]);
            assert_eq!(pool.state().full_range_pool_state.liquidity, 1);
        });

        chain_test!(min_price_constructor, {
            let pool = build_pool::<ChainTy>(min_ratio::<ChainTy>(), 1, 0, 0, 0, vec![]);
            assert_eq!(pool.state().full_range_pool_state.liquidity, 1);
        });

        chain_test!(sale_rate_deltas_must_exceed_last_execution_time, {
            let result = try_build_pool::<ChainTy>(
                max_ratio::<ChainTy>(),
                1,
                0,
                0,
                0,
                vec![TwammSaleRateDelta {
                    time: 0,
                    sale_rate_delta0: 0,
                    sale_rate_delta1: 0,
                }],
            );
            assert!(matches!(
                result.unwrap_err(),
                TwammPoolConstructionError::SaleRateDeltasInvalid
            ));
        });

        chain_test!(sale_rate_deltas_must_be_ordered, {
            let result = try_build_pool::<ChainTy>(
                max_ratio::<ChainTy>(),
                1,
                0,
                0,
                0,
                vec![
                    TwammSaleRateDelta {
                        time: 2,
                        sale_rate_delta0: 0,
                        sale_rate_delta1: 0,
                    },
                    TwammSaleRateDelta {
                        time: 1,
                        sale_rate_delta0: 0,
                        sale_rate_delta1: 0,
                    },
                ],
            );
            assert!(matches!(
                result.unwrap_err(),
                TwammPoolConstructionError::SaleRateDeltasInvalid
            ));
        });

        chain_test!(sale_rate_deltas_must_sum_to_zero, {
            let result = try_build_pool::<ChainTy>(
                max_ratio::<ChainTy>(),
                1,
                0,
                54,
                2,
                vec![
                    TwammSaleRateDelta {
                        time: 1,
                        sale_rate_delta0: 0,
                        sale_rate_delta1: 1,
                    },
                    TwammSaleRateDelta {
                        time: 2,
                        sale_rate_delta0: 1,
                        sale_rate_delta1: 0,
                    },
                ],
            );
            assert!(matches!(
                result.unwrap_err(),
                TwammPoolConstructionError::SaleRateDeltaSumNonZero
            ));
        });

        chain_test!(sale_rate_deltas_sum_to_zero, {
            build_pool::<ChainTy>(
                max_ratio::<ChainTy>(),
                1,
                0,
                23,
                35,
                vec![
                    TwammSaleRateDelta {
                        time: 1,
                        sale_rate_delta0: -23,
                        sale_rate_delta1: 0,
                    },
                    TwammSaleRateDelta {
                        time: 2,
                        sale_rate_delta0: 0,
                        sale_rate_delta1: -35,
                    },
                ],
            );
        });
    }

    chain_test!(zero_sale_rates_quote_token0, {
        let pool = build_pool::<ChainTy>(
            to_sqrt_ratio::<ChainTy>(1).unwrap(),
            1_000_000_000,
            0,
            0,
            0,
            vec![],
        );

        let quote = pool
            .quote(QuoteParams {
                token_amount: TokenAmount {
                    amount: 1000.into(),
                    token: ChainTy::zero_address(),
                },
                sqrt_ratio_limit: Some(min_ratio::<ChainTy>()),
                meta: 32,
                override_state: None,
            })
            .unwrap();

        assert_eq!(
            (
                quote.calculated_amount,
                quote.execution_resources.virtual_order_seconds_executed,
                quote.execution_resources.virtual_order_delta_times_crossed
            ),
            (999, 32, 0)
        );
    });

    chain_test!(zero_sale_rates_quote_token1, {
        let pool = build_pool::<ChainTy>(
            to_sqrt_ratio::<ChainTy>(1).unwrap(),
            100_000,
            0,
            0,
            0,
            vec![],
        );

        let quote = pool
            .quote(QuoteParams {
                token_amount: TokenAmount {
                    amount: 1000,
                    token: ChainTy::one_address(),
                },
                sqrt_ratio_limit: None,
                meta: 32,
                override_state: None,
            })
            .unwrap();

        assert_eq!(
            (
                quote.calculated_amount,
                quote.execution_resources.virtual_order_seconds_executed,
                quote.execution_resources.virtual_order_delta_times_crossed
            ),
            (990, 32, 0)
        );
    });

    chain_test!(non_zero_sale_rate_token0_quote_token1, {
        let pool = build_pool::<ChainTy>(
            to_sqrt_ratio::<ChainTy>(1).unwrap(),
            1_000_000,
            0,
            0,
            1 << 32,
            vec![TwammSaleRateDelta {
                time: u64::MAX,
                sale_rate_delta0: 0,
                sale_rate_delta1: -(1 << 32),
            }],
        );

        let quote = pool
            .quote(QuoteParams {
                token_amount: TokenAmount {
                    amount: 1000.into(),
                    token: ChainTy::zero_address(),
                },
                sqrt_ratio_limit: None,
                meta: 32,
                override_state: None,
            })
            .unwrap();

        assert_eq!(
            (
                quote.calculated_amount,
                quote.execution_resources.virtual_order_seconds_executed,
                quote.execution_resources.virtual_order_delta_times_crossed
            ),
            (998, 32, 0)
        );
    });

    chain_test!(non_zero_sale_rate_token1_quote_token1, {
        let pool = build_pool::<ChainTy>(
            to_sqrt_ratio::<ChainTy>(1).unwrap(),
            1_000_000,
            0,
            1 << 32,
            0,
            vec![TwammSaleRateDelta {
                time: u64::MAX,
                sale_rate_delta0: -(1 << 32),
                sale_rate_delta1: 0,
            }],
        );

        let quote = pool
            .quote(QuoteParams {
                token_amount: TokenAmount {
                    amount: 1000.into(),
                    token: ChainTy::one_address(),
                },
                sqrt_ratio_limit: Some(max_ratio::<ChainTy>()),
                meta: 32,
                override_state: None,
            })
            .unwrap();

        assert_eq!(
            (
                quote.calculated_amount,
                quote.execution_resources.virtual_order_seconds_executed,
                quote.execution_resources.virtual_order_delta_times_crossed
            ),
            (999, 32, 0)
        );
    });

    chain_test!(non_zero_sale_rate_token0_max_price_quote_token1, {
        let pool = build_pool::<ChainTy>(
            max_ratio::<ChainTy>(),
            1_000_000,
            0,
            0,
            1 << 32,
            vec![TwammSaleRateDelta {
                time: u64::MAX,
                sale_rate_delta0: 0,
                sale_rate_delta1: -(1 << 32),
            }],
        );

        let quote = pool
            .quote(QuoteParams {
                token_amount: TokenAmount {
                    amount: 1000.into(),
                    token: ChainTy::one_address(),
                },
                sqrt_ratio_limit: Some(max_ratio::<ChainTy>()),
                meta: 32,
                override_state: None,
            })
            .unwrap();

        assert_eq!(
            (
                quote.calculated_amount,
                quote.execution_resources.virtual_order_seconds_executed,
                quote.execution_resources.virtual_order_delta_times_crossed
            ),
            (0, 32, 0)
        );
    });
    chain_test!(
        zero_sale_rate_token0_close_to_max_usable_price_deltas_move_to_usable_price_quote_token1,
        {
            let pool = build_pool::<ChainTy>(
                max_ratio::<ChainTy>() + U256::ONE,
                1_000_000,
                0,
                0,
                1 << 32,
                vec![
                    TwammSaleRateDelta {
                        sale_rate_delta0: 100_000i128 * (1 << 32),
                        sale_rate_delta1: 0,
                        time: 16,
                    },
                    TwammSaleRateDelta {
                        time: u64::MAX,
                        sale_rate_delta0: -100_000 * (1 << 32),
                        sale_rate_delta1: -(1 << 32),
                    },
                ],
            );

            let quote = pool
                .quote(QuoteParams {
                    token_amount: TokenAmount {
                        amount: 1000,
                        token: ChainTy::one_address(),
                    },
                    meta: 32,
                    sqrt_ratio_limit: None,
                    override_state: None,
                })
                .unwrap();

            assert_eq!(
                (
                    quote.calculated_amount,
                    quote.execution_resources.virtual_order_seconds_executed,
                    quote.execution_resources.virtual_order_delta_times_crossed
                ),
                (2555, 32, 1)
            );
        }
    );

    chain_test!(
        zero_sale_rate_token1_close_to_min_usable_price_deltas_move_to_usable_price_quote_token1,
        {
            let pool = build_pool::<ChainTy>(
                min_ratio::<ChainTy>(),
                1_000_000,
                0,
                1 << 32,
                0,
                vec![
                    TwammSaleRateDelta {
                        sale_rate_delta0: 0,
                        sale_rate_delta1: 100_000 * (1 << 32),
                        time: 16,
                    },
                    TwammSaleRateDelta {
                        time: u64::MAX,
                        sale_rate_delta0: -(1 << 32),
                        sale_rate_delta1: -100_000 * (1 << 32),
                    },
                ],
            );

            let quote = pool
                .quote(QuoteParams {
                    token_amount: TokenAmount {
                        amount: 1000,
                        token: ChainTy::one_address(),
                    },
                    meta: 32,
                    sqrt_ratio_limit: None,
                    override_state: None,
                })
                .unwrap();

            assert_eq!(
                (
                    quote.calculated_amount,
                    quote.execution_resources.virtual_order_seconds_executed,
                    quote.execution_resources.virtual_order_delta_times_crossed
                ),
                (390, 32, 1)
            );
        }
    );

    chain_test!(
        zero_sale_rate_token0_close_to_max_usable_price_deltas_move_to_usable_price_quote_token0,
        {
            let pool = build_pool::<ChainTy>(
                max_ratio::<ChainTy>(),
                1_000_000,
                0,
                0,
                1 << 32,
                vec![
                    TwammSaleRateDelta {
                        sale_rate_delta0: 100_000 * (1 << 32),
                        sale_rate_delta1: 0,
                        time: 16,
                    },
                    TwammSaleRateDelta {
                        time: u64::MAX,
                        sale_rate_delta0: -100_000 * (1 << 32),
                        sale_rate_delta1: -(1 << 32),
                    },
                ],
            );

            let quote = pool
                .quote(QuoteParams {
                    token_amount: TokenAmount {
                        amount: 1000,
                        token: ChainTy::zero_address(),
                    },
                    meta: 32,
                    sqrt_ratio_limit: None,
                    override_state: None,
                })
                .unwrap();

            assert_eq!(
                (
                    quote.calculated_amount,
                    quote.execution_resources.virtual_order_seconds_executed,
                    quote.execution_resources.virtual_order_delta_times_crossed
                ),
                (390, 32, 1)
            );
        }
    );

    chain_test!(
        zero_sale_rate_token1_close_to_min_usable_price_deltas_move_to_usable_price_quote_token0,
        {
            let pool = build_pool::<ChainTy>(
                min_ratio::<ChainTy>(),
                1_000_000,
                0,
                1 << 32,
                0,
                vec![
                    TwammSaleRateDelta {
                        sale_rate_delta0: 0,
                        sale_rate_delta1: 100_000 * (1 << 32),
                        time: 16,
                    },
                    TwammSaleRateDelta {
                        time: u64::MAX,
                        sale_rate_delta0: -(1 << 32),
                        sale_rate_delta1: -100_000 * (1 << 32),
                    },
                ],
            );

            let quote = pool
                .quote(QuoteParams {
                    token_amount: TokenAmount {
                        amount: 1000,
                        token: ChainTy::zero_address(),
                    },
                    meta: 32,
                    sqrt_ratio_limit: None,
                    override_state: None,
                })
                .unwrap();

            assert_eq!(
                (
                    quote.calculated_amount,
                    quote.execution_resources.virtual_order_seconds_executed,
                    quote.execution_resources.virtual_order_delta_times_crossed
                ),
                (2555, 32, 1)
            );
        }
    );

    chain_test!(one_e18_sale_rates_no_sale_rate_deltas_quote_token1, {
        let pool = build_pool::<ChainTy>(
            to_sqrt_ratio::<ChainTy>(1).unwrap(),
            100_000,
            0,
            1 << 32,
            1 << 32,
            vec![TwammSaleRateDelta {
                time: u64::MAX,
                sale_rate_delta0: -(1 << 32),
                sale_rate_delta1: -(1 << 32),
            }],
        );

        let quote = pool
            .quote(QuoteParams {
                token_amount: TokenAmount {
                    amount: 1000,
                    token: ChainTy::one_address(),
                },
                sqrt_ratio_limit: None,
                meta: 32,
                override_state: None,
            })
            .unwrap();

        assert_eq!(
            (
                quote.calculated_amount,
                quote.execution_resources.virtual_order_seconds_executed,
                quote.execution_resources.virtual_order_delta_times_crossed
            ),
            (990, 32, 0)
        );
    });

    chain_test!(one_e18_sale_rates_no_sale_rate_deltas_quote_token0, {
        let pool = build_pool::<ChainTy>(
            to_sqrt_ratio::<ChainTy>(1).unwrap(),
            100_000,
            0,
            1 << 32,
            1 << 32,
            vec![TwammSaleRateDelta {
                time: u64::MAX,
                sale_rate_delta0: -(1 << 32),
                sale_rate_delta1: -(1 << 32),
            }],
        );

        let quote = pool
            .quote(QuoteParams {
                token_amount: TokenAmount {
                    amount: 1000,
                    token: ChainTy::zero_address(),
                },
                sqrt_ratio_limit: None,
                meta: 32,
                override_state: None,
            })
            .unwrap();

        assert_eq!(
            (
                quote.calculated_amount,
                quote.execution_resources.virtual_order_seconds_executed,
                quote.execution_resources.virtual_order_delta_times_crossed
            ),
            (989, 32, 0)
        );
    });

    chain_test!(
        token0_sale_rate_greater_than_token1_sale_rate_no_sale_rate_deltas_quote_token1,
        {
            let pool = build_pool::<ChainTy>(
                to_sqrt_ratio::<ChainTy>(1).unwrap(),
                1_000,
                0,
                10 << 32,
                1 << 32,
                vec![TwammSaleRateDelta {
                    time: u64::MAX,
                    sale_rate_delta0: -(10 << 32),
                    sale_rate_delta1: -(1 << 32),
                }],
            );

            let quote = pool
                .quote(QuoteParams {
                    token_amount: TokenAmount {
                        amount: 1000,
                        token: ChainTy::one_address(),
                    },
                    sqrt_ratio_limit: None,
                    meta: 32,
                    override_state: None,
                })
                .unwrap();

            assert_eq!(
                (
                    quote.calculated_amount,
                    quote.execution_resources.virtual_order_seconds_executed,
                    quote.execution_resources.virtual_order_delta_times_crossed
                ),
                (717, 32, 0)
            );
        }
    );

    chain_test!(
        token1_sale_rate_greater_than_token0_sale_rate_no_sale_rate_deltas_quote_token1,
        {
            let pool = build_pool::<ChainTy>(
                to_sqrt_ratio::<ChainTy>(1).unwrap(),
                100_000,
                0,
                1 << 32,
                10 << 32,
                vec![TwammSaleRateDelta {
                    time: u64::MAX,
                    sale_rate_delta0: -(1 << 32),
                    sale_rate_delta1: -(10 << 32),
                }],
            );

            let quote = pool
                .quote(QuoteParams {
                    token_amount: TokenAmount {
                        amount: 1000,
                        token: ChainTy::one_address(),
                    },
                    sqrt_ratio_limit: None,
                    meta: 32,
                    override_state: None,
                })
                .unwrap();

            assert_eq!(
                (
                    quote.calculated_amount,
                    quote.execution_resources.virtual_order_seconds_executed,
                    quote.execution_resources.virtual_order_delta_times_crossed
                ),
                (984, 32, 0)
            );
        }
    );

    chain_test!(
        token0_sale_rate_greater_than_token1_sale_rate_no_sale_rate_deltas_quote_token0,
        {
            let pool = build_pool::<ChainTy>(
                to_sqrt_ratio::<ChainTy>(1).unwrap(),
                100_000,
                0,
                10 << 32,
                1 << 32,
                vec![TwammSaleRateDelta {
                    time: u64::MAX,
                    sale_rate_delta0: -(10 << 32),
                    sale_rate_delta1: -(1 << 32),
                }],
            );

            let quote = pool
                .quote(QuoteParams {
                    token_amount: TokenAmount {
                        amount: 1000,
                        token: ChainTy::zero_address(),
                    },
                    sqrt_ratio_limit: None,
                    meta: 32,
                    override_state: None,
                })
                .unwrap();

            assert_eq!(
                (
                    quote.calculated_amount,
                    quote.execution_resources.virtual_order_seconds_executed,
                    quote.execution_resources.virtual_order_delta_times_crossed
                ),
                (983, 32, 0)
            );
        }
    );

    chain_test!(
        token1_sale_rate_greater_than_token0_sale_rate_no_sale_rate_deltas_quote_token0,
        {
            let pool = build_pool::<ChainTy>(
                to_sqrt_ratio::<ChainTy>(1).unwrap(),
                100_000,
                0,
                1 << 32,
                10 << 32,
                vec![TwammSaleRateDelta {
                    time: u64::MAX,
                    sale_rate_delta0: -(1 << 32),
                    sale_rate_delta1: -(10 << 32),
                }],
            );

            let quote = pool
                .quote(QuoteParams {
                    token_amount: TokenAmount {
                        amount: 1000,
                        token: ChainTy::zero_address(),
                    },
                    sqrt_ratio_limit: None,
                    meta: 32,
                    override_state: None,
                })
                .unwrap();

            assert_eq!(
                (
                    quote.calculated_amount,
                    quote.execution_resources.virtual_order_seconds_executed,
                    quote.execution_resources.virtual_order_delta_times_crossed
                ),
                (994, 32, 0)
            );
        }
    );

    chain_test!(
        sale_rate_deltas_goes_to_zero_halfway_through_execution_quote_token0,
        {
            let pool = build_pool::<ChainTy>(
                to_sqrt_ratio::<ChainTy>(1).unwrap(),
                100_000,
                0,
                1 << 32,
                1 << 32,
                vec![TwammSaleRateDelta {
                    sale_rate_delta0: -((1u128 << 32) as i128),
                    sale_rate_delta1: -((1u128 << 32) as i128),
                    time: 16,
                }],
            );

            let quote = pool
                .quote(QuoteParams {
                    token_amount: TokenAmount {
                        amount: 1000,
                        token: ChainTy::zero_address(),
                    },
                    sqrt_ratio_limit: None,
                    meta: 32,
                    override_state: None,
                })
                .unwrap();

            assert_eq!(
                (
                    quote.calculated_amount,
                    quote.execution_resources.virtual_order_seconds_executed,
                    quote.execution_resources.virtual_order_delta_times_crossed
                ),
                (989, 32, 1)
            );
        }
    );

    chain_test!(
        sale_rate_deltas_doubles_halfway_through_execution_quote_token0,
        {
            let pool = build_pool::<ChainTy>(
                to_sqrt_ratio::<ChainTy>(1).unwrap(),
                100_000,
                0,
                1 << 32,
                1 << 32,
                vec![
                    TwammSaleRateDelta {
                        sale_rate_delta0: (1u128 << 32) as i128,
                        sale_rate_delta1: (1u128 << 32) as i128,
                        time: 16,
                    },
                    TwammSaleRateDelta {
                        time: u64::MAX,
                        sale_rate_delta0: -(1 << 33),
                        sale_rate_delta1: -(1 << 33),
                    },
                ],
            );

            let quote = pool
                .quote(QuoteParams {
                    token_amount: TokenAmount {
                        amount: 1000,
                        token: ChainTy::zero_address(),
                    },
                    sqrt_ratio_limit: None,
                    meta: 32,
                    override_state: None,
                })
                .unwrap();

            assert_eq!(
                (
                    quote.calculated_amount,
                    quote.execution_resources.virtual_order_seconds_executed,
                    quote.execution_resources.virtual_order_delta_times_crossed
                ),
                (989, 32, 1)
            );
        }
    );

    chain_test!(price_after_no_swap, {
        let pool = build_pool::<ChainTy>(
            to_sqrt_ratio::<ChainTy>(693_147).unwrap(),
            70_710_696_755_630_728_101_718_334,
            0,
            10_526_880_627_450_980_392_156_862_745,
            10_526_880_627_450_980_392_156_862_745,
            vec![TwammSaleRateDelta {
                time: u64::MAX,
                sale_rate_delta0: -10_526_880_627_450_980_392_156_862_745,
                sale_rate_delta1: -10_526_880_627_450_980_392_156_862_745,
            }],
        );

        let first = pool
            .quote(QuoteParams {
                token_amount: TokenAmount {
                    amount: 0,
                    token: ChainTy::zero_address(),
                },
                sqrt_ratio_limit: Some(to_sqrt_ratio::<ChainTy>(693_147).unwrap()),
                meta: 43_200,
                override_state: None,
            })
            .unwrap();

        pool.quote(QuoteParams {
            token_amount: TokenAmount {
                amount: 0,
                token: ChainTy::zero_address(),
            },
            sqrt_ratio_limit: Some(to_sqrt_ratio::<ChainTy>(693_147).unwrap()),
            meta: 86_400,
            override_state: None,
        })
        .unwrap();

        pool.quote(QuoteParams {
            token_amount: TokenAmount {
                amount: 0,
                token: ChainTy::zero_address(),
            },
            sqrt_ratio_limit: Some(to_sqrt_ratio::<ChainTy>(693_147).unwrap()),
            meta: 86_400,
            override_state: Some(first.state_after),
        })
        .unwrap();
    });

    chain_test!(moody_testing_examples, {
        let sale_rate = 10u128.pow(18) << 32;
        let pool = build_pool::<ChainTy>(
            to_sqrt_ratio::<ChainTy>(693_147).unwrap(),
            1_000_000_000_000_000_000_000,
            60,
            sale_rate,
            sale_rate,
            vec![TwammSaleRateDelta {
                sale_rate_delta0: -(sale_rate as i128),
                sale_rate_delta1: -(sale_rate as i128),
                time: 120,
            }],
        );

        pool.quote(QuoteParams {
            token_amount: TokenAmount {
                amount: 0,
                token: ChainTy::zero_address(),
            },
            meta: 60,
            sqrt_ratio_limit: None,
            override_state: None,
        })
        .unwrap();

        pool.quote(QuoteParams {
            token_amount: TokenAmount {
                amount: 0,
                token: ChainTy::zero_address(),
            },
            meta: 90,
            sqrt_ratio_limit: None,
            override_state: None,
        })
        .unwrap();

        let fully_executed_twamm = pool
            .quote(QuoteParams {
                token_amount: TokenAmount {
                    amount: 0,
                    token: ChainTy::zero_address(),
                },
                meta: 120,
                sqrt_ratio_limit: None,
                override_state: None,
            })
            .unwrap();

        let state_after_fully_executed = fully_executed_twamm.state_after;

        let quote_token0_with_override = pool
            .quote(QuoteParams {
                token_amount: TokenAmount {
                    amount: 10u128.pow(18) as i128,
                    token: ChainTy::zero_address(),
                },
                meta: 120,
                sqrt_ratio_limit: None,
                override_state: Some(state_after_fully_executed),
            })
            .unwrap();

        assert_eq!(
            quote_token0_with_override.calculated_amount,
            pool.full_range_pool
                .quote(QuoteParams {
                    token_amount: TokenAmount {
                        token: ChainTy::zero_address(),
                        amount: 10u128.pow(18) as i128,
                    },
                    meta: (),
                    override_state: Some(state_after_fully_executed.full_range_pool_state),
                    sqrt_ratio_limit: None,
                })
                .unwrap()
                .calculated_amount
        );

        let quote_token1_with_override = pool
            .quote(QuoteParams {
                token_amount: TokenAmount {
                    amount: 10u128.pow(18) as i128,
                    token: ChainTy::one_address(),
                },
                sqrt_ratio_limit: Some(to_sqrt_ratio::<ChainTy>(693_147).unwrap()),
                meta: 120,
                override_state: Some(state_after_fully_executed),
            })
            .unwrap();

        assert_eq!(
            quote_token1_with_override.calculated_amount,
            pool.full_range_pool
                .quote(QuoteParams {
                    token_amount: TokenAmount {
                        token: ChainTy::one_address(),
                        amount: 10u128.pow(18) as i128,
                    },
                    meta: (),
                    override_state: Some(fully_executed_twamm.state_after.full_range_pool_state),
                    sqrt_ratio_limit: Some(to_sqrt_ratio::<ChainTy>(693_147).unwrap()),
                })
                .unwrap()
                .calculated_amount
        );
    });

    chain_test!(compare_to_contract_output, |chain| {
        let pool = build_pool::<ChainTy>(
            to_sqrt_ratio::<ChainTy>(693_147).unwrap(),
            70_710_696_755_630_728_101_718_334,
            0,
            10_526_880_627_450_980_392_156_862_745,
            10_526_880_627_450_980_392_156_862_745,
            vec![TwammSaleRateDelta {
                time: u64::MAX,
                sale_rate_delta0: -10_526_880_627_450_980_392_156_862_745,
                sale_rate_delta1: -10_526_880_627_450_980_392_156_862_745,
            }],
        );

        let first_swap = pool
            .quote(QuoteParams {
                token_amount: TokenAmount {
                    amount: (10_000u128 * 10u128.pow(18)) as i128,
                    token: ChainTy::zero_address(),
                },
                meta: 2_040,
                sqrt_ratio_limit: None,
                override_state: None,
            })
            .unwrap();

        assert_eq!(
            (
                first_swap.calculated_amount,
                first_swap.consumed_amount,
                first_swap
                    .execution_resources
                    .virtual_order_seconds_executed,
                first_swap
                    .execution_resources
                    .virtual_order_delta_times_crossed
            ),
            (
                match chain {
                    ChainEnum::Evm => 19_993_991_114_278_789_946_056,
                    ChainEnum::Starknet => 19_993_991_114_278_789_950_510,
                },
                10_000_000_000_000_000_000_000,
                2_040,
                0
            )
        );

        let second_swap = pool
            .quote(QuoteParams {
                token_amount: TokenAmount {
                    amount: (10_000u128 * 10u128.pow(18)) as i128,
                    token: ChainTy::zero_address(),
                },
                meta: 2_100,
                sqrt_ratio_limit: None,
                override_state: Some(first_swap.state_after),
            })
            .unwrap();

        assert_eq!(
            (
                second_swap.calculated_amount,
                second_swap.consumed_amount,
                second_swap
                    .execution_resources
                    .virtual_order_seconds_executed,
                second_swap
                    .execution_resources
                    .virtual_order_delta_times_crossed
            ),
            (
                match chain {
                    ChainEnum::Evm => 19_985_938_387_207_961_526_664,
                    ChainEnum::Starknet => 19_985_938_387_207_961_531_114,
                },
                10_000_000_000_000_000_000_000,
                60,
                0
            )
        );
    });

    chain_test!(second_swap_in_opposite_direction, {
        let pool = build_pool::<ChainTy>(
            to_sqrt_ratio::<ChainTy>(693_147).unwrap(),
            70_710_696_755_630_728_101_718_334,
            0,
            10_526_880_627_450_980_392_156_862_745,
            10_526_880_627_450_980_392_156_862_745,
            vec![TwammSaleRateDelta {
                time: u64::MAX,
                sale_rate_delta0: -10_526_880_627_450_980_392_156_862_745,
                sale_rate_delta1: -10_526_880_627_450_980_392_156_862_745,
            }],
        );

        let first_swap = pool
            .quote(QuoteParams {
                token_amount: TokenAmount {
                    amount: (10_000u128 * 10u128.pow(18)) as i128,
                    token: ChainTy::zero_address(),
                },
                sqrt_ratio_limit: None,
                meta: 2_040,
                override_state: None,
            })
            .unwrap();

        pool.quote(QuoteParams {
            token_amount: TokenAmount {
                amount: (10_000u128 * 10u128.pow(18)) as i128,
                token: ChainTy::one_address(),
            },
            sqrt_ratio_limit: None,
            meta: 2_100,
            override_state: Some(first_swap.state_after),
        })
        .unwrap();
    });

    #[test]
    fn example_from_production_sepolia() {
        let pool = TwammPool::<Evm>::new(
            Evm::zero_address(),
            Evm::one_address(),
            9_223_372_036_854_775,
            Evm::one_address(),
            U256::from_limbs([4182607738901102592, 148436996701757, 0, 0]),
            4_472_135_213_867,
            1_743_726_720,
            3728260255814876407785,
            1597830095238095,
            vec![
                TwammSaleRateDelta {
                    time: 1_743_729_408,
                    sale_rate_delta0: 0,
                    sale_rate_delta1: -1_597_830_095_238_095,
                },
                TwammSaleRateDelta {
                    time: 1_743_847_424,
                    sale_rate_delta0: -3_545_574_640_073_966_450_931,
                    sale_rate_delta1: 0,
                },
                TwammSaleRateDelta {
                    time: 1_744_240_640,
                    sale_rate_delta0: -155_475_198_893_155_900_840,
                    sale_rate_delta1: 0,
                },
                TwammSaleRateDelta {
                    time: 1_759_510_528,
                    sale_rate_delta0: -27_210_416_847_754_056_014,
                    sale_rate_delta1: 0,
                },
            ],
        )
        .unwrap();

        let result = pool
            .quote(QuoteParams {
                token_amount: TokenAmount {
                    token: Evm::zero_address(),
                    amount: 50_000_000_000_000_000,
                },
                meta: 1_743_783_660,
                override_state: None,
                sqrt_ratio_limit: None,
            })
            .unwrap();

        assert_eq!(
            (result.consumed_amount, result.calculated_amount),
            (50_000_000_000_000_000, 126_983_565)
        );
    }
}
