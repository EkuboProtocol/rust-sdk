use crate::math::uint::U256;
use crate::quoting::base_pool::{
    BasePool, BasePoolQuoteError, BasePoolResources, BasePoolState,
    MAX_SQRT_RATIO_AT_MAX_TICK_SPACING, MAX_TICK_AT_MAX_TICK_SPACING, MAX_TICK_SPACING,
    MIN_SQRT_RATIO_AT_MAX_TICK_SPACING, MIN_TICK_AT_MAX_TICK_SPACING,
};
use crate::quoting::types::{NodeKey, Pool, Quote, QuoteParams, Tick};
use alloc::vec;
use alloc::vec::Vec;
use core::ops::Add;
use num_traits::ToPrimitive;

#[derive(Clone, Copy)]
pub struct TwammPoolState {
    last_execution_time: u64,
    sale_rate0: u128,
    sale_rate1: u128,
}

#[derive(Clone, Copy, Default)]
pub struct TwammPoolResources {
    base_pool_resources: BasePoolResources,
    num_virtual_order_times_crossed: u32,
}

impl Add for TwammPoolResources {
    type Output = TwammPoolResources;

    fn add(self, rhs: Self) -> Self::Output {
        TwammPoolResources {
            base_pool_resources: self.base_pool_resources + rhs.base_pool_resources,
            num_virtual_order_times_crossed: self.num_virtual_order_times_crossed
                + rhs.num_virtual_order_times_crossed,
        }
    }
}

#[derive(Clone)]
struct VirtualOrderDeltas {
    time: u64,
    sale_rate_delta0: u128,
    sale_rate_delta1: u128,
}

pub struct TwammPool {
    base_pool: BasePool,
    state: TwammPoolState,
    virtual_order_deltas: Vec<VirtualOrderDeltas>,
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
        sale_rate0: u128,
        sale_rate1: u128,
        virtual_order_deltas: Vec<VirtualOrderDeltas>,
    ) -> Self {
        let signed_liquidity: i128 = liquidity.to_i128().expect("Liquidity overflow i128");
        TwammPool {
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
                    active_tick_index: if sqrt_ratio >= MIN_SQRT_RATIO_AT_MAX_TICK_SPACING
                        && sqrt_ratio < MAX_SQRT_RATIO_AT_MAX_TICK_SPACING
                    {
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
            state: TwammPoolState {
                last_execution_time,
                sale_rate0,
                sale_rate1,
            },
        }
    }
}

impl Pool for TwammPool {
    type Resources = TwammPoolResources;
    type State = TwammPoolState;
    type QuoteError = BasePoolQuoteError;

    fn get_key(&self) -> NodeKey {
        self.base_pool.get_key()
    }

    fn quote(
        &self,
        params: QuoteParams<Self::State>,
    ) -> Result<Quote<Self::Resources, Self::State>, Self::QuoteError> {
        todo!()
    }

    fn has_liquidity(&self) -> bool {
        todo!()
    }
}
