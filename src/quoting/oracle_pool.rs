use crate::quoting::types::{BlockTimestamp, Pool, PoolKey, Quote, QuoteParams};
use crate::{math::uint::U256, quoting::types::PoolState};
use core::ops::{Add, AddAssign, Sub, SubAssign};
use num_traits::Zero;

use crate::chain::Chain;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct OraclePoolState<S> {
    pub full_range_pool_state: S,
    pub last_snapshot_time: u64,
}

#[derive(Clone, Copy, Default, Debug, PartialEq, Eq)]
pub struct OraclePoolResources<R> {
    pub underlying_pool_resources: R,
    pub snapshots_written: u32,
}

impl<R: AddAssign> AddAssign for OraclePoolResources<R> {
    fn add_assign(&mut self, rhs: Self) {
        self.underlying_pool_resources += rhs.underlying_pool_resources;
        self.snapshots_written += rhs.snapshots_written;
    }
}

impl<R: AddAssign> Add for OraclePoolResources<R> {
    type Output = Self;

    fn add(mut self, rhs: Self) -> Self::Output {
        self += rhs;
        self
    }
}

impl<R: SubAssign> SubAssign for OraclePoolResources<R> {
    fn sub_assign(&mut self, rhs: Self) {
        self.underlying_pool_resources -= rhs.underlying_pool_resources;
        self.snapshots_written -= rhs.snapshots_written;
    }
}

impl<R: SubAssign> Sub for OraclePoolResources<R> {
    type Output = Self;

    fn sub(mut self, rhs: Self) -> Self::Output {
        self -= rhs;
        self
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct OraclePool<C: Chain> {
    full_range_pool: C::FullRangePool,
    last_snapshot_time: u64,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum OraclePoolError<E> {
    FullRangePoolError(E),
}

impl<C: Chain> OraclePool<C> {
    pub fn new(
        token0: U256,
        token1: U256,
        extension: U256,
        sqrt_ratio: U256,
        active_liquidity: u128,
        last_snapshot_time: u64,
    ) -> Result<Self, OraclePoolError<C::FullRangePoolError>> {
        Ok(OraclePool {
            full_range_pool: C::new_full_range_pool(
                token0,
                token1,
                Zero::zero(),
                extension,
                sqrt_ratio,
                active_liquidity,
            )
            .map_err(OraclePoolError::FullRangePoolError)?,
            last_snapshot_time,
        })
    }
}

impl<C: Chain> Pool<C> for OraclePool<C> {
    type Resources = OraclePoolResources<<C::FullRangePool as Pool<C>>::Resources>;
    type State = OraclePoolState<<C::FullRangePool as Pool<C>>::State>;
    type QuoteError = <C::FullRangePool as Pool<C>>::QuoteError;
    type Meta = BlockTimestamp;
    type PoolTypeConfig = <C::FullRangePool as Pool<C>>::PoolTypeConfig;

    fn key(&self) -> PoolKey<C::Fee, Self::PoolTypeConfig> {
        self.full_range_pool.key()
    }

    fn state(&self) -> Self::State {
        OraclePoolState {
            full_range_pool_state: self.full_range_pool.state(),
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

        let result = self.full_range_pool.quote(QuoteParams {
            sqrt_ratio_limit: params.sqrt_ratio_limit,
            override_state: params.override_state.map(|s| s.full_range_pool_state),
            token_amount: params.token_amount,
            meta: (),
        })?;

        Ok(Quote {
            calculated_amount: result.calculated_amount,
            consumed_amount: result.consumed_amount,
            execution_resources: OraclePoolResources {
                snapshots_written: if pool_time != block_time { 1 } else { 0 },
                underlying_pool_resources: result.execution_resources,
            },
            fees_paid: result.fees_paid,
            is_price_increasing: result.is_price_increasing,
            state_after: OraclePoolState {
                full_range_pool_state: result.state_after,
                last_snapshot_time: block_time,
            },
        })
    }

    fn has_liquidity(&self) -> bool {
        self.full_range_pool.has_liquidity()
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

impl<S: PoolState> PoolState for OraclePoolState<S> {
    fn sqrt_ratio(&self) -> U256 {
        self.full_range_pool_state.sqrt_ratio()
    }

    fn liquidity(&self) -> u128 {
        self.full_range_pool_state.liquidity()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        chain::{tests::chain_test, Chain, Starknet},
        math::{tick::to_sqrt_ratio, uint::U256},
        quoting::types::{Pool, PoolState, QuoteParams, TokenAmount},
    };

    const TOKEN0: U256 = U256([1, 0, 0, 0]);
    const TOKEN1: U256 = U256([2, 0, 0, 0]);
    const EXTENSION: U256 = U256([3, 0, 0, 0]);
    const DEFAULT_LIQUIDITY: u128 = 1_000_000_000;

    fn min_ratio<C: Chain>() -> U256 {
        C::min_sqrt_ratio_full_range()
    }

    fn max_ratio<C: Chain>() -> U256 {
        C::max_sqrt_ratio_full_range()
    }

    fn build_pool<C: Chain>(
        sqrt_ratio: U256,
        liquidity: u128,
        last_snapshot_time: u64,
    ) -> OraclePool<C> {
        OraclePool::new(
            TOKEN0,
            TOKEN1,
            EXTENSION,
            sqrt_ratio,
            liquidity,
            last_snapshot_time,
        )
        .unwrap()
    }

    fn default_pool<C: Chain>() -> OraclePool<C> {
        build_pool::<C>(to_sqrt_ratio::<C>(0).unwrap(), DEFAULT_LIQUIDITY, 1)
    }

    #[test]
    fn starknet_max_values() {
        assert_eq!(
            to_sqrt_ratio::<Starknet>(Starknet::MIN_TICK_AT_MAX_TICK_SPACING).unwrap(),
            Starknet::MIN_SQRT_RATIO_AT_MAX_TICK_SPACING
        );
        assert_eq!(
            to_sqrt_ratio::<Starknet>(Starknet::MAX_TICK_AT_MAX_TICK_SPACING).unwrap(),
            Starknet::MAX_SQRT_RATIO_AT_MAX_TICK_SPACING
        );
    }

    mod constructor_validation {
        use super::*;

        chain_test!(max_price_constructor, {
            let state = build_pool::<ChainTy>(max_ratio::<ChainTy>(), 1, 0).state();
            assert_eq!(state.full_range_pool_state.liquidity(), 1);
        });

        chain_test!(min_price_constructor, {
            let state = build_pool::<ChainTy>(min_ratio::<ChainTy>(), 1, 0).state();
            assert_eq!(state.full_range_pool_state.liquidity(), 1);
        });

        #[test]
        fn starknet_min_sqrt_ratio_at_max_tick_spacing() {
            let state =
                build_pool::<Starknet>(Starknet::MIN_SQRT_RATIO_AT_MAX_TICK_SPACING, 1, 0).state();
            assert_eq!(state.full_range_pool_state.liquidity(), 1);
        }

        #[test]
        fn starknet_max_sqrt_ratio_at_max_tick_spacing() {
            let state =
                build_pool::<Starknet>(Starknet::MAX_SQRT_RATIO_AT_MAX_TICK_SPACING, 1, 0).state();
            assert_eq!(state.full_range_pool_state.liquidity(), 1);
        }
    }

    chain_test!(quote_token1_input_update, {
        let pool = default_pool::<ChainTy>();

        let quote = pool
            .quote(QuoteParams {
                token_amount: TokenAmount {
                    amount: 1000,
                    token: TOKEN1,
                },
                sqrt_ratio_limit: None,
                override_state: None,
                meta: 2,
            })
            .unwrap();

        assert_eq!(
            (
                quote.calculated_amount,
                quote.consumed_amount,
                quote.execution_resources.snapshots_written,
                quote.state_after.last_snapshot_time
            ),
            (999, 1000, 1, 2)
        );
    });

    chain_test!(quote_token0_input, {
        let pool = default_pool::<ChainTy>();

        let quote = pool
            .quote(QuoteParams {
                token_amount: TokenAmount {
                    amount: 1000,
                    token: TOKEN0,
                },
                sqrt_ratio_limit: None,
                override_state: None,
                meta: 2,
            })
            .unwrap();

        assert_eq!(
            (
                quote.calculated_amount,
                quote.consumed_amount,
                quote.execution_resources.snapshots_written,
                quote.state_after.last_snapshot_time
            ),
            (999, 1000, 1, 2)
        );
    });
}
