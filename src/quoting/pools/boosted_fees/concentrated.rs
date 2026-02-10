use crate::chain::Chain;
use crate::quoting::types::{
    BlockTimestamp, LastTimeInfo, Pool, PoolConfig, PoolKey, Quote, QuoteParams, TimeRateDelta,
};
use crate::quoting::util::{approximate_extra_distinct_time_bitmap_lookups, real_last_time};
use crate::{private, quoting::types::PoolState};

use alloc::vec::Vec;
use derive_more::{Add, AddAssign, Sub, SubAssign};
use num_traits::Zero;
use ruint::aliases::U256;
use thiserror::Error;

use crate::chain::evm::{
    Evm, EvmConcentratedPoolKey, EvmConcentratedPoolQuoteError, EvmConcentratedPoolResources,
    EvmConcentratedPoolState, EvmConcentratedPoolTypeConfig,
};
use crate::quoting::pools::concentrated::ConcentratedPool;

/// Boosted fees pool that wraps an underlying pool and tracks donation deltas.
#[derive(Clone, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct BoostedFeesConcentratedPool {
    underlying_pool: ConcentratedPool<Evm>,
    last_donate_time: u32,
    donate_rate0: u128,
    donate_rate1: u128,
    donate_rate_deltas: Vec<TimeRateDelta>,
}

pub type BoostedFeesConcentratedPoolTypeConfig = <ConcentratedPool<Evm> as Pool>::PoolTypeConfig;
pub type BoostedFeesConcentratedPoolKey = PoolKey<
    <Evm as Chain>::Address,
    <ConcentratedPool<Evm> as Pool>::Fee,
    BoostedFeesConcentratedPoolTypeConfig,
>;
pub type BoostedFeesConcentratedPoolConfig<P> =
    PoolConfig<<P as Pool>::Address, <P as Pool>::Fee, BoostedFeesConcentratedPoolTypeConfig>;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct BoostedFeesConcentratedPoolState {
    pub concentrated_pool_state: EvmConcentratedPoolState,
    pub last_donate_time: u32,
    pub donate_rate0: u128,
    pub donate_rate1: u128,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash, Add, AddAssign, Sub, SubAssign)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct BoostedFeesConcentratedStandalonePoolResources {
    /// Number of additional distinct time bitmap lookups (besides the mandatory one).
    pub extra_distinct_bitmap_lookups: u32,
    /// The amount of donate rate updates that were applied
    pub virtual_donate_delta_times_crossed: u32,
    /// Whether the donations were executed or not (for a single swap, 1 or 0)
    pub virtual_donations_executed: u32,
    pub fees_accumulated: u32,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash, Add, AddAssign, Sub, SubAssign)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct BoostedFeesConcentratedPoolResources {
    pub concentrated: EvmConcentratedPoolResources,
    pub boosted_fees: BoostedFeesConcentratedStandalonePoolResources,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, Error)]
pub enum BoostedFeesConcentratedPoolConstructionError {
    #[error("donate rate deltas not ordered or not greater than last donate time")]
    DonateRateDeltasInvalid,
    #[error("donate rate delta overflow or underflow")]
    DonateRateDeltasOverflowOrUnderflow,
    #[error("donate rate delta sum non-zero")]
    DonateRateDeltaSumNonZero,
    #[error("pool type does not match boosted fees version")]
    IncorrectPoolType,
}

impl BoostedFeesConcentratedPool {
    pub fn new(
        underlying_pool: ConcentratedPool<Evm>,
        last_donate_time_info: LastTimeInfo,
        donate_rate0: u128,
        donate_rate1: u128,
        donate_rate_deltas: Vec<TimeRateDelta>,
    ) -> Result<Self, BoostedFeesConcentratedPoolConstructionError> {
        let mut last_time = last_donate_time_info.real_time();
        let mut dr0 = donate_rate0;
        let mut dr1 = donate_rate1;

        for delta in &donate_rate_deltas {
            if delta.time <= last_time {
                return Err(BoostedFeesConcentratedPoolConstructionError::DonateRateDeltasInvalid);
            }
            last_time = delta.time;

            dr0 = dr0.checked_add_signed(delta.rate_delta0).ok_or(
                BoostedFeesConcentratedPoolConstructionError::DonateRateDeltasOverflowOrUnderflow,
            )?;

            dr1 = dr1.checked_add_signed(delta.rate_delta1).ok_or(
                BoostedFeesConcentratedPoolConstructionError::DonateRateDeltasOverflowOrUnderflow,
            )?;
        }

        if !(dr0.is_zero() && dr1.is_zero()) {
            return Err(BoostedFeesConcentratedPoolConstructionError::DonateRateDeltaSumNonZero);
        }

        Ok(Self {
            underlying_pool,
            last_donate_time: last_donate_time_info.stored_time(),
            donate_rate0,
            donate_rate1,
            donate_rate_deltas,
        })
    }

    pub fn donate_rate_deltas(&self) -> &Vec<TimeRateDelta> {
        &self.donate_rate_deltas
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, Error)]
pub enum BoostedFeesConcentratedPoolQuoteError {
    #[error("underlying pool quote error")]
    UnderlyingPoolQuoteError(EvmConcentratedPoolQuoteError),
}

impl Pool for BoostedFeesConcentratedPool {
    type Address = <Evm as Chain>::Address;
    type Fee = <Evm as Chain>::Fee;
    type PoolTypeConfig = EvmConcentratedPoolTypeConfig;
    type Resources = BoostedFeesConcentratedPoolResources;
    type State = BoostedFeesConcentratedPoolState;
    type QuoteError = BoostedFeesConcentratedPoolQuoteError;
    type Meta = BlockTimestamp;

    fn key(&self) -> EvmConcentratedPoolKey {
        self.underlying_pool.key()
    }

    fn state(&self) -> Self::State {
        BoostedFeesConcentratedPoolState {
            concentrated_pool_state: self.underlying_pool.state(),
            last_donate_time: self.last_donate_time,
            donate_rate0: self.donate_rate0,
            donate_rate1: self.donate_rate1,
        }
    }

    fn quote(
        &self,
        QuoteParams {
            token_amount,
            sqrt_ratio_limit,
            override_state,
            meta: current_time,
        }: QuoteParams<Self::Address, Self::State, Self::Meta>,
    ) -> Result<Quote<Self::Resources, Self::State>, Self::QuoteError> {
        let BoostedFeesConcentratedPoolState {
            concentrated_pool_state: underlying_pool_state,
            last_donate_time,
            mut donate_rate0,
            mut donate_rate1,
        } = override_state.unwrap_or_else(|| self.state());

        let mut virtual_donate_delta_times_crossed = 0;
        let mut fees_accumulated = false;
        let real_last_donate_time;

        if current_time as u32 != last_donate_time {
            real_last_donate_time = real_last_time(current_time, last_donate_time);
            let mut time = real_last_donate_time;

            for delta in self
                .donate_rate_deltas
                .iter()
                .skip_while(|delta| delta.time <= real_last_donate_time)
                .take_while(|delta| delta.time <= current_time)
            {
                fees_accumulated |= (((donate_rate0 * u128::from(delta.time - time)) >> 32) != 0)
                    || (((donate_rate1 * u128::from(delta.time - time)) >> 32) != 0);

                donate_rate0 = donate_rate0.strict_add_signed(delta.rate_delta0);
                donate_rate1 = donate_rate1.strict_add_signed(delta.rate_delta1);

                time = delta.time;
                virtual_donate_delta_times_crossed += 1;
            }
        } else {
            real_last_donate_time = current_time;
        }

        let Quote {
            is_price_increasing,
            consumed_amount,
            calculated_amount,
            execution_resources: underlying_execution_resources,
            state_after: underlying_state_after,
            fees_paid,
        } = self
            .underlying_pool
            .quote(QuoteParams {
                token_amount,
                sqrt_ratio_limit,
                override_state: Some(underlying_pool_state),
                meta: (),
            })
            .map_err(BoostedFeesConcentratedPoolQuoteError::UnderlyingPoolQuoteError)?;

        Ok(Quote {
            is_price_increasing,
            consumed_amount,
            calculated_amount,
            fees_paid,
            execution_resources: BoostedFeesConcentratedPoolResources {
                concentrated: underlying_execution_resources,
                boosted_fees: BoostedFeesConcentratedStandalonePoolResources {
                    extra_distinct_bitmap_lookups: approximate_extra_distinct_time_bitmap_lookups(
                        real_last_donate_time,
                        current_time,
                    ),
                    virtual_donate_delta_times_crossed,
                    virtual_donations_executed: u32::from(current_time != real_last_donate_time),
                    fees_accumulated: u32::from(fees_accumulated),
                },
            },
            state_after: BoostedFeesConcentratedPoolState {
                concentrated_pool_state: underlying_state_after,
                last_donate_time: current_time as u32,
                donate_rate0,
                donate_rate1,
            },
        })
    }

    fn has_liquidity(&self) -> bool {
        self.underlying_pool.has_liquidity()
    }

    fn max_tick_with_liquidity(&self) -> Option<i32> {
        self.underlying_pool.max_tick_with_liquidity()
    }

    fn min_tick_with_liquidity(&self) -> Option<i32> {
        self.underlying_pool.min_tick_with_liquidity()
    }

    fn is_path_dependent(&self) -> bool {
        self.underlying_pool.is_path_dependent()
    }
}

impl PoolState for BoostedFeesConcentratedPoolState {
    fn sqrt_ratio(&self) -> U256 {
        self.concentrated_pool_state.sqrt_ratio()
    }

    fn liquidity(&self) -> u128 {
        self.concentrated_pool_state.liquidity()
    }
}

impl private::Sealed for BoostedFeesConcentratedPool {}
impl private::Sealed for BoostedFeesConcentratedPoolState {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        chain::{evm::Evm, tests::ChainTest as _},
        math::tick::to_sqrt_ratio,
        quoting::{
            pools::concentrated::{ConcentratedPool, ConcentratedPoolState, TickSpacing},
            types::{Pool, PoolConfig, PoolKey, Quote, QuoteParams, Tick, TokenAmount},
        },
    };
    use alloc::vec;

    fn concentrated_pool(liquidity: u128) -> ConcentratedPool<Evm> {
        ConcentratedPool::new(
            PoolKey {
                token0: Evm::zero_address(),
                token1: Evm::one_address(),
                config: PoolConfig {
                    fee: 0,
                    pool_type_config: TickSpacing(1),
                    extension: Evm::zero_address(),
                },
            },
            ConcentratedPoolState {
                sqrt_ratio: to_sqrt_ratio::<Evm>(0).expect("valid sqrt ratio"),
                liquidity,
                active_tick_index: Some(0),
            },
            vec![
                Tick {
                    index: -10,
                    liquidity_delta: liquidity as i128,
                },
                Tick {
                    index: 10,
                    liquidity_delta: -(liquidity as i128),
                },
            ],
        )
        .expect("concentrated pool construction succeeds")
    }

    fn boosted_pool(
        last_donated_time_info: LastTimeInfo,
        donate_rate0: u128,
        donate_rate1: u128,
        donate_rate_deltas: Vec<TimeRateDelta>,
    ) -> BoostedFeesConcentratedPool {
        BoostedFeesConcentratedPool::new(
            concentrated_pool(1_000_000),
            last_donated_time_info,
            donate_rate0,
            donate_rate1,
            donate_rate_deltas,
        )
        .expect("boosted fees pool construction succeeds")
    }

    fn quote_at(
        pool: &BoostedFeesConcentratedPool,
        current_time: u64,
    ) -> Quote<BoostedFeesConcentratedPoolResources, BoostedFeesConcentratedPoolState> {
        pool.quote(QuoteParams {
            token_amount: TokenAmount {
                amount: 0,
                token: Evm::zero_address(),
            },
            sqrt_ratio_limit: None,
            override_state: None,
            meta: current_time,
        })
        .expect("quote succeeds")
    }

    #[test]
    fn maybe_accumulate_fees_is_noop_at_same_timestamp() {
        let pool = boosted_pool(LastTimeInfo::Real(100), 0, 0, vec![]);
        let quote = quote_at(&pool, 100);

        let resources = quote.execution_resources.boosted_fees;

        assert_eq!(resources.extra_distinct_bitmap_lookups, 0);
        assert_eq!(resources.virtual_donate_delta_times_crossed, 0);
        assert_eq!(resources.virtual_donations_executed, 0);
        assert_eq!(resources.fees_accumulated, 0);

        let BoostedFeesConcentratedPoolState {
            concentrated_pool_state: _,
            last_donate_time,
            donate_rate0,
            donate_rate1,
        } = quote.state_after;

        assert_eq!(last_donate_time, 100);
        assert_eq!(donate_rate0, 0);
        assert_eq!(donate_rate1, 0);
    }

    #[test]
    fn maybe_accumulate_fees_tracks_time_change_without_deltas() {
        let pool = boosted_pool(LastTimeInfo::Real(100), 0, 0, vec![]);
        let quote = quote_at(&pool, 150);

        let resources = quote.execution_resources.boosted_fees;

        assert_eq!(resources.extra_distinct_bitmap_lookups, 0);
        assert_eq!(resources.virtual_donate_delta_times_crossed, 0);
        assert_eq!(resources.virtual_donations_executed, 1);
        assert_eq!(resources.fees_accumulated, 0);

        let BoostedFeesConcentratedPoolState {
            concentrated_pool_state: _,
            last_donate_time,
            donate_rate0,
            donate_rate1,
        } = quote.state_after;

        assert_eq!(last_donate_time, 150);
        assert_eq!(donate_rate0, 0);
        assert_eq!(donate_rate1, 0);
    }

    #[test]
    fn boosts_apply_deltas_and_mark_fees_accumulated() {
        let rate = 1u128 << 32;
        let pool = boosted_pool(
            LastTimeInfo::Real(0),
            rate,
            0,
            vec![TimeRateDelta {
                time: 200,
                rate_delta0: -(rate as i128),
                rate_delta1: 0,
            }],
        );

        let quote = quote_at(&pool, 300);

        let resources = quote.execution_resources.boosted_fees;

        assert_eq!(resources.extra_distinct_bitmap_lookups, 0);
        assert_eq!(resources.virtual_donate_delta_times_crossed, 1);
        assert_eq!(resources.virtual_donations_executed, 1);
        assert_eq!(resources.fees_accumulated, 1);

        let BoostedFeesConcentratedPoolState {
            concentrated_pool_state: _,
            last_donate_time,
            donate_rate0,
            donate_rate1,
        } = quote.state_after;

        assert_eq!(last_donate_time, 300);
        assert_eq!(donate_rate0, 0);
        assert_eq!(donate_rate1, 0);
    }

    #[test]
    fn future_boosts_do_not_change_current_rate() {
        let rate = 1u128 << 32;
        let pool = boosted_pool(
            LastTimeInfo::Real(100),
            0,
            0,
            vec![
                TimeRateDelta {
                    time: 200,
                    rate_delta0: rate as i128,
                    rate_delta1: 0,
                },
                TimeRateDelta {
                    time: 300,
                    rate_delta0: -(rate as i128),
                    rate_delta1: 0,
                },
            ],
        );

        let quote = quote_at(&pool, 150);

        let resources = quote.execution_resources.boosted_fees;

        assert_eq!(resources.extra_distinct_bitmap_lookups, 0);
        assert_eq!(resources.virtual_donate_delta_times_crossed, 0);
        assert_eq!(resources.virtual_donations_executed, 1);
        assert_eq!(resources.fees_accumulated, 0);

        let BoostedFeesConcentratedPoolState {
            concentrated_pool_state: _,
            last_donate_time,
            donate_rate0,
            donate_rate1,
        } = quote.state_after;

        assert_eq!(last_donate_time, 150);
        assert_eq!(donate_rate0, 0);
        assert_eq!(donate_rate1, 0);
    }
}
