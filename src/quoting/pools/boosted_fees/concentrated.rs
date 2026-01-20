use crate::chain::Chain;
use crate::quoting::types::{BlockTimestamp, Pool, PoolConfig, PoolKey, Quote, QuoteParams};
use crate::{private, quoting::types::PoolState};

use alloc::vec::Vec;
use derive_more::{Add, AddAssign, Sub, SubAssign};
use num_traits::Zero;
use ruint::aliases::U256;
use thiserror::Error;

use crate::chain::evm::{
    Evm, EvmBasePoolKey, EvmBasePoolQuoteError, EvmBasePoolResources, EvmBasePoolState,
    EvmBasePoolTypeConfig,
};
use crate::quoting::pools::base::BasePool;

/// Boosted fees pool that wraps an underlying pool and tracks donation deltas.
#[derive(Clone, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct BoostedFeesConcentratedPool {
    underlying_pool: BasePool<Evm>,
    last_donation_time: u32,
    token0_donation_rate: u128,
    token1_donation_rate: u128,
    donation_rate_deltas: Vec<BoostedFeesConcentratedDonationRateDelta>,
}

pub type BoostedFeesConcentratedPoolTypeConfig = <BasePool<Evm> as Pool>::PoolTypeConfig;
pub type BoostedFeesConcentratedPoolKey = PoolKey<
    <Evm as Chain>::Address,
    <BasePool<Evm> as Pool>::Fee,
    BoostedFeesConcentratedPoolTypeConfig,
>;
pub type BoostedFeesConcentratedPoolConfig<P> =
    PoolConfig<<P as Pool>::Address, <P as Pool>::Fee, BoostedFeesConcentratedPoolTypeConfig>;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct BoostedFeesConcentratedPoolState {
    pub underlying_pool_state: EvmBasePoolState,
    pub last_donation_time: u32,
    pub token0_donation_rate: u128,
    pub token1_donation_rate: u128,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash, Add, AddAssign, Sub, SubAssign)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct BoostedFeesConcentratedPoolResources {
    pub underlying_pool_resources: EvmBasePoolResources,
    /// The number of seconds that passed since the last donation accumulation
    pub virtual_donation_seconds_executed: u32,
    /// The amount of donate rate updates that were applied
    pub virtual_donation_delta_times_crossed: u32,
    /// Whether the donations were executed or not (for a single swap, 1 or 0)
    pub virtual_donations_executed: u32,
    pub fees_accumulated: u32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct BoostedFeesConcentratedDonationRateDelta {
    pub time: u64,
    pub token0_donation_rate_delta: i128,
    pub token1_donation_rate_delta: i128,
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

#[derive(Debug, Clone, Copy, Hash)]
pub enum LastTimeInfo {
    Stored { stored: u32, current: u64 },
    Real(u64),
}

pub fn real_last_time(stored: u32, current: u64) -> u64 {
    current - (current.wrapping_sub(stored.into()) & u64::from(u32::MAX))
}

impl LastTimeInfo {
    pub fn stored_time(self) -> u32 {
        match self {
            Self::Stored { stored, current: _ } => stored,
            Self::Real(real) => real as u32,
        }
    }

    pub fn real_time(self) -> u64 {
        match self {
            Self::Stored { stored, current } => {
                current - (current.wrapping_sub(stored.into()) & u64::from(u32::MAX))
            }
            Self::Real(real) => real,
        }
    }
}

impl BoostedFeesConcentratedPool {
    pub fn new(
        underlying_pool: BasePool<Evm>,
        last_donation_time_info: LastTimeInfo,
        token0_donation_rate: u128,
        token1_donation_rate: u128,
        donation_rate_deltas: Vec<BoostedFeesConcentratedDonationRateDelta>,
    ) -> Result<Self, BoostedFeesConcentratedPoolConstructionError> {
        let mut last_time = last_donation_time_info.real_time();
        let mut dr0 = token0_donation_rate;
        let mut dr1 = token1_donation_rate;

        for delta in &donation_rate_deltas {
            if delta.time <= last_time {
                return Err(BoostedFeesConcentratedPoolConstructionError::DonateRateDeltasInvalid);
            }
            last_time = delta.time;

            dr0 = dr0
                .checked_add_signed(delta.token0_donation_rate_delta)
                .ok_or(
                BoostedFeesConcentratedPoolConstructionError::DonateRateDeltasOverflowOrUnderflow,
            )?;

            dr1 = dr1
                .checked_add_signed(delta.token1_donation_rate_delta)
                .ok_or(
                BoostedFeesConcentratedPoolConstructionError::DonateRateDeltasOverflowOrUnderflow,
            )?;
        }

        if !(dr0.is_zero() && dr1.is_zero()) {
            return Err(BoostedFeesConcentratedPoolConstructionError::DonateRateDeltaSumNonZero);
        }

        Ok(Self {
            underlying_pool,
            last_donation_time: last_donation_time_info.stored_time(),
            token0_donation_rate,
            token1_donation_rate,
            donation_rate_deltas,
        })
    }

    pub fn donation_rate_deltas(&self) -> &Vec<BoostedFeesConcentratedDonationRateDelta> {
        &self.donation_rate_deltas
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, Error)]
pub enum BoostedFeesConcentratedPoolQuoteError {
    #[error("underlying pool quote error")]
    UnderlyingPoolQuoteError(EvmBasePoolQuoteError),
}

impl Pool for BoostedFeesConcentratedPool {
    type Address = <Evm as Chain>::Address;
    type Fee = <Evm as Chain>::Fee;
    type PoolTypeConfig = EvmBasePoolTypeConfig;
    type Resources = BoostedFeesConcentratedPoolResources;
    type State = BoostedFeesConcentratedPoolState;
    type QuoteError = BoostedFeesConcentratedPoolQuoteError;
    type Meta = BlockTimestamp;

    fn key(&self) -> EvmBasePoolKey {
        self.underlying_pool.key()
    }

    fn state(&self) -> Self::State {
        BoostedFeesConcentratedPoolState {
            underlying_pool_state: self.underlying_pool.state(),
            last_donation_time: self.last_donation_time,
            token0_donation_rate: self.token0_donation_rate,
            token1_donation_rate: self.token1_donation_rate,
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
            underlying_pool_state,
            last_donation_time,
            mut token0_donation_rate,
            mut token1_donation_rate,
        } = override_state.unwrap_or_else(|| self.state());

        let mut virtual_donation_deltas_crossed = 0;
        let mut fees_accumulated = false;
        let real_last_donation_time;

        if current_time as u32 != last_donation_time {
            real_last_donation_time = real_last_time(last_donation_time, current_time);
            let mut time = real_last_donation_time;

            for delta in self
                .donation_rate_deltas
                .iter()
                .skip_while(|delta| delta.time <= real_last_donation_time)
                .take_while(|delta| delta.time <= current_time)
            {
                fees_accumulated |=
                    (((token0_donation_rate * u128::from(delta.time - time)) >> 32) != 0)
                        || (((token1_donation_rate * u128::from(delta.time - time)) >> 32) != 0);

                token0_donation_rate =
                    token0_donation_rate.strict_add_signed(delta.token0_donation_rate_delta);
                token1_donation_rate =
                    token1_donation_rate.strict_add_signed(delta.token1_donation_rate_delta);

                time = delta.time;
                virtual_donation_deltas_crossed += 1;
            }
        } else {
            real_last_donation_time = current_time;
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
                underlying_pool_resources: underlying_execution_resources,
                virtual_donation_seconds_executed: (current_time - real_last_donation_time) as u32,
                virtual_donation_delta_times_crossed: virtual_donation_deltas_crossed,
                virtual_donations_executed: u32::from(current_time != real_last_donation_time),
                fees_accumulated: u32::from(fees_accumulated),
            },
            state_after: BoostedFeesConcentratedPoolState {
                underlying_pool_state: underlying_state_after,
                last_donation_time: current_time as u32,
                token0_donation_rate,
                token1_donation_rate,
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
        self.underlying_pool_state.sqrt_ratio()
    }

    fn liquidity(&self) -> u128 {
        self.underlying_pool_state.liquidity()
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
            pools::base::{BasePool, BasePoolState, TickSpacing},
            types::{Pool, PoolConfig, PoolKey, Quote, QuoteParams, Tick, TokenAmount},
        },
    };
    use alloc::vec;

    fn base_pool(liquidity: u128) -> BasePool<Evm> {
        BasePool::new(
            PoolKey {
                token0: Evm::zero_address(),
                token1: Evm::one_address(),
                config: PoolConfig {
                    fee: 0,
                    pool_type_config: TickSpacing(1),
                    extension: Evm::zero_address(),
                },
            },
            BasePoolState {
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
        .expect("base pool construction succeeds")
    }

    fn boosted_pool(
        last_donation_time_info: LastTimeInfo,
        token0_donation_rate: u128,
        token1_donation_rate: u128,
        donation_rate_deltas: Vec<BoostedFeesConcentratedDonationRateDelta>,
    ) -> BoostedFeesConcentratedPool {
        BoostedFeesConcentratedPool::new(
            base_pool(1_000_000),
            last_donation_time_info,
            token0_donation_rate,
            token1_donation_rate,
            donation_rate_deltas,
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

        let BoostedFeesConcentratedPoolResources {
            virtual_donation_seconds_executed,
            virtual_donation_delta_times_crossed,
            virtual_donations_executed,
            fees_accumulated,
            underlying_pool_resources: _,
        } = quote.execution_resources;

        assert_eq!(virtual_donation_seconds_executed, 0);
        assert_eq!(virtual_donation_delta_times_crossed, 0);
        assert_eq!(virtual_donations_executed, 0);
        assert_eq!(fees_accumulated, 0);

        let BoostedFeesConcentratedPoolState {
            underlying_pool_state: _,
            last_donation_time,
            token0_donation_rate,
            token1_donation_rate,
        } = quote.state_after;

        assert_eq!(last_donation_time, 100);
        assert_eq!(token0_donation_rate, 0);
        assert_eq!(token1_donation_rate, 0);
    }

    #[test]
    fn maybe_accumulate_fees_tracks_time_change_without_deltas() {
        let pool = boosted_pool(LastTimeInfo::Real(100), 0, 0, vec![]);
        let quote = quote_at(&pool, 150);

        let BoostedFeesConcentratedPoolResources {
            virtual_donation_seconds_executed,
            virtual_donation_delta_times_crossed,
            virtual_donations_executed,
            fees_accumulated,
            underlying_pool_resources: _,
        } = quote.execution_resources;

        assert_eq!(virtual_donation_seconds_executed, 50);
        assert_eq!(virtual_donation_delta_times_crossed, 0);
        assert_eq!(virtual_donations_executed, 1);
        assert_eq!(fees_accumulated, 0);

        let BoostedFeesConcentratedPoolState {
            underlying_pool_state: _,
            last_donation_time,
            token0_donation_rate,
            token1_donation_rate,
        } = quote.state_after;

        assert_eq!(last_donation_time, 150);
        assert_eq!(token0_donation_rate, 0);
        assert_eq!(token1_donation_rate, 0);
    }

    #[test]
    fn boosts_apply_deltas_and_mark_fees_accumulated() {
        let rate = 1u128 << 32;
        let pool = boosted_pool(
            LastTimeInfo::Real(0),
            rate,
            0,
            vec![BoostedFeesConcentratedDonationRateDelta {
                time: 200,
                token0_donation_rate_delta: -(rate as i128),
                token1_donation_rate_delta: 0,
            }],
        );

        let quote = quote_at(&pool, 300);

        let BoostedFeesConcentratedPoolResources {
            virtual_donation_seconds_executed,
            virtual_donation_delta_times_crossed,
            virtual_donations_executed,
            fees_accumulated,
            underlying_pool_resources: _,
        } = quote.execution_resources;

        assert_eq!(virtual_donation_seconds_executed, 300);
        assert_eq!(virtual_donation_delta_times_crossed, 1);
        assert_eq!(virtual_donations_executed, 1);
        assert_eq!(fees_accumulated, 1);

        let BoostedFeesConcentratedPoolState {
            underlying_pool_state: _,
            last_donation_time,
            token0_donation_rate,
            token1_donation_rate,
        } = quote.state_after;

        assert_eq!(last_donation_time, 300);
        assert_eq!(token0_donation_rate, 0);
        assert_eq!(token1_donation_rate, 0);
    }

    #[test]
    fn future_boosts_do_not_change_current_rate() {
        let rate = 1u128 << 32;
        let pool = boosted_pool(
            LastTimeInfo::Real(100),
            0,
            0,
            vec![
                BoostedFeesConcentratedDonationRateDelta {
                    time: 200,
                    token0_donation_rate_delta: rate as i128,
                    token1_donation_rate_delta: 0,
                },
                BoostedFeesConcentratedDonationRateDelta {
                    time: 300,
                    token0_donation_rate_delta: -(rate as i128),
                    token1_donation_rate_delta: 0,
                },
            ],
        );

        let quote = quote_at(&pool, 150);

        let BoostedFeesConcentratedPoolResources {
            virtual_donation_seconds_executed,
            virtual_donation_delta_times_crossed,
            virtual_donations_executed,
            fees_accumulated,
            underlying_pool_resources: _,
        } = quote.execution_resources;

        assert_eq!(virtual_donation_seconds_executed, 50);
        assert_eq!(virtual_donation_delta_times_crossed, 0);
        assert_eq!(virtual_donations_executed, 1);
        assert_eq!(fees_accumulated, 0);

        let BoostedFeesConcentratedPoolState {
            underlying_pool_state: _,
            last_donation_time,
            token0_donation_rate,
            token1_donation_rate,
        } = quote.state_after;

        assert_eq!(last_donation_time, 150);
        assert_eq!(token0_donation_rate, 0);
        assert_eq!(token1_donation_rate, 0);
    }
}
