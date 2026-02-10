use num_traits::Zero;
use ruint::aliases::U256;

use crate::{private, quoting::util::real_last_time};
use core::{
    error::Error,
    fmt::Debug,
    ops::{AddAssign, SubAssign},
};
use core::{
    hash::Hash,
    ops::{Add, Sub},
};

/// Unique key identifying the pool.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct PoolKey<A, F, C> {
    /// The smaller token address.
    pub token0: A,
    /// The larger token address.
    pub token1: A,
    /// Pool configuration including fee, extension, and pool type specifics.
    pub config: PoolConfig<A, F, C>,
}

/// Pool configuration shared across pool implementations.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct PoolConfig<A, F, C> {
    /// Extension address.
    pub extension: A,
    /// Fee tier of the pool.
    pub fee: F,
    /// Pool-type specific configuration.
    pub pool_type_config: C,
}

/// The aggregate effect of all positions on a pool that are bounded by the specific tick
#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Tick {
    /// Tick index where liquidity delta applies.
    pub index: i32,
    /// Liquidity change applied at this tick.
    pub liquidity_delta: i128,
}

/// Amount and token information.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct TokenAmount<A> {
    /// Token being swapped.
    pub token: A,
    /// Signed amount (positive for exact input, negative for exact output).
    pub amount: i128,
}

/// Parameters for a quote operation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct QuoteParams<A, S, M> {
    /// Token and amount for the swap.
    pub token_amount: TokenAmount<A>,
    /// Optional price limit.
    pub sqrt_ratio_limit: Option<U256>,
    /// Optional override of current pool state.
    pub override_state: Option<S>,
    /// Pool-specific metadata (e.g., timestamp).
    pub meta: M,
}

/// The simulated outcome of a swap
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Quote<R, S> {
    /// Whether price increased during the quote.
    pub is_price_increasing: bool,
    /// Signed amount of input consumed.
    pub consumed_amount: i128,
    /// Unsigned amount of output calculated.
    pub calculated_amount: u128,
    /// Execution resource usage.
    pub execution_resources: R,
    /// Pool state after the simulated swap.
    pub state_after: S,
    /// Fees paid during the swap.
    pub fees_paid: u128,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct TimeRateDelta {
    pub time: u64,
    pub rate_delta0: i128,
    pub rate_delta1: i128,
}

#[derive(Debug, Clone, Copy, Hash)]
pub enum LastTimeInfo {
    Stored { stored: u32, current: u64 },
    Real(u64),
}

/// Commonly used as [`Pool::Meta`]
pub type BlockTimestamp = u64;

pub trait Pool: private::Sealed + Debug {
    type Address;
    type Fee;
    type Resources: Debug
        + Default
        + Copy
        + Eq
        + Hash
        + Add<Output = Self::Resources>
        + AddAssign
        + Sub<Output = Self::Resources>
        + SubAssign;
    type State: PoolState + Debug + Copy + Eq + Hash;
    type QuoteError: Error + Copy + Eq + Hash + 'static;
    /// Any additional data that is required to compute a quote for this pool, e.g. the block timestamp
    type Meta: Debug + Copy + Eq + Hash;
    type PoolTypeConfig; // TODO Bounds

    fn key(&self) -> PoolKey<Self::Address, Self::Fee, Self::PoolTypeConfig>;
    fn state(&self) -> Self::State;

    /// Quotes the pool with the given parameters
    fn quote(
        &self,
        params: QuoteParams<Self::Address, Self::State, Self::Meta>,
    ) -> Result<Quote<Self::Resources, Self::State>, Self::QuoteError>;

    /// A quick check on whether the pool has any liquidity
    fn has_liquidity(&self) -> bool {
        !self.state().liquidity().is_zero()
    }

    /// Returns the greatest tick with non-zero liquidity in the pool
    fn max_tick_with_liquidity(&self) -> Option<i32>;
    /// Returns the smallest tick with non-zero liquidity in the pool
    fn min_tick_with_liquidity(&self) -> Option<i32>;

    /// Returns false if a swap of x followed by a swap of y will have the same output as a swap of x + y
    fn is_path_dependent(&self) -> bool;
}

pub trait PoolState: private::Sealed {
    fn sqrt_ratio(&self) -> U256;
    fn liquidity(&self) -> u128;
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
            Self::Stored { stored, current } => real_last_time(current, stored),
            Self::Real(real) => real,
        }
    }
}

impl<A, F, C> PoolKey<A, F, C> {
    /// Convenience function to map pool type configs using their [`From`] implementations.
    pub fn map_into_config<T: From<C>>(self) -> PoolKey<A, F, T> {
        let Self {
            token0,
            token1,
            config:
                PoolConfig {
                    extension,
                    fee,
                    pool_type_config,
                },
        } = self;

        PoolKey {
            token0,
            token1,
            config: PoolConfig {
                extension,
                fee,
                pool_type_config: pool_type_config.into(),
            },
        }
    }
}
