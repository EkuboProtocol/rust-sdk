use num_traits::Zero;
use ruint::aliases::U256;

use crate::private;
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
    pub token0: A,
    pub token1: A,
    pub config: PoolConfig<A, F, C>,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct PoolConfig<A, F, C> {
    pub extension: A,
    pub fee: F,
    pub pool_type_config: C,
}

/*impl From<U256> for Config<Evm> {
    fn from(value: U256) -> Config<Evm> {
        Config {
            tick_spacing: (value % U256::from_limbs([4294967296, 0, 0, 0])).as_u32(),
            fee: ((value >> 32) % U256::from_limbs([0, 1, 0, 0])).as_u64(),
            extension: value >> 96,
        }
    }
}

impl From<Config<Evm>> for U256 {
    fn from(value: Config<Evm>) -> U256 {
        U256::from(value.tick_spacing)
            + (U256::from(value.fee) << 32)
            + (U256::from(value.extension) << 96)
    }
}*/

/// The aggregate effect of all positions on a pool that are bounded by the specific tick
#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Tick {
    pub index: i32,
    pub liquidity_delta: i128,
}

/// Amount and token information.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TokenAmount<A> {
    pub token: A,
    pub amount: i128,
}

/// Parameters for a quote operation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct QuoteParams<A, S, M> {
    pub token_amount: TokenAmount<A>,
    pub sqrt_ratio_limit: Option<U256>,
    pub override_state: Option<S>,
    pub meta: M,
}

/// The simulated outcome of a swap
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Quote<R, S> {
    pub is_price_increasing: bool,
    pub consumed_amount: i128,
    pub calculated_amount: u128,
    pub execution_resources: R,
    pub state_after: S,
    pub fees_paid: u128,
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
