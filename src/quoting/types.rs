use crate::math::uint::U256;
use core::fmt::Debug;
use core::ops::Add;

// Unique key identifying the pool.
#[derive(Clone)]
pub struct NodeKey {
    pub token0: U256,
    pub token1: U256,
    pub fee: u128,
    pub tick_spacing: u32,
    pub extension: U256,
}

// The aggregate effect of all positions on a pool that are bounded by the specific tick
#[derive(Clone)]
pub struct Tick {
    pub index: i32,
    pub liquidity_delta: i128,
}

// Information about a block necessary for quoting against some pools
#[derive(Clone)]
pub struct Block {
    pub number: u64,
    pub time: u64,
}

// Information about the state of the network necessary for quoting against some kinds of pools (not used by base pools)
#[derive(Clone)]
pub struct QuoteMeta {
    pub block: Block,
}

// Amount and token information.
#[derive(Clone)]
pub struct TokenAmount {
    pub amount: i128,
    pub token: U256,
}

// Parameters for a quote operation.
#[derive(Clone)]
pub struct QuoteParams<S> {
    pub token_amount: TokenAmount,
    pub sqrt_ratio_limit: Option<U256>,
    pub override_state: Option<S>,
    pub meta: QuoteMeta,
}

// The result of all pool swaps is some input and output delta
#[derive(Clone)]
pub struct Quote<R, S> {
    pub is_price_increasing: bool,
    pub consumed_amount: i128,
    pub calculated_amount: i128,
    pub execution_resources: R,
    pub state_after: S,
    pub fees_paid: u128,
}

pub trait Pool {
    type Resources: Add<Output = Self::Resources> + Default + Clone + Copy;
    type State: Clone + Copy;
    type QuoteError: Debug;

    fn get_key(&self) -> NodeKey;

    fn quote(
        &self,
        params: QuoteParams<Self::State>,
    ) -> Result<Quote<Self::Resources, Self::State>, Self::QuoteError>;

    fn has_liquidity(&self) -> bool;
}
