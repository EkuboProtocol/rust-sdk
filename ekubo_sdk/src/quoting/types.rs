use crate::math::swap::ComputeStepError;
use crate::math::uint::U256;
use core::ops::Add;

// Unique key identifying the pool.
pub struct NodeKey {
    pub token0: U256,
    pub token1: U256,
    pub fee: u128,
    pub tick_spacing: u32,
    pub extension: U256,
}

// Resources consumed during any swap execution.
pub struct BasePoolResources {
    pub initialized_ticks_crossed: u32,
    pub tick_spacings_crossed: u32,
}

impl Default for BasePoolResources {
    fn default() -> Self {
        BasePoolResources {
            initialized_ticks_crossed: 0,
            tick_spacings_crossed: 0,
        }
    }
}

impl Add for BasePoolResources {
    type Output = BasePoolResources;

    fn add(self, rhs: Self) -> Self::Output {
        BasePoolResources {
            initialized_ticks_crossed: self.initialized_ticks_crossed
                + rhs.initialized_ticks_crossed,
            tick_spacings_crossed: self.tick_spacings_crossed + rhs.tick_spacings_crossed,
        }
    }
}

// State of the pool that can change with every swap
#[derive(Clone)]
pub struct BasePoolState {
    pub sqrt_ratio: U256,
    pub liquidity: u128,
    pub active_tick_index: Option<usize>,
}

// A boundary to a position on a pool
#[derive(Clone)]
pub struct Tick {
    pub index: i32,
    pub liquidity_delta: i128,
}

// Information about a block necessary for quoting against some pools
pub struct Block {
    pub number: u64,
    pub time: u64,
}

// Information about the state of the network necessary for quoting against some kinds of pools (not used by base pools)
pub struct QuoteMeta {
    pub block: Block,
}

// Parameters for a quote operation.
pub struct QuoteParams {
    pub token_amount: TokenAmount,
    pub sqrt_ratio_limit: Option<U256>,
    pub override_state: Option<BasePoolState>,
    pub meta: QuoteMeta,
}

// Amount and token information.
pub struct TokenAmount {
    pub amount: i128,
    pub token: U256,
}

// Result of a quote operation.
pub struct Quote {
    pub is_price_increasing: bool,
    pub consumed_amount: i128,
    pub calculated_amount: i128,
    pub execution_resources: BasePoolResources,
    pub state_after: BasePoolState,
    pub fees_paid: u128,
}

#[derive(Debug, PartialEq)]
pub enum QuoteError {
    InvalidToken,
    InvalidSqrtRatioLimit,
    InvalidTick(i32),
    FailedComputeSwapStep(ComputeStepError),
}

pub trait Pool {
    // Given the quote parameters, return the result of a swap
    fn quote(&self, params: QuoteParams) -> Result<Quote, QuoteError>;

    // Whether the pool has any liquidity, i.e. can support quotes of any size
    fn has_liquidity(&self) -> bool;
}
