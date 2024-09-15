use crate::math::uint::U256;

// Unique key identifying the pool.
pub struct NodeKey {
    pub token0: U256,
    pub token1: U256,
    pub fee: u128,
    pub tick_spacing: u32,
    pub extension: U256,
}

// Define the resources consumed during execution.
pub struct BasePoolResources {
    pub initialized_ticks_crossed: u64,
    pub tick_spacings_crossed: u64,
}

// Represent the state of the pool at a given time.
#[derive(Clone)]
pub struct BasePoolState {
    pub sqrt_ratio: U256,
    pub liquidity: u128,
    pub active_tick_index: Option<usize>,
}

// Represents a tick with a liquidity delta.
pub struct Tick {
    pub tick: i32,
    pub liquidity_delta: i128,
}

// Parameters for a quote operation.
pub struct QuoteParams {
    pub token_amount: TokenAmount,
    pub sqrt_ratio_limit: Option<U256>,
    pub override_state: Option<BasePoolState>,
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
