use crate::math::uint::U256;
use core::fmt::Debug;
use core::ops::Add;

// Unique key identifying the pool.
#[derive(Clone, Copy, PartialEq, Debug)]
pub struct NodeKey {
    pub token0: U256,
    pub token1: U256,
    pub fee: u128,
    pub tick_spacing: u32,
    pub extension: U256,
}

// The aggregate effect of all positions on a pool that are bounded by the specific tick
#[derive(Clone, Copy, PartialEq, Debug)]
pub struct Tick {
    pub index: i32,
    pub liquidity_delta: i128,
}

// Amount and token information.
#[derive(Clone, Copy, PartialEq, Debug, Ord, PartialOrd, Eq)]
pub struct TokenAmount {
    pub token: U256,
    pub amount: i128,
}

// Parameters for a quote operation.
#[derive(Clone, Copy)]
pub struct QuoteParams<S, M> {
    pub token_amount: TokenAmount,
    pub sqrt_ratio_limit: Option<U256>,
    pub override_state: Option<S>,
    pub meta: M,
}

// The result of all pool swaps is some input and output delta
#[derive(Clone, Copy)]
pub struct Quote<R, S> {
    pub is_price_increasing: bool,
    pub consumed_amount: i128,
    pub calculated_amount: i128,
    pub execution_resources: R,
    pub state_after: S,
    pub fees_paid: u128,
}

// Commonly used as meta
pub type BlockTimestamp = u64;

pub trait Pool: Send + Sync {
    type Resources: Add<Output = Self::Resources> + Default + Copy;
    type State: Copy;
    type QuoteError: Debug;
    // Any additional data that is required to compute a quote for this pool, e.g. the block timestamp
    type Meta: Copy;

    fn get_key(&self) -> &NodeKey;

    fn get_state(&self) -> Self::State;

    fn quote(
        &self,
        params: QuoteParams<Self::State, Self::Meta>,
    ) -> Result<Quote<Self::Resources, Self::State>, Self::QuoteError>;

    fn has_liquidity(&self) -> bool;
}

#[cfg(test)]
mod tests {
    use crate::math::uint::U256;
    use crate::quoting::types::TokenAmount;

    #[test]
    fn test_ordering_token_amount() {
        assert!(
            TokenAmount {
                token: U256::one(),
                amount: 0,
            } > TokenAmount {
                token: U256::zero(),
                amount: 1,
            }
        );
        assert_eq!(
            TokenAmount {
                token: U256::zero(),
                amount: 0,
            },
            TokenAmount {
                token: U256::zero(),
                amount: 0,
            }
        );
        assert!(
            TokenAmount {
                token: U256::zero(),
                amount: 0,
            } > TokenAmount {
                token: U256::zero(),
                amount: -1,
            }
        );
        assert!(
            TokenAmount {
                token: U256::zero(),
                amount: 0,
            } < TokenAmount {
                token: U256::one(),
                amount: -1,
            }
        );
        assert!(
            TokenAmount {
                token: U256::zero(),
                amount: 0,
            } < TokenAmount {
                token: U256::zero(),
                amount: 1,
            }
        );
    }
}
