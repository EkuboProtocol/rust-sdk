use crate::math::uint::U256;
use core::fmt::Debug;
use core::ops::Add;

// Unique key identifying the pool.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct NodeKey {
    #[cfg_attr(feature = "serde", serde(with = "crate::quoting::types::serde_u256"))]
    pub token0: U256,
    #[cfg_attr(feature = "serde", serde(with = "crate::quoting::types::serde_u256"))]
    pub token1: U256,
    pub config: Config,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Config {
    pub fee: u64,
    pub tick_spacing: u32,
    #[cfg_attr(feature = "serde", serde(with = "crate::quoting::types::serde_u256"))]
    pub extension: U256,
}

#[cfg(feature = "serde")]
pub mod serde_u256 {
    use super::*;
    use serde::Serializer;

    pub fn serialize<S>(value: &U256, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let hex_str = alloc::format!("{:x}", value);
        serializer.serialize_str(&hex_str)
    }

    pub fn deserialize<'de, D>(deserializer: D) -> Result<U256, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let hex_str: alloc::borrow::Cow<'static, str> =
            serde::Deserialize::deserialize(deserializer)?;
        U256::from_str_radix(&hex_str, 16).map_err(serde::de::Error::custom)
    }
}

impl From<U256> for Config {
    fn from(value: U256) -> Config {
        Config {
            tick_spacing: (value % U256([4294967296, 0, 0, 0])).as_u32(),
            fee: ((value >> 32) % U256([0, 1, 0, 0])).as_u64(),
            extension: value >> 96,
        }
    }
}

impl From<Config> for U256 {
    fn from(value: Config) -> U256 {
        U256::from(value.tick_spacing)
            + (U256::from(value.fee) << 32)
            + (U256::from(value.extension) << 96)
    }
}

// The aggregate effect of all positions on a pool that are bounded by the specific tick
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
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
#[derive(Clone, Copy, Debug)]
pub struct QuoteParams<S, M> {
    pub token_amount: TokenAmount,
    pub sqrt_ratio_limit: Option<U256>,
    pub override_state: Option<S>,
    pub meta: M,
}

// The result of all pool swaps is some input and output delta
#[derive(Clone, Copy, Debug)]
pub struct Quote<R, S> {
    pub is_price_increasing: bool,
    pub consumed_amount: i128,
    pub calculated_amount: u128,
    pub execution_resources: R,
    pub state_after: S,
    pub fees_paid: u128,
}

// Commonly used as meta
pub type BlockTimestamp = u64;

pub trait Pool: Send + Sync + Debug + Clone + PartialEq + Eq {
    type Resources: Add + Debug + Default + Copy + PartialEq + Eq;
    type State: Debug + Copy + PartialEq + Eq;
    type QuoteError: Debug + Copy;
    // Any additional data that is required to compute a quote for this pool, e.g. the block timestamp
    type Meta: Debug + Copy;

    fn get_key(&self) -> &NodeKey;

    fn get_state(&self) -> Self::State;

    fn quote(
        &self,
        params: QuoteParams<Self::State, Self::Meta>,
    ) -> Result<Quote<Self::Resources, Self::State>, Self::QuoteError>;

    fn has_liquidity(&self) -> bool;

    // Returns the greatest tick with non-zero liquidity in the pool
    fn max_tick_with_liquidity(&self) -> Option<i32>;
    // Returns the smallest tick with non-zero liquidity in the pool
    fn min_tick_with_liquidity(&self) -> Option<i32>;

    // Returns false if a swap of x followed by a swap of y will have the same output as a swap of x + y
    fn is_path_dependent(&self) -> bool;
}

#[cfg(test)]
mod tests {
    use crate::math::uint::U256;
    use crate::quoting::types::{Config, TokenAmount};

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

    #[test]
    fn test_config_from_u256() {
        let c: Config = U256::from_str_radix("9784678070511645692802677866596", 10)
            .unwrap()
            .into();
        assert_eq!(
            c,
            Config {
                tick_spacing: 100,
                fee: 1 << 63,
                extension: U256::from(123)
            }
        );
    }

    #[test]
    fn test_u256_from_config() {
        let c: Config = Config {
            tick_spacing: 100,
            fee: 1 << 63,
            extension: U256::from(123),
        };
        let v: U256 = c.into();
        assert_eq!(
            v,
            U256::from_str_radix("9784678070511645692802677866596", 10).unwrap()
        );
    }

    #[test]
    #[cfg(feature = "serde")]
    fn test_node_key() {
        use crate::quoting::types::NodeKey;

        let key = NodeKey {
            token0: U256::from(1),
            token1: U256::from(2),
            config: Config {
                tick_spacing: 100,
                fee: 1 << 63,
                extension: U256::from(123),
            },
        };

        let serialized = serde_json::to_string(&key).unwrap();
        let expected = serde_json::json!({
            "token0": "1",
            "token1": "2",
            "config": {
                "tick_spacing": 100,
                "fee": "9223372036854775808",
                "extension": "123"
            }
        });

        assert_eq!(serde_json::from_str::<NodeKey>(&serialized).unwrap(), key);
    }
}
