use core::{error::Error, fmt};

use derive_more::{Add, AddAssign, Sub, SubAssign};
use num_traits::Zero as _;
use ruint::aliases::U256;

use crate::{
    chain::{evm::Evm, Chain},
    math::swap::{amount_before_fee, compute_fee},
    private,
    quoting::types::{Pool, PoolConfig, PoolKey, PoolState, Quote, QuoteParams},
};

/// Ve33 extension pool wrapper.
///
/// Ve33 pools execute the underlying Core swap with zero Core fees, then account
/// the voted swap fee in the unspecified token.
#[derive(Clone, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Ve33Pool<P> {
    underlying_pool: P,
    swap_fee: <Evm as Chain>::Fee,
}

/// Unique identifier for a [`Ve33Pool`].
pub type Ve33PoolKey<P> =
    PoolKey<<Evm as Chain>::Address, <Evm as Chain>::Fee, <P as Pool>::PoolTypeConfig>;
/// Pool configuration for a [`Ve33Pool`].
pub type Ve33PoolConfig<P> =
    PoolConfig<<Evm as Chain>::Address, <Evm as Chain>::Fee, <P as Pool>::PoolTypeConfig>;

/// State snapshot for a [`Ve33Pool`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Ve33PoolState<S> {
    /// State of the underlying pool.
    pub underlying_pool_state: S,
    /// Current voted Ve33 swap fee.
    pub swap_fee: <Evm as Chain>::Fee,
}

/// Resources consumed by Ve33 extension logic.
#[derive(Clone, Copy, Default, Debug, PartialEq, Eq, Hash, Add, AddAssign, Sub, SubAssign)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Ve33StandalonePoolResources {
    /// Whether a non-zero Ve33 swap fee was accounted.
    pub fees_accumulated: u32,
}

/// Resources consumed during Ve33 quote execution.
#[derive(Clone, Copy, Default, Debug, PartialEq, Eq, Hash, Add, AddAssign, Sub, SubAssign)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Ve33PoolResources<R> {
    /// Resources consumed by the underlying pool.
    pub underlying: R,
    /// Resources added by the Ve33 wrapper.
    pub ve33: Ve33StandalonePoolResources,
}

/// Errors that can occur when constructing a [`Ve33Pool`].
#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, thiserror::Error)]
pub enum Ve33PoolConstructionError {
    #[error("underlying pool fee must be zero")]
    FeeMustBeZero,
    #[error("extension must be non-zero")]
    MissingExtension,
}

/// Errors that can occur when quoting a [`Ve33Pool`].
#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub enum Ve33PoolQuoteError<E> {
    /// Underlying pool quote failed.
    UnderlyingPoolQuoteError(E),
    /// Exact-output fee computation overflowed.
    AmountBeforeFeeOverflow,
}

impl<P> Ve33Pool<P>
where
    P: Pool<Address = <Evm as Chain>::Address, Fee = <Evm as Chain>::Fee>,
{
    /// Creates a new Ve33 pool wrapper over an EVM pool with zero Core fee.
    pub fn new(
        underlying_pool: P,
        swap_fee: <Evm as Chain>::Fee,
    ) -> Result<Self, Ve33PoolConstructionError> {
        let PoolConfig { fee, extension, .. } = underlying_pool.key().config;

        if !fee.is_zero() {
            return Err(Ve33PoolConstructionError::FeeMustBeZero);
        }
        if extension.is_zero() {
            return Err(Ve33PoolConstructionError::MissingExtension);
        }

        Ok(Self {
            underlying_pool,
            swap_fee,
        })
    }

    /// Returns the current voted Ve33 swap fee.
    pub fn swap_fee(&self) -> <Evm as Chain>::Fee {
        self.swap_fee
    }

    /// Returns the underlying pool.
    pub fn underlying_pool(&self) -> &P {
        &self.underlying_pool
    }
}

impl<P> AsRef<P> for Ve33Pool<P>
where
    P: Pool<Address = <Evm as Chain>::Address, Fee = <Evm as Chain>::Fee>,
{
    fn as_ref(&self) -> &P {
        self.underlying_pool()
    }
}

impl<P> AsRef<Self> for Ve33Pool<P> {
    fn as_ref(&self) -> &Self {
        self
    }
}

impl<E: fmt::Display> fmt::Display for Ve33PoolQuoteError<E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnderlyingPoolQuoteError(error) => {
                write!(f, "underlying pool quote error: {error}")
            }
            Self::AmountBeforeFeeOverflow => f.write_str("amount before fee overflow"),
        }
    }
}

impl<E> Error for Ve33PoolQuoteError<E> where E: Error + 'static {}

impl<P> Pool for Ve33Pool<P>
where
    P: Pool<Address = <Evm as Chain>::Address, Fee = <Evm as Chain>::Fee>,
{
    type Address = <Evm as Chain>::Address;
    type Fee = <Evm as Chain>::Fee;
    type Resources = Ve33PoolResources<P::Resources>;
    type State = Ve33PoolState<P::State>;
    type QuoteError = Ve33PoolQuoteError<P::QuoteError>;
    type Meta = P::Meta;
    type PoolTypeConfig = P::PoolTypeConfig;

    fn key(&self) -> Ve33PoolKey<P> {
        self.underlying_pool.key()
    }

    fn state(&self) -> Self::State {
        Ve33PoolState {
            underlying_pool_state: self.underlying_pool.state(),
            swap_fee: self.swap_fee,
        }
    }

    fn quote(
        &self,
        QuoteParams {
            token_amount,
            sqrt_ratio_limit,
            override_state,
            meta,
        }: QuoteParams<Self::Address, Self::State, Self::Meta>,
    ) -> Result<Quote<Self::Resources, Self::State>, Self::QuoteError> {
        let Ve33PoolState {
            underlying_pool_state,
            swap_fee,
        } = override_state.unwrap_or_else(|| self.state());

        let Quote {
            is_price_increasing,
            consumed_amount,
            mut calculated_amount,
            execution_resources: underlying_execution_resources,
            state_after: underlying_state_after,
            fees_paid,
        } = self
            .underlying_pool
            .quote(QuoteParams {
                token_amount,
                sqrt_ratio_limit,
                override_state: Some(underlying_pool_state),
                meta,
            })
            .map_err(Ve33PoolQuoteError::UnderlyingPoolQuoteError)?;

        let ve33_fee = if swap_fee.is_zero() {
            0
        } else if token_amount.amount >= 0 {
            let fee = compute_fee::<Evm>(calculated_amount, swap_fee);
            calculated_amount -= fee;
            fee
        } else {
            let amount_including_fee = amount_before_fee::<Evm>(calculated_amount, swap_fee)
                .ok_or(Ve33PoolQuoteError::AmountBeforeFeeOverflow)?;
            let fee = amount_including_fee - calculated_amount;
            calculated_amount = amount_including_fee;
            fee
        };

        Ok(Quote {
            is_price_increasing,
            consumed_amount,
            calculated_amount,
            fees_paid: fees_paid + ve33_fee,
            execution_resources: Ve33PoolResources {
                underlying: underlying_execution_resources,
                ve33: Ve33StandalonePoolResources {
                    fees_accumulated: u32::from(ve33_fee != 0),
                },
            },
            state_after: Ve33PoolState {
                underlying_pool_state: underlying_state_after,
                swap_fee,
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

impl<S: PoolState> PoolState for Ve33PoolState<S> {
    fn sqrt_ratio(&self) -> U256 {
        self.underlying_pool_state.sqrt_ratio()
    }

    fn liquidity(&self) -> u128 {
        self.underlying_pool_state.liquidity()
    }
}

impl<P> private::Sealed for Ve33Pool<P> {}
impl<S: PoolState> private::Sealed for Ve33PoolState<S> {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        chain::{evm::Evm, tests::ChainTest as _},
        math::{swap::amount_before_fee, tick::to_sqrt_ratio},
        quoting::{
            pools::full_range::{FullRangePool, FullRangePoolState, FullRangePoolTypeConfig},
            types::{Pool, PoolConfig, PoolKey, QuoteParams, TokenAmount},
        },
    };

    const ONE_PERCENT_FEE: u64 = ((1u128 << 64) / 100) as u64;

    fn full_range_pool() -> FullRangePool {
        FullRangePool::new(
            PoolKey {
                token0: Evm::zero_address(),
                token1: Evm::one_address(),
                config: PoolConfig {
                    fee: 0,
                    extension: Evm::one_address(),
                    pool_type_config: FullRangePoolTypeConfig,
                },
            },
            FullRangePoolState {
                sqrt_ratio: to_sqrt_ratio::<Evm>(0).unwrap(),
                liquidity: 1_000_000,
            },
        )
        .unwrap()
    }

    #[test]
    fn exact_input_takes_fee_from_output() {
        let underlying = full_range_pool();
        let ve33 = Ve33Pool::new(underlying.clone(), ONE_PERCENT_FEE).unwrap();
        let token_amount = TokenAmount {
            token: Evm::zero_address(),
            amount: 100_000,
        };

        let underlying_quote = underlying
            .quote(QuoteParams {
                token_amount,
                sqrt_ratio_limit: None,
                override_state: None,
                meta: (),
            })
            .unwrap();
        let ve33_quote = ve33
            .quote(QuoteParams {
                token_amount,
                sqrt_ratio_limit: None,
                override_state: None,
                meta: (),
            })
            .unwrap();

        let expected_fee = compute_fee::<Evm>(underlying_quote.calculated_amount, ONE_PERCENT_FEE);
        assert_eq!(
            ve33_quote.calculated_amount,
            underlying_quote.calculated_amount - expected_fee
        );
        assert_eq!(ve33_quote.fees_paid, expected_fee);
        assert_eq!(ve33_quote.execution_resources.ve33.fees_accumulated, 1);
    }

    #[test]
    fn exact_output_adds_fee_to_input() {
        let underlying = full_range_pool();
        let ve33 = Ve33Pool::new(underlying.clone(), ONE_PERCENT_FEE).unwrap();
        let token_amount = TokenAmount {
            token: Evm::zero_address(),
            amount: -100_000,
        };

        let underlying_quote = underlying
            .quote(QuoteParams {
                token_amount,
                sqrt_ratio_limit: None,
                override_state: None,
                meta: (),
            })
            .unwrap();
        let ve33_quote = ve33
            .quote(QuoteParams {
                token_amount,
                sqrt_ratio_limit: None,
                override_state: None,
                meta: (),
            })
            .unwrap();

        assert_eq!(
            ve33_quote.calculated_amount,
            amount_before_fee::<Evm>(underlying_quote.calculated_amount, ONE_PERCENT_FEE).unwrap()
        );
        assert_eq!(
            ve33_quote.fees_paid,
            ve33_quote.calculated_amount - underlying_quote.calculated_amount
        );
    }

    #[test]
    fn constructor_requires_zero_core_fee() {
        let pool = FullRangePool::new(
            PoolKey {
                token0: Evm::zero_address(),
                token1: Evm::one_address(),
                config: PoolConfig {
                    fee: 1,
                    extension: Evm::one_address(),
                    pool_type_config: FullRangePoolTypeConfig,
                },
            },
            FullRangePoolState {
                sqrt_ratio: to_sqrt_ratio::<Evm>(0).unwrap(),
                liquidity: 1_000_000,
            },
        )
        .unwrap();

        assert_eq!(
            Ve33Pool::new(pool, 0).unwrap_err(),
            Ve33PoolConstructionError::FeeMustBeZero
        );
    }
}
