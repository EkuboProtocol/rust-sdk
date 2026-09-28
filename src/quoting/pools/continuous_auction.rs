use core::{error::Error, fmt};

use derive_more::{Add, AddAssign, Sub, SubAssign};
use num_traits::Zero as _;
use ruint::aliases::U256;

use crate::{
    chain::{Chain, evm::Evm},
    math::swap::{amount_before_fee, compute_fee},
    private,
    quoting::types::{BlockTimestamp, Pool, PoolConfig, PoolKey, PoolState, Quote, QuoteParams},
};

/// Continuous auction extension pool wrapper.
///
/// Auction pools execute the underlying Core swap with zero Core fees. Only the live bid's
/// executor swaps fee-free; every other swapper pays the live bid's fee in the unspecified token,
/// accounted like the Ve33 voted fee. Quotes are produced for such outsiders. Without a live bid
/// the pool does not swap and quoting fails with [`ContinuousAuctionPoolQuoteError::PoolClosed`].
#[derive(Clone, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ContinuousAuctionPool<P> {
    underlying_pool: P,
    auction: ContinuousAuctionState,
}

/// Unique identifier for a [`ContinuousAuctionPool`].
pub type ContinuousAuctionPoolKey<P> =
    PoolKey<<Evm as Chain>::Address, <Evm as Chain>::Fee, <P as Pool>::PoolTypeConfig>;
/// Pool configuration for a [`ContinuousAuctionPool`].
pub type ContinuousAuctionPoolConfig<P> =
    PoolConfig<<Evm as Chain>::Address, <Evm as Chain>::Fee, <P as Pool>::PoolTypeConfig>;

/// The part of a bid that affects swaps.
#[derive(Clone, Copy, Default, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ContinuousAuctionBid {
    /// First second in which the bid holds the pool.
    pub start: u64,
    /// First second in which the bid no longer holds the pool.
    pub end: u64,
    /// Fee charged to swappers other than the bid's executor, as a 0.32 fixed-point fraction: the
    /// upper 32 bits of Core's 0.64 fee format.
    pub fee: u32,
}

impl ContinuousAuctionBid {
    /// Returns the fee in Core's 0.64 fixed-point format.
    pub fn core_fee(&self) -> <Evm as Chain>::Fee {
        u64::from(self.fee) << 32
    }

    fn holds(&self, time: BlockTimestamp) -> bool {
        self.start <= time && time < self.end
    }
}

/// The settled schedule of an auction pool, as returned by `ContinuousAuction.auctions(poolId)`.
#[derive(Clone, Copy, Default, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ContinuousAuctionState {
    /// The current bid. A zero bid, or one whose `end` has passed, does not hold the pool.
    pub current_bid: ContinuousAuctionBid,
    /// The next bid, placed during second `last_settled` and starting at `last_settled + 1`.
    /// It takes over from the current bid at its start.
    pub next_bid: Option<ContinuousAuctionBid>,
    /// The last second in which the extension settled rent.
    pub last_settled: u64,
}

impl ContinuousAuctionState {
    /// Returns the bid holding the pool at `time`, if any, mirroring `ContinuousAuction._activeBid`.
    pub fn live_bid(&self, time: BlockTimestamp) -> Option<ContinuousAuctionBid> {
        let active = match self.next_bid {
            Some(next) if next.start <= time => next,
            _ => self.current_bid,
        };
        active.holds(time).then_some(active)
    }

    /// Returns the schedule after the extension settles at `time`: a due next bid becomes current.
    fn settled(self, time: BlockTimestamp) -> Self {
        let (current_bid, next_bid) = match self.next_bid {
            Some(next) if next.start <= time => (next, None),
            next_bid => (self.current_bid, next_bid),
        };
        Self {
            current_bid,
            next_bid,
            last_settled: self.last_settled.max(time),
        }
    }
}

/// State snapshot for a [`ContinuousAuctionPool`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ContinuousAuctionPoolState<S> {
    /// State of the underlying pool.
    pub underlying_pool_state: S,
    /// Bid schedule stored by the extension.
    pub auction: ContinuousAuctionState,
}

/// Resources consumed by continuous auction extension logic, on top of the underlying swap.
///
/// On concentrated pools the extension also updates its per-tick rent growth for every
/// initialized tick the swap crosses, which the underlying resources already count.
#[derive(Clone, Copy, Default, Debug, PartialEq, Eq, Hash, Add, AddAssign, Sub, SubAssign)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ContinuousAuctionStandalonePoolResources {
    /// Whether the swap was the first extension call of its second and settled rent.
    pub settlements: u32,
    /// Whether a non-zero fee was saved for the bid holder.
    pub fees_accumulated: u32,
}

/// Resources consumed during continuous auction quote execution.
#[derive(Clone, Copy, Default, Debug, PartialEq, Eq, Hash, Add, AddAssign, Sub, SubAssign)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ContinuousAuctionPoolResources<R> {
    /// Resources consumed by the underlying pool.
    pub underlying: R,
    /// Resources added by the auction wrapper.
    pub continuous_auction: ContinuousAuctionStandalonePoolResources,
}

/// Errors that can occur when constructing a [`ContinuousAuctionPool`].
#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, thiserror::Error)]
pub enum ContinuousAuctionPoolConstructionError {
    #[error("underlying pool fee must be zero")]
    FeeMustBeZero,
    #[error("extension must be non-zero")]
    MissingExtension,
}

/// Errors that can occur when quoting a [`ContinuousAuctionPool`].
#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub enum ContinuousAuctionPoolQuoteError<E> {
    /// Underlying pool quote failed.
    UnderlyingPoolQuoteError(E),
    /// No bid holds the pool at the quote's timestamp, so the pool does not swap.
    PoolClosed,
    /// Exact-output fee computation overflowed.
    AmountBeforeFeeOverflow,
}

impl<P> ContinuousAuctionPool<P>
where
    P: Pool<Address = <Evm as Chain>::Address, Fee = <Evm as Chain>::Fee, Meta = ()>,
{
    /// Creates a new auction pool wrapper over an EVM pool with zero Core fee.
    pub fn new(
        underlying_pool: P,
        auction: ContinuousAuctionState,
    ) -> Result<Self, ContinuousAuctionPoolConstructionError> {
        let PoolConfig { fee, extension, .. } = underlying_pool.key().config;

        if !fee.is_zero() {
            return Err(ContinuousAuctionPoolConstructionError::FeeMustBeZero);
        }
        if extension.is_zero() {
            return Err(ContinuousAuctionPoolConstructionError::MissingExtension);
        }

        Ok(Self {
            underlying_pool,
            auction,
        })
    }

    /// Returns the bid schedule.
    pub fn auction(&self) -> ContinuousAuctionState {
        self.auction
    }

    /// Returns the underlying pool.
    pub fn underlying_pool(&self) -> &P {
        &self.underlying_pool
    }
}

impl<P> AsRef<P> for ContinuousAuctionPool<P>
where
    P: Pool<Address = <Evm as Chain>::Address, Fee = <Evm as Chain>::Fee, Meta = ()>,
{
    fn as_ref(&self) -> &P {
        self.underlying_pool()
    }
}

impl<P> AsRef<Self> for ContinuousAuctionPool<P> {
    fn as_ref(&self) -> &Self {
        self
    }
}

impl<E: fmt::Display> fmt::Display for ContinuousAuctionPoolQuoteError<E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnderlyingPoolQuoteError(error) => {
                write!(f, "underlying pool quote error: {error}")
            }
            Self::PoolClosed => f.write_str("pool closed: no live bid"),
            Self::AmountBeforeFeeOverflow => f.write_str("amount before fee overflow"),
        }
    }
}

impl<E> Error for ContinuousAuctionPoolQuoteError<E> where E: Error + 'static {}

impl<P> Pool for ContinuousAuctionPool<P>
where
    P: Pool<Address = <Evm as Chain>::Address, Fee = <Evm as Chain>::Fee, Meta = ()>,
{
    type Address = <Evm as Chain>::Address;
    type Fee = <Evm as Chain>::Fee;
    type Resources = ContinuousAuctionPoolResources<P::Resources>;
    type State = ContinuousAuctionPoolState<P::State>;
    type QuoteError = ContinuousAuctionPoolQuoteError<P::QuoteError>;
    type Meta = BlockTimestamp;
    type PoolTypeConfig = P::PoolTypeConfig;

    fn key(&self) -> ContinuousAuctionPoolKey<P> {
        self.underlying_pool.key()
    }

    fn state(&self) -> Self::State {
        ContinuousAuctionPoolState {
            underlying_pool_state: self.underlying_pool.state(),
            auction: self.auction,
        }
    }

    fn quote(
        &self,
        QuoteParams {
            token_amount,
            sqrt_ratio_limit,
            override_state,
            meta: time,
        }: QuoteParams<Self::Address, Self::State, Self::Meta>,
    ) -> Result<Quote<Self::Resources, Self::State>, Self::QuoteError> {
        let ContinuousAuctionPoolState {
            underlying_pool_state,
            auction,
        } = override_state.unwrap_or_else(|| self.state());

        let fee = auction
            .live_bid(time)
            .ok_or(ContinuousAuctionPoolQuoteError::PoolClosed)?
            .core_fee();

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
                meta: (),
            })
            .map_err(ContinuousAuctionPoolQuoteError::UnderlyingPoolQuoteError)?;

        let auction_fee = if token_amount.amount >= 0 {
            let fee = compute_fee::<Evm>(calculated_amount, fee);
            calculated_amount -= fee;
            fee
        } else {
            // The extension casts the input including the fee to int128.
            let amount_including_fee = amount_before_fee::<Evm>(calculated_amount, fee)
                .filter(|&amount| amount <= i128::MAX as u128)
                .ok_or(ContinuousAuctionPoolQuoteError::AmountBeforeFeeOverflow)?;
            let fee = amount_including_fee - calculated_amount;
            calculated_amount = amount_including_fee;
            fee
        };

        Ok(Quote {
            is_price_increasing,
            consumed_amount,
            calculated_amount,
            fees_paid: fees_paid + auction_fee,
            execution_resources: ContinuousAuctionPoolResources {
                underlying: underlying_execution_resources,
                continuous_auction: ContinuousAuctionStandalonePoolResources {
                    settlements: u32::from(auction.last_settled < time),
                    fees_accumulated: u32::from(auction_fee != 0),
                },
            },
            state_after: ContinuousAuctionPoolState {
                underlying_pool_state: underlying_state_after,
                auction: auction.settled(time),
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

impl<S: PoolState> PoolState for ContinuousAuctionPoolState<S> {
    fn sqrt_ratio(&self) -> U256 {
        self.underlying_pool_state.sqrt_ratio()
    }

    fn liquidity(&self) -> u128 {
        self.underlying_pool_state.liquidity()
    }
}

impl<P> private::Sealed for ContinuousAuctionPool<P> {}
impl<S: PoolState> private::Sealed for ContinuousAuctionPoolState<S> {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        chain::{evm::Evm, tests::ChainTest as _},
        math::tick::to_sqrt_ratio,
        quoting::{
            pools::{
                concentrated::{ConcentratedPool, ConcentratedPoolState, TickSpacing},
                full_range::{FullRangePool, FullRangePoolState, FullRangePoolTypeConfig},
                stableswap::{StableswapPool, StableswapPoolTypeConfig},
            },
            types::{PoolConfig, PoolKey, QuoteParams, Tick, TokenAmount},
        },
    };
    use alloc::{format, vec::Vec};

    // Fixtures are Core swaps logged by `AuctionQuoteFixturesTest` against evm-contracts PR #375 at
    // 4be93a5c0493298a6c9f2ef60b635b17e02dd7c5; the generator is the `fixture-generator` document on
    // EKU-158. Each pool has a bid live at second 101 and swaps from its initial state at tick 0
    // (sqrt ratio 2**128), through the bid's executor for holder fixtures and another locker otherwise.
    const NOW: u64 = 101;
    const ONE_PERCENT: u32 = 42_949_672;
    const FIVE_BPS: u32 = 2_147_483;
    const THIRTY_PERCENT: u32 = 1_288_490_188;
    const MIN_TICK: i32 = -88_722_835;
    const MAX_TICK: i32 = 88_722_835;

    fn auction(fee: u32) -> ContinuousAuctionState {
        ContinuousAuctionState {
            current_bid: ContinuousAuctionBid::default(),
            next_bid: Some(ContinuousAuctionBid {
                start: NOW,
                end: 512,
                fee,
            }),
            last_settled: NOW - 1,
        }
    }

    fn key<C>(pool_type_config: C) -> PoolKey<<Evm as Chain>::Address, u64, C> {
        PoolKey {
            token0: Evm::zero_address(),
            token1: Evm::one_address(),
            config: PoolConfig {
                fee: 0,
                extension: Evm::one_address(),
                pool_type_config,
            },
        }
    }

    fn concentrated_pool() -> ConcentratedPool<Evm> {
        let positions: [(i32, i32, i128); 4] = [
            (-1600, 1600, 1_250_500_691_666_528_455_630),
            (-320, 480, 2_083_584_384_999_821_926_541),
            (160, 960, 750_210_399_401_269_119_446),
            (-800, -160, 625_150_327_834_073_600_128),
        ];
        let mut ticks: Vec<Tick> = positions
            .iter()
            .flat_map(|&(lower, upper, liquidity)| {
                [
                    Tick {
                        index: lower,
                        liquidity_delta: liquidity,
                    },
                    Tick {
                        index: upper,
                        liquidity_delta: -liquidity,
                    },
                ]
            })
            .collect();
        ticks.sort_by_key(|tick| tick.index);
        let active_tick_index = ticks.iter().rposition(|tick| tick.index <= 0);

        ConcentratedPool::new(
            key(TickSpacing(16)),
            ConcentratedPoolState {
                sqrt_ratio: to_sqrt_ratio::<Evm>(0).unwrap(),
                liquidity: 3_334_085_076_666_350_382_171,
                active_tick_index,
            },
            ticks,
        )
        .unwrap()
    }

    fn stableswap_pool() -> StableswapPool {
        StableswapPool::new(
            key(StableswapPoolTypeConfig {
                center_tick: 0,
                amplification_factor: 20,
            }),
            FullRangePoolState {
                sqrt_ratio: to_sqrt_ratio::<Evm>(0).unwrap(),
                liquidity: 23_810_035_717_783_728_409_620,
            },
        )
        .unwrap()
    }

    fn full_range_pool() -> FullRangePool {
        FullRangePool::new(
            key(FullRangePoolTypeConfig),
            FullRangePoolState {
                sqrt_ratio: to_sqrt_ratio::<Evm>(0).unwrap(),
                liquidity: 1_000_000_000_000_000_000,
            },
        )
        .unwrap()
    }

    /// Foundry logs the fixed-point expansion of the ratio Core stores.
    fn assert_stored_sqrt_ratio(quoted: U256, stored: &str, context: &str) {
        assert_eq!(
            quoted,
            stored.parse::<U256>().unwrap(),
            "sqrt ratio after {context}"
        );
    }

    /// One Foundry swap: `(amount, is_token1, limit_tick, delta0, delta1, sqrt_ratio_after)`.
    type Fixture = (i128, bool, i32, i128, i128, &'static str);

    type AuctionQuoteResult<P> = Result<
        Quote<
            <ContinuousAuctionPool<P> as Pool>::Resources,
            <ContinuousAuctionPool<P> as Pool>::State,
        >,
        <ContinuousAuctionPool<P> as Pool>::QuoteError,
    >;

    fn quote<P>(
        pool: &ContinuousAuctionPool<P>,
        amount: i128,
        is_token1: bool,
        limit_tick: i32,
        time: u64,
    ) -> AuctionQuoteResult<P>
    where
        P: Pool<Address = <Evm as Chain>::Address, Fee = u64, Meta = ()>,
    {
        let key = pool.key();
        pool.quote(QuoteParams {
            token_amount: TokenAmount {
                token: if is_token1 { key.token1 } else { key.token0 },
                amount,
            },
            sqrt_ratio_limit: Some(to_sqrt_ratio::<Evm>(limit_tick).unwrap()),
            override_state: None,
            meta: time,
        })
    }

    fn check_outsider_fixtures<P>(pool: &ContinuousAuctionPool<P>, fixtures: &[Fixture])
    where
        P: Pool<Address = <Evm as Chain>::Address, Fee = u64, Meta = ()>,
    {
        for &(amount, is_token1, limit_tick, delta0, delta1, sqrt_ratio_after) in fixtures {
            let quote = quote(pool, amount, is_token1, limit_tick, NOW).unwrap();
            let (specified, calculated) = if is_token1 {
                (delta1, delta0)
            } else {
                (delta0, delta1)
            };
            assert_eq!(
                quote.consumed_amount, specified,
                "consumed amount of {amount} is_token1={is_token1}"
            );
            assert_eq!(
                quote.calculated_amount,
                calculated.unsigned_abs(),
                "calculated amount of {amount} is_token1={is_token1}"
            );
            assert_stored_sqrt_ratio(
                quote.state_after.sqrt_ratio(),
                sqrt_ratio_after,
                &format!("{amount} is_token1={is_token1}"),
            );
            let resources = quote.execution_resources.continuous_auction;
            assert_eq!(resources.settlements, 1);
            assert_eq!(resources.fees_accumulated, 1);
        }
    }

    #[test]
    fn concentrated_outsider_swaps_match_contract() {
        let pool = ContinuousAuctionPool::new(concentrated_pool(), auction(ONE_PERCENT)).unwrap();
        check_outsider_fixtures(
            &pool,
            &[
                (
                    100_000_000_000_000_000,
                    false,
                    MIN_TICK,
                    100_000_000_000_000_000,
                    -98_997_030_781_060_512,
                    "340272161057763610369071035797639004160",
                ),
                (
                    400_000_000_000_000_000,
                    true,
                    MAX_TICK,
                    -395_953_464_793_384_319,
                    400_000_000_000_000_000,
                    "340320693340766264835122801345522827264",
                ),
                (
                    -200_000_000_000_000_000,
                    false,
                    MAX_TICK,
                    -200_000_000_000_000_000,
                    202_032_321_180_702_105,
                    "340302780484039516543169164236501811200",
                ),
                (
                    -300_000_000_000_000_000,
                    true,
                    MIN_TICK,
                    303_057_518_985_207_167,
                    -300_000_000_000_000_000,
                    "340252284791600776540248807708391636992",
                ),
                (
                    10_000_000_000_000_000_000,
                    true,
                    200,
                    -344_910_576_144_100_096,
                    348_430_562_851_212_443,
                    "340316396842083298508397242390312648704",
                ),
                (
                    -10_000_000_000_000_000_000,
                    false,
                    200,
                    -348_394_521_279_018_033,
                    351_950_063_406_611_590,
                    "340316396842083298508397242390312648704",
                ),
                (
                    1_000_000_000_000_000,
                    true,
                    MAX_TICK,
                    -989_999_703_290_091,
                    1_000_000_000_000_000,
                    "340282468982631280555974561192925462528",
                ),
            ],
        );
    }

    #[test]
    fn stableswap_outsider_swaps_match_contract() {
        let pool = ContinuousAuctionPool::new(stableswap_pool(), auction(FIVE_BPS)).unwrap();
        check_outsider_fixtures(
            &pool,
            &[
                (
                    100_000_000_000_000_000,
                    false,
                    MIN_TICK,
                    100_000_000_000_000_000,
                    -99_949_580_235_875_749,
                    "340280937771726740228848555201914732544",
                ),
                (
                    400_000_000_000_000_000,
                    true,
                    MAX_TICK,
                    -399_793_283_677_582_728,
                    400_000_000_000_000_000,
                    "340288083541794546894303974739448692736",
                ),
                (
                    -200_000_000_000_000_000,
                    false,
                    MAX_TICK,
                    -200_000_000_000_000_000,
                    200_101_730_813_212_425,
                    "340285225255375998334829099058890539008",
                ),
                (
                    -300_000_000_000_000_000,
                    true,
                    MIN_TICK,
                    300_153_856_849_497_004,
                    -300_000_000_000_000_000,
                    "340278079455296400842926919738541998080",
                ),
                (
                    10_000_000_000_000_000_000,
                    true,
                    200,
                    -999_500_000_150_869_975,
                    1_000_042_000_861_007_197,
                    "340316396842083298508397242390312648704",
                ),
                (
                    -10_000_000_000_000_000_000,
                    false,
                    200,
                    -999_999_999_999_995_716,
                    1_000_542_271_845_974_113,
                    "340316396842083298508397242390312648704",
                ),
                (
                    1_000_000_000_000_000,
                    true,
                    MAX_TICK,
                    -999_499_958_169_929,
                    1_000_000_000_000_000,
                    "340282381212490603631369093887876399104",
                ),
            ],
        );
    }

    #[test]
    fn full_range_outsider_swaps_match_contract() {
        let pool = ContinuousAuctionPool::new(full_range_pool(), auction(THIRTY_PERCENT)).unwrap();
        check_outsider_fixtures(
            &pool,
            &[
                (
                    100_000_000_000_000_000,
                    false,
                    MIN_TICK,
                    100_000_000_000_000_000,
                    -63_636_363_653_296_774,
                    "309347606291762239512158734036689223680",
                ),
                (
                    400_000_000_000_000_000,
                    true,
                    MAX_TICK,
                    -200_000_000_053_218_432,
                    400_000_000_000_000_000,
                    "476395313689313848804452264627572572160",
                ),
                (
                    -200_000_000_000_000_000,
                    false,
                    MAX_TICK,
                    -200_000_000_000_000_000,
                    357_142_857_047_824_228,
                    "425352958651173079329218259289710264320",
                ),
                (
                    -300_000_000_000_000_000,
                    true,
                    MIN_TICK,
                    612_244_897_796_270_105,
                    -300_000_000_000_000_000,
                    "238197656844656924424362225188493852672",
                ),
                (
                    10_000_000_000_000_000_000,
                    true,
                    200,
                    -69_996_465_138_812,
                    100_004_950_161_704,
                    "340316396842083298508397242390312648704",
                ),
                (
                    -10_000_000_000_000_000_000,
                    false,
                    200,
                    -99_994_950_171_695,
                    142_864_214_478_705,
                    "340316396842083298508397242390312648704",
                ),
                (
                    1_000_000_000_000_000,
                    true,
                    MAX_TICK,
                    -699_300_699_486_777,
                    1_000_000_000_000_000,
                    "340622649287859401860134555468666241024",
                ),
            ],
        );
    }

    /// The executor swaps fee-free, so its Foundry swaps equal the zero-fee underlying quote.
    fn check_holder_fixtures<P>(pool: &P, fixtures: &[Fixture])
    where
        P: Pool<Address = <Evm as Chain>::Address, Fee = u64, Meta = ()>,
    {
        let key = pool.key();
        for &(amount, is_token1, limit_tick, delta0, delta1, sqrt_ratio_after) in fixtures {
            let quote = pool
                .quote(QuoteParams {
                    token_amount: TokenAmount {
                        token: if is_token1 { key.token1 } else { key.token0 },
                        amount,
                    },
                    sqrt_ratio_limit: Some(to_sqrt_ratio::<Evm>(limit_tick).unwrap()),
                    override_state: None,
                    meta: (),
                })
                .unwrap();
            let calculated = if is_token1 { delta0 } else { delta1 };
            assert_eq!(
                quote.calculated_amount,
                calculated.unsigned_abs(),
                "holder calculated amount of {amount} is_token1={is_token1}"
            );
            assert_stored_sqrt_ratio(
                quote.state_after.sqrt_ratio(),
                sqrt_ratio_after,
                &format!("holder {amount} is_token1={is_token1}"),
            );
        }
    }

    #[test]
    fn holder_swaps_are_the_underlying_zero_fee_swap() {
        check_holder_fixtures(
            &concentrated_pool(),
            &[
                (
                    100_000_000_000_000_000,
                    false,
                    MIN_TICK,
                    100_000_000_000_000_000,
                    -99_997_000_766_373_173,
                    "340272161057763610369071035797639004160",
                ),
                (
                    -300_000_000_000_000_000,
                    true,
                    MIN_TICK,
                    300_026_943_863_093_729,
                    -300_000_000_000_000_000,
                    "340252284791600776540248807708391636992",
                ),
                (
                    400_000_000_000_000_000,
                    true,
                    MAX_TICK,
                    -399_952_994_650_492_787,
                    400_000_000_000_000_000,
                    "340320693340766264835122801345522827264",
                ),
                (
                    -200_000_000_000_000_000,
                    false,
                    MAX_TICK,
                    -200_000_000_000_000_000,
                    200_011_998_014_052_826,
                    "340302780484039516543169164236501811200",
                ),
                (
                    1_000_000_000_000_000,
                    true,
                    MAX_TICK,
                    -999_999_700_067_247,
                    1_000_000_000_000_000,
                    "340282468982631280555974561192925462528",
                ),
            ],
        );
        check_holder_fixtures(
            &stableswap_pool(),
            &[
                (
                    100_000_000_000_000_000,
                    false,
                    MIN_TICK,
                    100_000_000_000_000_000,
                    -99_999_580_010_793_784,
                    "340280937771726740228848555201914732544",
                ),
                (
                    -300_000_000_000_000_000,
                    true,
                    MIN_TICK,
                    300_003_779_966_357_745,
                    -300_000_000_000_000_000,
                    "340278079455296400842926919738541998080",
                ),
                (
                    400_000_000_000_000_000,
                    true,
                    MAX_TICK,
                    -399_993_280_257_362_721,
                    400_000_000_000_000_000,
                    "340288083541794546894303974739448692736",
                ),
                (
                    -200_000_000_000_000_000,
                    false,
                    MAX_TICK,
                    -200_000_000_000_000_000,
                    200_001_679_977_996_018,
                    "340285225255375998334829099058890539008",
                ),
                (
                    1_000_000_000_000_000,
                    true,
                    MAX_TICK,
                    -999_999_957_998_054,
                    1_000_000_000_000_000,
                    "340282381212490603631369093887876399104",
                ),
            ],
        );
        check_holder_fixtures(
            &full_range_pool(),
            &[
                (
                    100_000_000_000_000_000,
                    false,
                    MIN_TICK,
                    100_000_000_000_000_000,
                    -90_909_090_909_090_909,
                    "309347606291762239512158734036689223680",
                ),
                (
                    -300_000_000_000_000_000,
                    true,
                    MIN_TICK,
                    428_571_428_571_428_572,
                    -300_000_000_000_000_000,
                    "238197656844656924424362225188493852672",
                ),
                (
                    400_000_000_000_000_000,
                    true,
                    MAX_TICK,
                    -285_714_285_714_285_714,
                    400_000_000_000_000_000,
                    "476395313689313848804452264627572572160",
                ),
                (
                    -200_000_000_000_000_000,
                    false,
                    MAX_TICK,
                    -200_000_000_000_000_000,
                    250_000_000_000_000_000,
                    "425352958651173079329218259289710264320",
                ),
                (
                    1_000_000_000_000_000,
                    true,
                    MAX_TICK,
                    -999_000_999_000_998,
                    1_000_000_000_000_000,
                    "340622649287859401860134555468666241024",
                ),
            ],
        );
    }

    #[test]
    fn pool_is_closed_without_a_live_bid() {
        let pool = ContinuousAuctionPool::new(full_range_pool(), auction(ONE_PERCENT)).unwrap();
        // Before the pending bid starts, at its end, and after it.
        for time in [NOW - 1, 512, 1_000] {
            assert_eq!(
                quote(&pool, 1_000, false, MIN_TICK, time).unwrap_err(),
                ContinuousAuctionPoolQuoteError::PoolClosed
            );
        }
        let unrented =
            ContinuousAuctionPool::new(full_range_pool(), ContinuousAuctionState::default())
                .unwrap();
        assert_eq!(
            quote(&unrented, 1_000, false, MIN_TICK, NOW).unwrap_err(),
            ContinuousAuctionPoolQuoteError::PoolClosed
        );
    }

    #[test]
    fn next_bid_takes_over_the_fee_at_its_start() {
        let state = ContinuousAuctionState {
            current_bid: ContinuousAuctionBid {
                start: 50,
                end: 1_000,
                fee: ONE_PERCENT,
            },
            next_bid: Some(ContinuousAuctionBid {
                start: NOW,
                end: 200,
                fee: 0,
            }),
            last_settled: NOW - 1,
        };
        let pool = ContinuousAuctionPool::new(full_range_pool(), state).unwrap();

        // The incumbent keeps the current second.
        let before = quote(&pool, 1_000_000, false, MIN_TICK, NOW - 1).unwrap();
        assert_eq!(before.execution_resources.continuous_auction.settlements, 0);
        assert_eq!(
            before
                .execution_resources
                .continuous_auction
                .fees_accumulated,
            1
        );
        assert_eq!(before.state_after.auction, state);

        // From its start the next bid's zero fee applies and settlement activates it.
        let after = quote(&pool, 1_000_000, false, MIN_TICK, NOW).unwrap();
        assert_eq!(after.fees_paid, 0);
        assert_eq!(
            after
                .execution_resources
                .continuous_auction
                .fees_accumulated,
            0
        );
        assert_eq!(after.execution_resources.continuous_auction.settlements, 1);
        assert_eq!(
            after.state_after.auction,
            ContinuousAuctionState {
                current_bid: state.next_bid.unwrap(),
                next_bid: None,
                last_settled: NOW,
            }
        );
        assert_eq!(
            after.calculated_amount,
            before.calculated_amount + before.fees_paid
        );

        // The next bid's end does not revive the displaced incumbent.
        assert_eq!(
            quote(&pool, 1_000, false, MIN_TICK, 200).unwrap_err(),
            ContinuousAuctionPoolQuoteError::PoolClosed
        );
    }

    #[test]
    fn chained_quotes_reuse_the_settled_state() {
        let pool = ContinuousAuctionPool::new(concentrated_pool(), auction(ONE_PERCENT)).unwrap();
        let first = quote(&pool, 100_000_000_000_000_000, false, MIN_TICK, NOW).unwrap();
        let second = pool
            .quote(QuoteParams {
                token_amount: TokenAmount {
                    token: Evm::zero_address(),
                    amount: 100_000_000_000_000_000,
                },
                sqrt_ratio_limit: None,
                override_state: Some(first.state_after),
                meta: NOW,
            })
            .unwrap();
        assert_eq!(second.execution_resources.continuous_auction.settlements, 0);
        assert_eq!(
            second
                .execution_resources
                .continuous_auction
                .fees_accumulated,
            1
        );
    }

    #[test]
    fn exact_output_rejects_inputs_beyond_int128() {
        // A ~2**95.5 input times 2**32 (the maximum fee) fits u128 but not int128.
        let underlying = FullRangePool::new(
            key(FullRangePoolTypeConfig),
            FullRangePoolState {
                sqrt_ratio: to_sqrt_ratio::<Evm>(0).unwrap(),
                liquidity: 56_000_000_000_000_000_000_000_000_000,
            },
        )
        .unwrap();
        let pool = ContinuousAuctionPool::new(
            underlying,
            ContinuousAuctionState {
                current_bid: ContinuousAuctionBid {
                    start: 0,
                    end: u64::MAX,
                    fee: u32::MAX,
                },
                next_bid: None,
                last_settled: NOW,
            },
        )
        .unwrap();
        assert_eq!(
            quote(
                &pool,
                -28_000_000_000_000_000_000_000_000_000,
                true,
                MIN_TICK,
                NOW
            )
            .unwrap_err(),
            ContinuousAuctionPoolQuoteError::AmountBeforeFeeOverflow
        );
    }

    #[test]
    fn constructor_requires_zero_core_fee_and_extension() {
        let mut key = key(FullRangePoolTypeConfig);
        key.config.fee = 1;
        let state = FullRangePoolState {
            sqrt_ratio: to_sqrt_ratio::<Evm>(0).unwrap(),
            liquidity: 1,
        };
        assert_eq!(
            ContinuousAuctionPool::new(FullRangePool::new(key, state).unwrap(), auction(0))
                .unwrap_err(),
            ContinuousAuctionPoolConstructionError::FeeMustBeZero
        );
        key.config.fee = 0;
        key.config.extension = Evm::zero_address();
        assert_eq!(
            ContinuousAuctionPool::new(FullRangePool::new(key, state).unwrap(), auction(0))
                .unwrap_err(),
            ContinuousAuctionPoolConstructionError::MissingExtension
        );
    }
}
