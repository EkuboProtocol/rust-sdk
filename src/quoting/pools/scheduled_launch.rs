//! Quoting for pools of the `ScheduledLaunch` extension.
//!
//! A launch pool is a concentrated pool whose only position belongs to the extension. Swaps are
//! forwarded to the extension, which first advances the launch (releasing inventory linearly over
//! `[start_time, end_time)`, selling it back down to the target price and adding the rest as
//! liquidity), then swaps on `Core` with buys capped at the top of the launch range, and finally
//! charges a linearly declining creator fee on the calculated side of the swap.
//!
//! The model mirrors `ScheduledLaunch._swap` and the `Core` swap loop step by step, including the
//! tick bitmap word boundaries a swap with `skipAhead` 0 stops at, so it reproduces the
//! contract's deltas, fee and post-swap state exactly.

use derive_more::{Add, AddAssign, Sub, SubAssign};
use num_traits::Zero;
use ruint::aliases::U256;
use thiserror::Error;

use crate::{
    chain::{
        Chain,
        evm::{EVM_FULL_RANGE_TICK_SPACING, EVM_MAX_TICK_SPACING, Evm},
    },
    math::{
        delta::{AmountDeltaError, amount0_delta, amount1_delta},
        muldiv::muldiv,
        sqrt_ratio::{next_sqrt_ratio_from_amount0, next_sqrt_ratio_from_amount1},
        swap::{amount_before_fee, compute_fee, is_price_increasing},
        tick::{sqrt_ratio_to_tick, to_sqrt_ratio},
    },
    private,
    quoting::{
        pools::{
            CommonPoolConstructionError, CommonPoolQuoteError,
            concentrated::{ConcentratedPoolResources, ConcentratedPoolTypeConfig, TickSpacing},
            ensure_valid_token_order, is_token1,
        },
        types::{BlockTimestamp, Pool, PoolConfig, PoolKey, PoolState, Quote, QuoteParams},
    },
};

/// `skipAhead` of the swaps this model quotes. The extension's own inventory sales always use 0,
/// and so does the Yul router's forwarded hop.
const SKIP_AHEAD: u32 = 0;

/// Offset `Core` adds to compressed ticks to index its tick bitmaps.
const TICK_BITMAP_STORAGE_OFFSET: i64 = 89_421_695;

const TWO_POW_128: U256 = U256::from_limbs([0, 0, 1, 0]);

// Initial gas estimates, uncalibrated. Each is Foundry gas of the `Core.forward` frame of a launch
// swap routed through the production Yul router's forwarded hop, measured cold (`--isolate`) on the
// `test/LaunchYulRouter.t.sol` fixture at
// `EkuboProtocol/evm-contracts@40e5bb11f7d4a8b40bb40232027fa7888052eacb`, both token orders. They
// exclude the router, the lock and token settlement. Calibrate against execution before relying on
// them.

/// A launch swap whose advance has nothing to sell or add (measured 60,805-62,645).
pub const SCHEDULED_LAUNCH_SWAP_GAS_UNCALIBRATED: u64 = 62_000;
/// Extra gas when the advance sells released inventory towards the target (measured
/// 18,920-19,044).
pub const SCHEDULED_LAUNCH_INVENTORY_SALE_GAS_UNCALIBRATED: u64 = 19_000;
/// Extra gas when the advance adds liquidity to the existing launch position (measured
/// `updatePosition` 33,727-34,045 plus the saved balance update).
pub const SCHEDULED_LAUNCH_LIQUIDITY_ADDITION_GAS_UNCALIBRATED: u64 = 39_000;
/// Extra gas, on top of a liquidity addition, when it creates the launch position and initializes
/// its ticks: the first advance after the start (measured `updatePosition` 210,049-257,574).
pub const SCHEDULED_LAUNCH_POSITION_CREATION_GAS_UNCALIBRATED: u64 = 200_000;
/// Extra gas per initialized tick crossed.
pub const SCHEDULED_LAUNCH_TICK_CROSSED_GAS_UNCALIBRATED: u64 = 16_350;
/// Extra gas per additional swap step at an uninitialized tick bitmap word boundary, in the user
/// swap or the inventory sale (measured about 4,000 per word walking an empty range).
pub const SCHEDULED_LAUNCH_EXTRA_BITMAP_LOOKUP_GAS_UNCALIBRATED: u64 = 4_000;

/// Launch pool quoted against the state the `ScheduledLaunch` extension and `Core` report.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ScheduledLaunchPool {
    key: ScheduledLaunchPoolKey,
    launch: ScheduledLaunchConfig,
    state: ScheduledLaunchPoolState,
    target_sqrt_ratio: U256,
    lower_sqrt_ratio: U256,
    upper_sqrt_ratio: U256,
}

/// Unique identifier for a [`ScheduledLaunchPool`]. The fee is 0 and the extension is the
/// `ScheduledLaunch` contract.
pub type ScheduledLaunchPoolKey =
    PoolKey<<Evm as Chain>::Address, <Evm as Chain>::Fee, ScheduledLaunchPoolTypeConfig>;
/// Pool configuration for a [`ScheduledLaunchPool`].
pub type ScheduledLaunchPoolConfig =
    PoolConfig<<Evm as Chain>::Address, <Evm as Chain>::Fee, ScheduledLaunchPoolTypeConfig>;
/// Type config for a [`ScheduledLaunchPool`], the tick spacing of the launch pool.
pub type ScheduledLaunchPoolTypeConfig = ConcentratedPoolTypeConfig;

/// Launch parameters as `LaunchCreated` reports them in its `LaunchConfig`.
///
/// `target_tick` and `upper_tick` are in quote units per launch token, independent of token order,
/// exactly as in the contract's `LaunchConfig`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ScheduledLaunchConfig {
    /// Whether the launch token is token1 of the pool.
    pub launch_token_is_token1: bool,
    /// Fixed supply released linearly over the launch.
    pub total_supply: u128,
    /// First second of the launch; the first quotable timestamp.
    pub start_time: u64,
    /// End of the launch; swaps at or after it revert.
    pub end_time: u64,
    /// Price the launch sells released inventory down to.
    pub target_tick: i32,
    /// Top of the launch range; buys stop there.
    pub upper_tick: i32,
    /// Creator fee at `start_time`, a 0.64 fixed point number.
    pub initial_fee: u64,
    /// Creator fee from `end_time`, a 0.64 fixed point number.
    pub final_fee: u64,
}

/// State of a [`ScheduledLaunchPool`]: the launch fields of the last `LaunchAdvanced` and the
/// `Core` pool and position state.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ScheduledLaunchPoolState {
    /// Released supply already sold or added as liquidity.
    pub deployed: u128,
    /// The extension's saved token0 balance for the launch.
    pub reserve0: u128,
    /// The extension's saved token1 balance for the launch.
    pub reserve1: u128,
    /// `Core` pool sqrt ratio, as a fixed point number.
    pub sqrt_ratio: U256,
    /// `Core` pool tick. Not always the floor tick of `sqrt_ratio`.
    pub tick: i32,
    /// `Core` pool active liquidity.
    pub liquidity: u128,
    /// Liquidity of the launch position, the only position in the pool.
    pub position_liquidity: u128,
}

/// Resources of the user swap on `Core`, plus the launch advance it triggers.
#[derive(Clone, Copy, Default, Debug, PartialEq, Eq, Hash, Add, AddAssign, Sub, SubAssign)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ScheduledLaunchPoolResources {
    /// Resources of the user swap on `Core`.
    pub concentrated: ConcentratedPoolResources,
    /// Resources added by the launch extension.
    pub launch: ScheduledLaunchStandalonePoolResources,
}

/// Resources added by the launch extension on top of the `Core` swap.
#[derive(Clone, Copy, Default, Debug, PartialEq, Eq, Hash, Add, AddAssign, Sub, SubAssign)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ScheduledLaunchStandalonePoolResources {
    /// Forwarded launch swaps (1 per quote).
    pub swaps: u32,
    /// Advances that sold released inventory towards the target.
    pub inventory_sales: u32,
    /// Extra swap steps the inventory sales took at uninitialized tick bitmap word boundaries.
    pub inventory_sale_extra_bitmap_lookups: u32,
    /// Advances that added released inventory as liquidity.
    pub liquidity_additions: u32,
    /// Liquidity additions that created the launch position.
    pub position_creations: u32,
}

impl ScheduledLaunchPoolResources {
    /// Initial gas estimate from the Foundry gas of launch swaps through the Yul router.
    ///
    /// Uncalibrated: quoter-service should calibrate it against execution.
    #[must_use]
    pub fn uncalibrated_gas_estimate(&self) -> u64 {
        SCHEDULED_LAUNCH_SWAP_GAS_UNCALIBRATED * u64::from(self.launch.swaps)
            + SCHEDULED_LAUNCH_INVENTORY_SALE_GAS_UNCALIBRATED
                * u64::from(self.launch.inventory_sales)
            + SCHEDULED_LAUNCH_LIQUIDITY_ADDITION_GAS_UNCALIBRATED
                * u64::from(self.launch.liquidity_additions)
            + SCHEDULED_LAUNCH_POSITION_CREATION_GAS_UNCALIBRATED
                * u64::from(self.launch.position_creations)
            + SCHEDULED_LAUNCH_TICK_CROSSED_GAS_UNCALIBRATED
                * u64::from(self.concentrated.initialized_ticks_crossed)
            + SCHEDULED_LAUNCH_EXTRA_BITMAP_LOOKUP_GAS_UNCALIBRATED
                * u64::from(
                    self.concentrated.extra_distinct_bitmap_lookups
                        + self.launch.inventory_sale_extra_bitmap_lookups,
                )
    }
}

/// Errors that can occur when constructing a [`ScheduledLaunchPool`].
#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, Error)]
pub enum ScheduledLaunchPoolConstructionError {
    #[error(transparent)]
    Common(#[from] CommonPoolConstructionError),
    #[error("launch pools have no pool fee")]
    FeeMustBeZero,
    #[error("extension must be non-zero")]
    MissingExtension,
    #[error("tick spacing is invalid")]
    InvalidTickSpacing,
    #[error("launch config is invalid")]
    InvalidLaunchConfig,
    #[error("launch range bounds are not valid ticks for the tick spacing")]
    InvalidLaunchRange,
    #[error("sqrt ratio is invalid")]
    InvalidSqrtRatio,
    #[error("active liquidity does not match the launch position and tick")]
    ActiveLiquidityMismatch,
}

/// Errors that can occur when quoting a [`ScheduledLaunchPool`].
#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, Error)]
pub enum ScheduledLaunchPoolQuoteError {
    #[error(transparent)]
    Common(#[from] CommonPoolQuoteError),
    /// The swap reverts with `LaunchNotStarted`.
    #[error("launch has not started")]
    LaunchNotStarted,
    /// The swap reverts with `LaunchEnded`; quote the terminal pool instead.
    #[error("launch has ended")]
    LaunchEnded,
    #[error("invalid price limit")]
    InvalidSqrtRatioLimit,
    #[error("price limit in the wrong direction")]
    SqrtRatioLimitWrongDirection,
    #[error("amount before fee overflow")]
    AmountBeforeFeeOverflow,
    #[error("amount delta error")]
    AmountDelta(#[from] AmountDeltaError),
    #[error("arithmetic overflow")]
    Overflow,
}

/// `Core` pool state and the launch position, the only liquidity in the pool.
#[derive(Clone, Copy)]
struct CorePool {
    sqrt_ratio: U256,
    tick: i32,
    liquidity: u128,
    position_liquidity: u128,
}

struct SwapOutcome {
    delta0: i128,
    delta1: i128,
    initialized_ticks_crossed: u32,
    extra_bitmap_lookups: u32,
}

impl ScheduledLaunchPool {
    /// Creates a launch pool.
    ///
    /// `key` is the launch pool key, `launch` the `LaunchConfig` from `LaunchCreated` and `state`
    /// the latest launch and `Core` state.
    pub fn new(
        key: ScheduledLaunchPoolKey,
        launch: ScheduledLaunchConfig,
        state: ScheduledLaunchPoolState,
    ) -> Result<Self, ScheduledLaunchPoolConstructionError> {
        ensure_valid_token_order(&key)?;

        let PoolConfig {
            extension,
            fee,
            pool_type_config: TickSpacing(tick_spacing),
        } = key.config;

        if !fee.is_zero() {
            return Err(ScheduledLaunchPoolConstructionError::FeeMustBeZero);
        }
        if extension.is_zero() {
            return Err(ScheduledLaunchPoolConstructionError::MissingExtension);
        }
        if tick_spacing == EVM_FULL_RANGE_TICK_SPACING || tick_spacing > EVM_MAX_TICK_SPACING.0 {
            return Err(ScheduledLaunchPoolConstructionError::InvalidTickSpacing);
        }
        if launch.total_supply.is_zero()
            || launch.end_time <= launch.start_time
            || launch.initial_fee < launch.final_fee
            || launch.target_tick >= launch.upper_tick
        {
            return Err(ScheduledLaunchPoolConstructionError::InvalidLaunchConfig);
        }

        let (lower, upper) = position_bounds(&launch);
        let spacing = tick_spacing as i32;
        if lower % spacing != 0 || upper % spacing != 0 {
            return Err(ScheduledLaunchPoolConstructionError::InvalidLaunchRange);
        }
        let (Some(target_sqrt_ratio), Some(lower_sqrt_ratio), Some(upper_sqrt_ratio)) = (
            to_sqrt_ratio::<Evm>(pool_target_tick(&launch)),
            to_sqrt_ratio::<Evm>(lower),
            to_sqrt_ratio::<Evm>(upper),
        ) else {
            return Err(ScheduledLaunchPoolConstructionError::InvalidLaunchRange);
        };

        if state.sqrt_ratio < Evm::min_sqrt_ratio()
            || state.sqrt_ratio > Evm::max_sqrt_ratio()
            || Evm::adjust_sqrt_ratio_precision(state.sqrt_ratio) != state.sqrt_ratio
        {
            return Err(ScheduledLaunchPoolConstructionError::InvalidSqrtRatio);
        }
        let in_range = state.tick >= lower && state.tick < upper;
        let expected_liquidity = if in_range {
            state.position_liquidity
        } else {
            0
        };
        if state.liquidity != expected_liquidity {
            return Err(ScheduledLaunchPoolConstructionError::ActiveLiquidityMismatch);
        }

        Ok(Self {
            key,
            launch,
            state,
            target_sqrt_ratio,
            lower_sqrt_ratio,
            upper_sqrt_ratio,
        })
    }

    /// The launch parameters.
    #[must_use]
    pub fn launch(&self) -> &ScheduledLaunchConfig {
        &self.launch
    }

    /// Pool tick the launch sells released inventory towards (`Launch.targetTick`).
    #[must_use]
    pub fn pool_target_tick(&self) -> i32 {
        pool_target_tick(&self.launch)
    }

    /// Bounds of the launch position in pool ticks.
    #[must_use]
    pub fn position_bounds(&self) -> (i32, i32) {
        position_bounds(&self.launch)
    }

    /// Cumulative released supply at `time`, including tokens already deployed.
    #[must_use]
    pub fn released(&self, time: u64) -> u128 {
        let launch = &self.launch;
        if time <= launch.start_time {
            return 0;
        }
        if time >= launch.end_time {
            return launch.total_supply;
        }
        // total_supply < 2**128 and the elapsed fraction is below one, so this fits.
        (U256::from(launch.total_supply) * U256::from(time - launch.start_time)
            / U256::from(launch.end_time - launch.start_time))
        .to()
    }

    /// Creator fee charged at `time`, a 0.64 fixed point number.
    #[must_use]
    pub fn fee_at(&self, time: u64) -> u64 {
        let launch = &self.launch;
        if time <= launch.start_time {
            return launch.initial_fee;
        }
        if time >= launch.end_time {
            return launch.final_fee;
        }
        let decline = U256::from(launch.initial_fee - launch.final_fee)
            * U256::from(time - launch.start_time)
            / U256::from(launch.end_time - launch.start_time);
        launch.initial_fee - decline.to::<u64>()
    }

    /// Applies the advance that precedes every launch swap at `time`.
    fn advance(
        &self,
        state: &mut ScheduledLaunchPoolState,
        time: u64,
        resources: &mut ScheduledLaunchStandalonePoolResources,
    ) -> Result<(), ScheduledLaunchPoolQuoteError> {
        let available = self.available(state, time)?;
        if available != 0
            && let Some(extra_bitmap_lookups) = self.sell(state, available)?
        {
            resources.inventory_sales += 1;
            resources.inventory_sale_extra_bitmap_lookups += extra_bitmap_lookups;
        }
        let creates_position = state.position_liquidity == 0;
        if self.add_liquidity(state, time)? {
            resources.liquidity_additions += 1;
            resources.position_creations += u32::from(creates_position);
        }
        Ok(())
    }

    fn available(
        &self,
        state: &ScheduledLaunchPoolState,
        time: u64,
    ) -> Result<u128, ScheduledLaunchPoolQuoteError> {
        self.released(time)
            .checked_sub(state.deployed)
            .ok_or(ScheduledLaunchPoolQuoteError::Overflow)
    }

    /// `_sell`: sells released inventory towards the target with an exact-input swap. Returns the
    /// sale's extra bitmap lookups if it swapped.
    fn sell(
        &self,
        state: &mut ScheduledLaunchPoolState,
        available: u128,
    ) -> Result<Option<u32>, ScheduledLaunchPoolQuoteError> {
        let token_is1 = self.launch.launch_token_is_token1;
        let current = state.sqrt_ratio;
        let target = self.target_sqrt_ratio;
        if (token_is1 && current >= target) || (!token_is1 && current <= target) {
            return Ok(None);
        }
        let quote_reserve = if token_is1 {
            state.reserve0
        } else {
            state.reserve1
        };
        if quote_reserve > i128::MAX as u128 {
            return Ok(None);
        }
        let amount = sale_amount(current, token_is1, available)?;
        if amount == 0 {
            return Ok(None);
        }

        let mut pool = core_pool(state);
        let outcome = self.core_swap(&mut pool, amount, token_is1, target, SKIP_AHEAD)?;
        set_core_pool(state, pool);
        save_update(state, token_is1, outcome.delta0, outcome.delta1)?;
        Ok(Some(outcome.extra_bitmap_lookups))
    }

    /// `_addLiquidity`: adds the reserves at hand, with the launch side limited to released
    /// inventory, to the launch position.
    fn add_liquidity(
        &self,
        state: &mut ScheduledLaunchPoolState,
        time: u64,
    ) -> Result<bool, ScheduledLaunchPoolQuoteError> {
        let available = self.available(state, time)?;
        let (mut amount0, mut amount1) = (state.reserve0, state.reserve1);
        if self.launch.launch_token_is_token1 {
            amount1 = available;
        } else {
            amount0 = available;
        }

        let liquidity = max_liquidity(
            state.sqrt_ratio,
            self.lower_sqrt_ratio,
            self.upper_sqrt_ratio,
            amount0.min(i128::MAX as u128),
            amount1.min(i128::MAX as u128),
        )?;
        let capacity = max_liquidity_per_tick(self.key.config.pool_type_config.0)
            .saturating_sub(state.position_liquidity);
        let liquidity = liquidity.min(capacity);
        if liquidity == 0 {
            return Ok(false);
        }

        let (delta0, delta1) = self.liquidity_delta_amounts(state.sqrt_ratio, liquidity)?;
        let (lower, upper) = self.position_bounds();
        state.position_liquidity += liquidity;
        if state.tick >= lower && state.tick < upper {
            state.liquidity = state
                .liquidity
                .checked_add(liquidity)
                .ok_or(ScheduledLaunchPoolQuoteError::Overflow)?;
        }
        save_update(
            state,
            self.launch.launch_token_is_token1,
            to_i128(delta0)?,
            to_i128(delta1)?,
        )?;
        Ok(true)
    }

    /// Amounts `Core.updatePosition` takes for adding `liquidity`, rounded up.
    fn liquidity_delta_amounts(
        &self,
        sqrt_ratio: U256,
        liquidity: u128,
    ) -> Result<(u128, u128), ScheduledLaunchPoolQuoteError> {
        let (lower, upper) = (self.lower_sqrt_ratio, self.upper_sqrt_ratio);
        Ok(if sqrt_ratio <= lower {
            (amount0_delta(lower, upper, liquidity, true)?, 0)
        } else if sqrt_ratio < upper {
            (
                amount0_delta(sqrt_ratio, upper, liquidity, true)?,
                amount1_delta(lower, sqrt_ratio, liquidity, true)?,
            )
        } else {
            (0, amount1_delta(lower, upper, liquidity, true)?)
        })
    }

    /// `_withinRange`: buys stop at the top of the launch range.
    fn within_range(&self, is_increasing: bool, limit: U256) -> U256 {
        let token_is1 = self.launch.launch_token_is_token1;
        if is_increasing == token_is1 {
            return limit;
        }
        let top = if token_is1 {
            self.lower_sqrt_ratio
        } else {
            self.upper_sqrt_ratio
        };
        if (token_is1 && limit >= top) || (!token_is1 && limit <= top) {
            limit
        } else {
            top
        }
    }

    /// Ticks the launch position initializes, with their liquidity deltas.
    fn initialized_ticks(&self, position_liquidity: u128) -> [(i32, i128); 2] {
        let (lower, upper) = self.position_bounds();
        // Liquidity is capped at Core's per-tick maximum, far below i128::MAX.
        let net = position_liquidity as i128;
        [(lower, net), (upper, -net)]
    }

    /// `Core.swap` on the launch pool with a zero pool fee.
    fn core_swap(
        &self,
        pool: &mut CorePool,
        amount: i128,
        is_token1: bool,
        sqrt_ratio_limit: U256,
        skip_ahead: u32,
    ) -> Result<SwapOutcome, ScheduledLaunchPoolQuoteError> {
        let mut outcome = SwapOutcome {
            delta0: 0,
            delta1: 0,
            initialized_ticks_crossed: 0,
            extra_bitmap_lookups: 0,
        };
        if amount == 0 || pool.sqrt_ratio == sqrt_ratio_limit {
            return Ok(outcome);
        }

        let increasing = is_price_increasing(amount, is_token1);
        if (sqrt_ratio_limit < pool.sqrt_ratio) == increasing {
            return Err(ScheduledLaunchPoolQuoteError::SqrtRatioLimitWrongDirection);
        }

        let spacing = self.key.config.pool_type_config.0;
        let ticks = if pool.position_liquidity == 0 {
            None
        } else {
            Some(self.initialized_ticks(pool.position_liquidity))
        };
        let initialized = ticks.as_ref().map_or(&[][..], |t| &t[..]);

        let mut amount_remaining = amount;
        let mut calculated: i128 = 0;
        let mut steps: u32 = 0;

        loop {
            let (next_tick, is_initialized) = if increasing {
                find_next_initialized_tick(initialized, pool.tick, spacing, skip_ahead)
            } else {
                find_prev_initialized_tick(initialized, pool.tick, spacing, skip_ahead)
            };
            let next_tick_sqrt_ratio =
                to_sqrt_ratio::<Evm>(next_tick).ok_or(ScheduledLaunchPoolQuoteError::Overflow)?;
            let limited = if increasing {
                next_tick_sqrt_ratio.min(sqrt_ratio_limit)
            } else {
                next_tick_sqrt_ratio.max(sqrt_ratio_limit)
            };

            let sqrt_ratio_next = if pool.liquidity == 0 {
                limited
            } else {
                let step = swap_step(
                    pool.sqrt_ratio,
                    pool.liquidity,
                    limited,
                    amount_remaining,
                    is_token1,
                    increasing,
                )?;
                amount_remaining = step.amount_remaining;
                calculated = calculated
                    .checked_add(step.calculated_delta)
                    .ok_or(ScheduledLaunchPoolQuoteError::Overflow)?;
                step.sqrt_ratio_next
            };
            steps += 1;

            if sqrt_ratio_next == next_tick_sqrt_ratio {
                pool.sqrt_ratio = sqrt_ratio_next;
                pool.tick = next_tick - i32::from(!increasing);
                if is_initialized {
                    let (_, net) = initialized
                        .iter()
                        .find(|(index, _)| *index == next_tick)
                        .copied()
                        .unwrap_or_default();
                    let delta = if increasing { net } else { -net };
                    pool.liquidity = pool
                        .liquidity
                        .checked_add_signed(delta)
                        .ok_or(ScheduledLaunchPoolQuoteError::Overflow)?;
                    outcome.initialized_ticks_crossed += 1;
                }
            } else if pool.sqrt_ratio != sqrt_ratio_next {
                pool.sqrt_ratio = sqrt_ratio_next;
                pool.tick = sqrt_ratio_to_tick::<Evm>(sqrt_ratio_next);
            }

            if amount_remaining == 0 || pool.sqrt_ratio == sqrt_ratio_limit {
                break;
            }
        }

        let specified = amount - amount_remaining;
        (outcome.delta0, outcome.delta1) = if is_token1 {
            (calculated, specified)
        } else {
            (specified, calculated)
        };
        outcome.extra_bitmap_lookups = steps
            .saturating_sub(1)
            .saturating_sub(outcome.initialized_ticks_crossed);
        Ok(outcome)
    }
}

/// The result of one iteration of `Core`'s swap loop with non-zero liquidity and a zero fee.
struct Step {
    amount_remaining: i128,
    calculated_delta: i128,
    sqrt_ratio_next: U256,
}

fn swap_step(
    sqrt_ratio: U256,
    liquidity: u128,
    limited: U256,
    amount_remaining: i128,
    is_token1: bool,
    increasing: bool,
) -> Result<Step, ScheduledLaunchPoolQuoteError> {
    // Launch pools have a zero pool fee, so the whole remaining amount moves the price.
    const FEE: u64 = 0;
    let is_exact_out = amount_remaining < 0;
    let price_impact = if is_exact_out {
        amount_remaining
    } else {
        amount_remaining - to_i128(compute_fee::<Evm>(amount_remaining.unsigned_abs(), FEE))?
    };

    let from_amount = if is_token1 {
        next_sqrt_ratio_from_amount1(sqrt_ratio, liquidity, price_impact)
            .map(|next| Evm::round_sqrt_ratio(next, false))
    } else {
        next_sqrt_ratio_from_amount0(sqrt_ratio, liquidity, price_impact)
            .map(|next| Evm::round_sqrt_ratio(next, true))
    };
    let hit_limit = from_amount.map_or(true, |next| {
        if increasing {
            next > limited
        } else {
            next < limited
        }
    });

    if hit_limit {
        let (specified, calculated) = if is_token1 {
            (
                amount1_delta(limited, sqrt_ratio, liquidity, !is_exact_out)?,
                amount0_delta(limited, sqrt_ratio, liquidity, is_exact_out)?,
            )
        } else {
            (
                amount0_delta(limited, sqrt_ratio, liquidity, !is_exact_out)?,
                amount1_delta(limited, sqrt_ratio, liquidity, is_exact_out)?,
            )
        };
        let (amount_remaining, calculated_delta) = if is_exact_out {
            let before_fee = amount_before_fee::<Evm>(calculated, FEE)
                .ok_or(ScheduledLaunchPoolQuoteError::AmountBeforeFeeOverflow)?;
            (amount_remaining + to_i128(specified)?, to_i128(before_fee)?)
        } else {
            let before_fee = amount_before_fee::<Evm>(specified, FEE)
                .ok_or(ScheduledLaunchPoolQuoteError::AmountBeforeFeeOverflow)?;
            (
                amount_remaining - to_i128(before_fee)?,
                -to_i128(calculated)?,
            )
        };
        return Ok(Step {
            amount_remaining,
            calculated_delta,
            sqrt_ratio_next: limited,
        });
    }

    // `hit_limit` is false only for a computed ratio.
    let next = from_amount.unwrap_or(limited);
    if next == sqrt_ratio {
        // The price did not move: Core takes the entire exact input as fees.
        return Ok(Step {
            amount_remaining: 0,
            calculated_delta: 0,
            sqrt_ratio_next: sqrt_ratio,
        });
    }

    let without_fee = if is_token1 {
        amount0_delta(next, sqrt_ratio, liquidity, is_exact_out)?
    } else {
        amount1_delta(next, sqrt_ratio, liquidity, is_exact_out)?
    };
    let calculated_delta = if is_exact_out {
        to_i128(
            amount_before_fee::<Evm>(without_fee, FEE)
                .ok_or(ScheduledLaunchPoolQuoteError::AmountBeforeFeeOverflow)?,
        )?
    } else {
        -to_i128(without_fee)?
    };
    Ok(Step {
        amount_remaining: 0,
        calculated_delta,
        sqrt_ratio_next: next,
    })
}

fn pool_target_tick(launch: &ScheduledLaunchConfig) -> i32 {
    if launch.launch_token_is_token1 {
        -launch.target_tick
    } else {
        launch.target_tick
    }
}

fn position_bounds(launch: &ScheduledLaunchConfig) -> (i32, i32) {
    if launch.launch_token_is_token1 {
        (-launch.upper_tick, -launch.target_tick)
    } else {
        (launch.target_tick, launch.upper_tick)
    }
}

fn core_pool(state: &ScheduledLaunchPoolState) -> CorePool {
    CorePool {
        sqrt_ratio: state.sqrt_ratio,
        tick: state.tick,
        liquidity: state.liquidity,
        position_liquidity: state.position_liquidity,
    }
}

fn set_core_pool(state: &mut ScheduledLaunchPoolState, pool: CorePool) {
    state.sqrt_ratio = pool.sqrt_ratio;
    state.tick = pool.tick;
    state.liquidity = pool.liquidity;
}

/// `_saveUpdate`: the launch pays a `Core` balance update from its saved balances.
fn save_update(
    state: &mut ScheduledLaunchPoolState,
    launch_token_is_token1: bool,
    delta0: i128,
    delta1: i128,
) -> Result<(), ScheduledLaunchPoolQuoteError> {
    let spent = if launch_token_is_token1 {
        delta1
    } else {
        delta0
    };
    state.deployed = state
        .deployed
        .checked_add_signed(spent)
        .ok_or(ScheduledLaunchPoolQuoteError::Overflow)?;
    state.reserve0 = state
        .reserve0
        .checked_add_signed(-delta0)
        .ok_or(ScheduledLaunchPoolQuoteError::Overflow)?;
    state.reserve1 = state
        .reserve1
        .checked_add_signed(-delta1)
        .ok_or(ScheduledLaunchPoolQuoteError::Overflow)?;
    Ok(())
}

/// `_saleAmount`: input such that the output at the current price fits a signed delta.
fn sale_amount(
    current: U256,
    token_is1: bool,
    available: u128,
) -> Result<i128, ScheduledLaunchPoolQuoteError> {
    let (numerator, denominator) = if token_is1 {
        (current, TWO_POW_128)
    } else {
        (TWO_POW_128, current)
    };
    let limit = muldiv(U256::from(i128::MAX), numerator, denominator, false)
        .map_err(|_| ScheduledLaunchPoolQuoteError::Overflow)?;
    let limit = muldiv(limit, numerator, denominator, false)
        .map_err(|_| ScheduledLaunchPoolQuoteError::Overflow)?;
    // Bounded by available < 2**128 and the saved launch balance, which fits in an int128.
    to_i128(U256::from(available).min(limit).to())
}

/// `maxLiquidity` from `math/liquidity.sol`.
fn max_liquidity(
    sqrt_ratio: U256,
    lower: U256,
    upper: U256,
    amount0: u128,
    amount1: u128,
) -> Result<u128, ScheduledLaunchPoolQuoteError> {
    let liquidity = if sqrt_ratio <= lower {
        max_liquidity_for_token0(lower, upper, amount0)?
    } else if sqrt_ratio < upper {
        max_liquidity_for_token0(sqrt_ratio, upper, amount0)?
            .min(max_liquidity_for_token1(lower, sqrt_ratio, amount1))
    } else {
        max_liquidity_for_token1(lower, upper, amount1)
    };
    Ok(liquidity.min(U256::from(u128::MAX)).to())
}

fn max_liquidity_for_token0(
    lower: U256,
    upper: U256,
    amount: u128,
) -> Result<U256, ScheduledLaunchPoolQuoteError> {
    let numerator = muldiv(lower, upper, TWO_POW_128, false)
        .map_err(|_| ScheduledLaunchPoolQuoteError::Overflow)?;
    muldiv(U256::from(amount), numerator, upper - lower, false)
        .map_err(|_| ScheduledLaunchPoolQuoteError::Overflow)
}

fn max_liquidity_for_token1(lower: U256, upper: U256, amount: u128) -> U256 {
    (U256::from(amount) << 128) / (upper - lower)
}

/// `concentratedMaxLiquidityPerTick` of the pool config.
fn max_liquidity_per_tick(tick_spacing: u32) -> u128 {
    let ticks = 1 + (Evm::max_tick() as u32 / tick_spacing) as u128 * 2;
    u128::MAX / ticks
}

/// `tickToBitmapWordAndIndex`, as one contiguous raw bitmap index.
fn bitmap_raw_index(tick: i32, tick_spacing: u32) -> i64 {
    i64::from(tick).div_euclid(i64::from(tick_spacing)) + TICK_BITMAP_STORAGE_OFFSET
}

fn bitmap_raw_index_to_tick(raw_index: i64, tick_spacing: u32) -> i32 {
    // Raw indices of valid ticks map back into the tick range.
    ((raw_index - TICK_BITMAP_STORAGE_OFFSET) * i64::from(tick_spacing)) as i32
}

/// `findNextInitializedTick` over a bitmap holding only `initialized`.
fn find_next_initialized_tick(
    initialized: &[(i32, i128)],
    from_tick: i32,
    tick_spacing: u32,
    mut skip_ahead: u32,
) -> (i32, bool) {
    let mut next_tick = from_tick;
    loop {
        let raw = bitmap_raw_index(next_tick + tick_spacing as i32, tick_spacing);
        let word_end = (raw >> 8 << 8) + 255;
        let found = initialized
            .iter()
            .map(|(tick, _)| bitmap_raw_index(*tick, tick_spacing))
            .filter(|index| *index >= raw && *index <= word_end)
            .min();
        if let Some(index) = found {
            return (bitmap_raw_index_to_tick(index, tick_spacing), true);
        }
        next_tick = bitmap_raw_index_to_tick(word_end, tick_spacing);
        if next_tick >= Evm::max_tick() {
            return (Evm::max_tick(), false);
        }
        if skip_ahead == 0 {
            return (next_tick, false);
        }
        skip_ahead -= 1;
    }
}

/// `findPrevInitializedTick` over a bitmap holding only `initialized`.
fn find_prev_initialized_tick(
    initialized: &[(i32, i128)],
    from_tick: i32,
    tick_spacing: u32,
    mut skip_ahead: u32,
) -> (i32, bool) {
    let mut prev_tick = from_tick;
    loop {
        let raw = bitmap_raw_index(prev_tick, tick_spacing);
        let word_start = raw >> 8 << 8;
        let found = initialized
            .iter()
            .map(|(tick, _)| bitmap_raw_index(*tick, tick_spacing))
            .filter(|index| *index >= word_start && *index <= raw)
            .max();
        if let Some(index) = found {
            return (bitmap_raw_index_to_tick(index, tick_spacing), true);
        }
        prev_tick = bitmap_raw_index_to_tick(word_start, tick_spacing);
        if prev_tick <= Evm::min_tick() {
            return (Evm::min_tick(), false);
        }
        if skip_ahead == 0 {
            return (prev_tick, false);
        }
        skip_ahead -= 1;
        prev_tick -= 1;
    }
}

fn to_i128(value: u128) -> Result<i128, ScheduledLaunchPoolQuoteError> {
    i128::try_from(value).map_err(|_| ScheduledLaunchPoolQuoteError::Overflow)
}

impl Pool for ScheduledLaunchPool {
    type Address = <Evm as Chain>::Address;
    type Fee = <Evm as Chain>::Fee;
    type Resources = ScheduledLaunchPoolResources;
    type State = ScheduledLaunchPoolState;
    type QuoteError = ScheduledLaunchPoolQuoteError;
    type Meta = BlockTimestamp;
    type PoolTypeConfig = ScheduledLaunchPoolTypeConfig;

    fn key(&self) -> ScheduledLaunchPoolKey {
        self.key
    }

    fn state(&self) -> Self::State {
        self.state
    }

    /// Quotes the forwarded launch swap at block timestamp `meta`.
    ///
    /// `consumed_amount` is the specified amount the swap fills, which is less than requested
    /// when a buy reaches the top of the launch range. `calculated_amount` includes the creator
    /// fee and `fees_paid` is the creator fee.
    fn quote(
        &self,
        params: QuoteParams<Self::Address, Self::State, Self::Meta>,
    ) -> Result<Quote<Self::Resources, Self::State>, Self::QuoteError> {
        let time = params.meta;
        if time < self.launch.start_time {
            return Err(ScheduledLaunchPoolQuoteError::LaunchNotStarted);
        }
        if time >= self.launch.end_time {
            return Err(ScheduledLaunchPoolQuoteError::LaunchEnded);
        }

        let amount = params.token_amount.amount;
        let is_token1 = is_token1(&self.key, params.token_amount.token)?;
        let is_increasing = is_price_increasing(amount, is_token1);

        let sqrt_ratio_limit = match params.sqrt_ratio_limit {
            Some(limit) => {
                if limit < Evm::min_sqrt_ratio()
                    || limit > Evm::max_sqrt_ratio()
                    || Evm::adjust_sqrt_ratio_precision(limit) != limit
                {
                    return Err(ScheduledLaunchPoolQuoteError::InvalidSqrtRatioLimit);
                }
                limit
            }
            None if is_increasing => Evm::max_sqrt_ratio(),
            None => Evm::min_sqrt_ratio(),
        };

        let initial = params.override_state.unwrap_or(self.state);
        let mut state = initial;
        let mut launch_resources = ScheduledLaunchStandalonePoolResources {
            swaps: 1,
            ..Default::default()
        };
        self.advance(&mut state, time, &mut launch_resources)?;

        let mut pool = core_pool(&state);
        let starting_sqrt_ratio = pool.sqrt_ratio;
        let outcome = self.core_swap(
            &mut pool,
            amount,
            is_token1,
            self.within_range(is_increasing, sqrt_ratio_limit),
            SKIP_AHEAD,
        )?;
        set_core_pool(&mut state, pool);

        // `_chargeFee`: the creator fee is taken on the calculated side.
        let (specified, calculated) = if is_token1 {
            (outcome.delta1, outcome.delta0)
        } else {
            (outcome.delta0, outcome.delta1)
        };
        let calculated_abs = calculated.unsigned_abs();
        let fee = self.fee_at(time);
        let fee_amount = if amount < 0 {
            amount_before_fee::<Evm>(calculated_abs, fee)
                .ok_or(ScheduledLaunchPoolQuoteError::AmountBeforeFeeOverflow)?
                - calculated_abs
        } else {
            compute_fee::<Evm>(calculated_abs, fee)
        };
        let with_fee = calculated
            .checked_add(to_i128(fee_amount)?)
            .ok_or(ScheduledLaunchPoolQuoteError::Overflow)?;

        Ok(Quote {
            is_price_increasing: is_increasing,
            consumed_amount: specified,
            calculated_amount: with_fee.unsigned_abs(),
            execution_resources: ScheduledLaunchPoolResources {
                concentrated: ConcentratedPoolResources {
                    no_override_price_change: u32::from(
                        initial == self.state && starting_sqrt_ratio != pool.sqrt_ratio,
                    ),
                    initialized_ticks_crossed: outcome.initialized_ticks_crossed,
                    extra_distinct_bitmap_lookups: outcome.extra_bitmap_lookups,
                },
                launch: launch_resources,
            },
            state_after: state,
            fees_paid: fee_amount,
        })
    }

    fn has_liquidity(&self) -> bool {
        self.state.position_liquidity != 0 || self.state.deployed < self.launch.total_supply
    }

    fn max_tick_with_liquidity(&self) -> Option<i32> {
        Some(self.position_bounds().1)
    }

    fn min_tick_with_liquidity(&self) -> Option<i32> {
        Some(self.position_bounds().0)
    }

    fn is_path_dependent(&self) -> bool {
        true
    }
}

impl PoolState for ScheduledLaunchPoolState {
    fn sqrt_ratio(&self) -> U256 {
        self.sqrt_ratio
    }

    fn liquidity(&self) -> u128 {
        self.liquidity
    }
}

impl private::Sealed for ScheduledLaunchPool {}
impl private::Sealed for ScheduledLaunchPoolState {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{chain::tests::ChainTest, quoting::types::TokenAmount};

    const SUPPLY: u128 = 1_000_000_000_000_000_000_000_000;
    const ONE: i128 = 1_000_000_000_000_000_000;

    /// The launch of the contract tests: the launch token is token1 and the quote token is the
    /// native token.
    fn launch_pool() -> ScheduledLaunchPool {
        ScheduledLaunchPool::new(
            PoolKey {
                token0: Evm::zero_address(),
                token1: Evm::one_address(),
                config: PoolConfig {
                    extension: Evm::one_address(),
                    fee: 0,
                    pool_type_config: TickSpacing(100),
                },
            },
            ScheduledLaunchConfig {
                launch_token_is_token1: true,
                total_supply: SUPPLY,
                start_time: 100,
                end_time: 1_100,
                target_tick: 0,
                upper_tick: 100_000,
                initial_fee: ((1u128 << 64) / 10) as u64,
                final_fee: ((1u128 << 64) / 100) as u64,
            },
            ScheduledLaunchPoolState {
                deployed: 0,
                reserve0: 0,
                reserve1: SUPPLY,
                sqrt_ratio: to_sqrt_ratio::<Evm>(0).unwrap(),
                tick: 0,
                liquidity: 0,
                position_liquidity: 0,
            },
        )
        .unwrap()
    }

    fn buy(
        pool: &ScheduledLaunchPool,
        state: Option<ScheduledLaunchPoolState>,
        time: u64,
        amount: i128,
    ) -> Result<
        Quote<ScheduledLaunchPoolResources, ScheduledLaunchPoolState>,
        ScheduledLaunchPoolQuoteError,
    > {
        pool.quote(QuoteParams {
            token_amount: TokenAmount {
                token: Evm::zero_address(),
                amount,
            },
            sqrt_ratio_limit: None,
            override_state: state,
            meta: time,
        })
    }

    #[test]
    fn quotable_only_during_the_launch() {
        let pool = launch_pool();
        assert_eq!(
            buy(&pool, None, 99, ONE),
            Err(ScheduledLaunchPoolQuoteError::LaunchNotStarted)
        );
        assert!(buy(&pool, None, 100, ONE).is_ok());
        assert!(buy(&pool, None, 1_099, ONE).is_ok());
        assert_eq!(
            buy(&pool, None, 1_100, ONE),
            Err(ScheduledLaunchPoolQuoteError::LaunchEnded)
        );
    }

    #[test]
    fn buys_fill_partially_at_the_range_top() {
        let pool = launch_pool();
        let requested = 900_000 * ONE;
        let first = buy(&pool, None, 200, requested).unwrap();
        assert!(first.consumed_amount > 0 && first.consumed_amount < requested);
        assert!(first.calculated_amount > 0);
        assert_eq!(first.state_after.tick, -100_001);

        // Nothing is on offer above the range until more inventory is released.
        let second = buy(&pool, Some(first.state_after), 200, requested).unwrap();
        assert_eq!((second.consumed_amount, second.calculated_amount), (0, 0));
        assert_eq!(second.state_after, first.state_after);
    }

    #[test]
    fn resources_follow_the_advance() {
        let pool = launch_pool();
        let first = buy(&pool, None, 400, 1_000 * ONE).unwrap();
        assert_eq!(
            first.execution_resources.launch,
            ScheduledLaunchStandalonePoolResources {
                swaps: 1,
                inventory_sales: 0,
                inventory_sale_extra_bitmap_lookups: 0,
                liquidity_additions: 1,
                position_creations: 1,
            }
        );

        // The buy moved the price above the target, so the next release is sold down first.
        let next = buy(&pool, Some(first.state_after), 401, 1_000 * ONE).unwrap();
        assert_eq!(next.execution_resources.launch.inventory_sales, 1);
        assert_eq!(next.execution_resources.launch.position_creations, 0);
        assert_eq!(
            next.execution_resources
                .concentrated
                .no_override_price_change,
            0
        );
        assert!(
            first.execution_resources.uncalibrated_gas_estimate()
                > next.execution_resources.uncalibrated_gas_estimate()
        );

        // A second swap in the same second has nothing left to release.
        let same = buy(&pool, Some(first.state_after), 400, 1_000 * ONE).unwrap();
        assert_eq!(
            same.execution_resources.launch,
            ScheduledLaunchStandalonePoolResources {
                swaps: 1,
                ..Default::default()
            }
        );
    }

    #[test]
    fn bitmap_search_matches_core_word_boundaries() {
        // Tick 0 is raw index 89_421_695 = 349_303 * 256 + 127 for every spacing.
        assert_eq!(find_next_initialized_tick(&[], 0, 100, 0), (12_800, false));
        assert_eq!(find_prev_initialized_tick(&[], 0, 100, 0), (-12_700, false));
        assert_eq!(
            find_next_initialized_tick(&[(0, 1), (100_000, -1)], 0, 100, 0),
            (12_800, false)
        );
        assert_eq!(
            find_next_initialized_tick(&[(0, 1), (100, -1)], 0, 100, 0),
            (100, true)
        );
        assert_eq!(
            find_prev_initialized_tick(&[(0, 1), (100, -1)], 99, 100, 0),
            (0, true)
        );
        assert_eq!(
            find_prev_initialized_tick(&[(0, 1), (100, -1)], -1, 100, 0),
            (-12_700, false)
        );
        assert_eq!(
            find_next_initialized_tick(&[], Evm::max_tick() - 1, 1, 0),
            (Evm::max_tick(), false)
        );
        assert_eq!(
            find_prev_initialized_tick(&[], Evm::min_tick(), 1, 0),
            (Evm::min_tick(), false)
        );
    }

    #[test]
    fn max_liquidity_per_tick_matches_core() {
        assert_eq!(
            max_liquidity_per_tick(100),
            u128::MAX / (1 + (88_722_835 / 100) * 2)
        );
    }
}
