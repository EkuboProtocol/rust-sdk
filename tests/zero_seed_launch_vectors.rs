//! Reproduces the `ZeroSeedLaunch` vectors in `tests/vectors`: the contract's frozen integer
//! vectors, the parity vectors read from local `Core`, extension and periphery state and events,
//! the indexer's LOCAL anvil receipt of the two supported instances, and the pinned ABIs.
#![cfg(any(feature = "evm-alloy-0_6", feature = "evm-alloy-1"))]

use core::str::FromStr;
use std::collections::HashMap;

use ekubo_sdk::{
    U256,
    alloy_primitives::{Address, B256, hex, keccak256},
    chain::evm::{Evm, EvmZeroSeedLaunchPool, EvmZeroSeedLaunchPoolKey},
    math::tick::to_sqrt_ratio,
    quoting::{
        pools::{
            concentrated::TickSpacing,
            zero_seed_launch::{
                MINTABLE_ERC20_CREATION_CODE, MINTABLE_ERC20_CREATION_CODE_KECCAK,
                ZeroSeedLaunchConfig, ZeroSeedLaunchFeeSchedule, ZeroSeedLaunchFullFillError,
                ZeroSeedLaunchInstance, ZeroSeedLaunchLocalPreview, ZeroSeedLaunchParameterError,
                ZeroSeedLaunchParameters, ZeroSeedLaunchPoolConstructionError,
                ZeroSeedLaunchPoolQuoteError, ZeroSeedLaunchPoolState, ZeroSeedLaunchQuoteKind,
                ZeroSeedLaunchRange, check_launch_binding, check_launch_binding_math,
                extension_token_salt, launch_token_address, periphery_launch_salt,
                periphery_launch_token_address, preview_installation, preview_installation_math,
                validate_claim_recipient,
            },
        },
        types::{Pool, PoolConfig, PoolKey, QuoteParams, TokenAmount},
    },
};
use serde_json::Value;
use sha2::{Digest, Sha256};

const FROZEN: &str = include_str!("vectors/zero-seed-launch.json");
const PARITY: &str = include_str!("vectors/zero-seed-launch-parity.json");
const INDEXER: &str = include_str!("vectors/zero-seed-launch-indexer.json");
const PINS: &str = include_str!("vectors/pins/pins.json");
const ABI_LAUNCH: &str = include_str!("vectors/pins/ZeroSeedLaunch.abi.json");
const ABI_PERIPHERY: &str = include_str!("vectors/pins/ZeroSeedLaunchPeriphery.abi.json");
const ABI_TOKEN: &str = include_str!("vectors/pins/MintableERC20.abi.json");

/// Fixture quote tokens of the contract tests: the high one makes the launch token token0.
const QUOTE_HIGH: &str = "0xffffffffffffffffffffffffffffffffffffffff";
const QUOTE_LOW: &str = "0x0000000000000000000000000000000000010000";

const TRANSFER_FROM_FAILED: &str = "0x7939f424";
const TRADING_NOT_STARTED: &str = "0xacf75be8";
const SQRT_RATIO_LIMIT_WRONG_DIRECTION: &str = "0xa574a6b4";
/// solady `SafeCastLib.Overflow()`: a delta does not fit an int128.
const SAFE_CAST_OVERFLOW: &str = "0x35278d12";

const LAUNCH_CREATED: &str = "0x085ada2e6f98dc43ec420caff7f39c25cbc16c81595684b19c4fca014dae5f2d";
const LAUNCH_SWAPPED: &str = "0x3e58795f52a8e88efdec2da89ea3798175f8764145ccd7bf5e40633a7d571f6d";
const CREATOR_FEES_CLAIMED: &str =
    "0xf0ffdfa84530baef2e9f8bbb160545a59bfef8da319fa27aa69e4f3c8f05a41d";
const LAUNCH_OWNER_CHANGED: &str =
    "0x478004cf03e8c3b648608ce0259ce479c813aa671a383230ee7763fe5da22391";
const LAUNCH_FEES_CLAIMED: &str =
    "0x908c6b2c19765fe47aef218b4f71ea1a10a9e156d9d5c3500c3a298e01428805";

fn address(s: &str) -> Address {
    Address::from_str(s).unwrap()
}

fn b256(s: &str) -> B256 {
    B256::from_str(s).unwrap()
}

fn s<'a>(v: &'a Value, field: &str) -> &'a str {
    v[field]
        .as_str()
        .unwrap_or_else(|| panic!("{field} is not a string in {v}"))
}

fn num<T: FromStr>(v: &Value, field: &str) -> T
where
    T::Err: core::fmt::Debug,
{
    match &v[field] {
        Value::String(x) => x.parse().unwrap(),
        Value::Number(x) => x.to_string().parse().unwrap(),
        other => panic!("{field} is {other}"),
    }
}

fn hex_u64(v: &Value, field: &str) -> u64 {
    u64::from_str_radix(&s(v, field)[2..], 16).unwrap()
}

fn sha256_hex(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect()
}

fn state(v: &Value) -> ZeroSeedLaunchPoolState {
    ZeroSeedLaunchPoolState {
        sqrt_ratio: U256::from_str(s(v, "sqrt_ratio")).unwrap(),
        tick: num(v, "tick"),
        liquidity: num(v, "liquidity"),
    }
}

fn fee_schedule(v: &Value) -> ZeroSeedLaunchFeeSchedule {
    ZeroSeedLaunchFeeSchedule {
        trading_start: num(v, "tradingStart"),
        fee_duration: num(v, "feeDuration"),
        initial_fee: num(v, "initialFee"),
        final_fee: num(v, "finalFee"),
    }
}

/// The SDK's own initial `Core` state for an installation: price at the token-only bound, active
/// liquidity only while the tick is inside the position.
fn initial_state(range: &ZeroSeedLaunchRange, liquidity: u128) -> ZeroSeedLaunchPoolState {
    let tick = range.initial_tick();
    let (lower, upper) = range.pool_bounds();
    ZeroSeedLaunchPoolState {
        sqrt_ratio: to_sqrt_ratio::<Evm>(tick).unwrap(),
        tick,
        liquidity: if tick >= lower && tick < upper {
            liquidity
        } else {
            0
        },
    }
}

// ---------------------------------------------------------------------------------------------
// Indexer LOCAL receipt: the two supported instances, decoded from the emitted logs.
// ---------------------------------------------------------------------------------------------

fn indexer() -> Value {
    serde_json::from_str(INDEXER).unwrap()
}

/// The supported instance observation exactly as the indexer receipt records it.
fn fixture_instance(fixture: &Value, label: &str) -> ZeroSeedLaunchInstance {
    let entry = fixture["instances"]
        .as_array()
        .unwrap()
        .iter()
        .find(|i| s(i, "label") == label)
        .unwrap();
    let quote = address(s(entry, "quote"));
    ZeroSeedLaunchInstance {
        chain_id: fixture["chainId"].as_u64().unwrap(),
        extension: address(s(entry, "extension")),
        extension_runtime: U256::from_str(s(entry, "extensionRuntimeKeccak")).unwrap(),
        periphery: address(s(entry, "periphery")),
        periphery_runtime: U256::from_str(s(entry, "peripheryRuntimeKeccak")).unwrap(),
        core: address(s(&fixture["addresses"], "core")),
        core_runtime: U256::from_str(s(&fixture["provenance"], "coreRuntimeKeccak")).unwrap(),
        constructor_quote: quote,
        quote_token_getter: quote,
        quote_kind: match s(entry, "quoteKind") {
            "native" => {
                assert!(entry["quoteRuntimeKeccak"].is_null());
                ZeroSeedLaunchQuoteKind::Native
            }
            "erc20" => ZeroSeedLaunchQuoteKind::Erc20 {
                quote_runtime: U256::from_str(s(entry, "quoteRuntimeKeccak")).unwrap(),
            },
            other => panic!("quote kind {other}"),
        },
    }
}

fn data_bytes(log: &Value) -> Vec<u8> {
    hex::decode(&s(log, "data")[2..]).unwrap()
}

fn word(data: &[u8], i: usize) -> U256 {
    U256::from_be_slice(&data[i * 32..(i + 1) * 32])
}

fn word_address(data: &[u8], i: usize) -> Address {
    Address::from_slice(&data[i * 32 + 12..(i + 1) * 32])
}

fn word_i32(data: &[u8], i: usize) -> i32 {
    i32::from_be_bytes(data[i * 32 + 28..(i + 1) * 32].try_into().unwrap())
}

fn word_i128(data: &[u8], i: usize) -> i128 {
    i128::from_be_bytes(data[i * 32 + 16..(i + 1) * 32].try_into().unwrap())
}

fn word_u128(data: &[u8], i: usize) -> u128 {
    word(data, i).to::<u128>()
}

fn topic_address(log: &Value, i: usize) -> Address {
    Address::from_slice(&hex::decode(&log["topics"][i].as_str().unwrap()[2..]).unwrap()[12..])
}

fn abi_string(data: &[u8], base: usize, offset_word: usize) -> String {
    let start = base * 32 + word(data, offset_word).to::<usize>();
    let len = U256::from_be_slice(&data[start..start + 32]).to::<usize>();
    String::from_utf8(data[start + 32..start + 32 + len].to_vec()).unwrap()
}

/// A pool key from the `(token0, token1, bytes32 config)` encoding of `Core`.
fn pool_key(token0: Address, token1: Address, config: &[u8]) -> EvmZeroSeedLaunchPoolKey {
    let type_config = u32::from_be_bytes(config[28..32].try_into().unwrap());
    assert_eq!(type_config >> 31, 1, "concentrated pool config");
    EvmZeroSeedLaunchPoolKey {
        token0,
        token1,
        config: PoolConfig {
            extension: Address::from_slice(&config[..20]),
            fee: u64::from_be_bytes(config[20..28].try_into().unwrap()),
            pool_type_config: TickSpacing(type_config & 0x7fff_ffff),
        },
    }
}

/// `Core.poolState` word: 96-bit float sqrt ratio, int32 tick, uint128 liquidity.
fn indexer_state(word: &str) -> ZeroSeedLaunchPoolState {
    let word = U256::from_str(word).unwrap();
    let float: U256 = word >> 160usize;
    let mantissa_mask = (U256::from(1) << 94) - U256::from(1);
    let exponent: u8 = (float >> 94usize).try_into().unwrap();
    let tick_bits: u32 = ((word >> 128usize) & U256::from(u32::MAX))
        .try_into()
        .unwrap();
    ZeroSeedLaunchPoolState {
        sqrt_ratio: (float & mantissa_mask) << (2 + 32 * exponent),
        tick: tick_bits as i32,
        liquidity: (word & U256::from(u128::MAX)).try_into().unwrap(),
    }
}

/// A launch as decoded from its emitted `LaunchCreated` log.
struct IndexedLaunch {
    label: String,
    instance: ZeroSeedLaunchInstance,
    key: EvmZeroSeedLaunchPoolKey,
    config: ZeroSeedLaunchConfig,
    token: Address,
    created_state: ZeroSeedLaunchPoolState,
}

fn indexed_launches(fixture: &Value) -> HashMap<String, IndexedLaunch> {
    let mut launches = HashMap::new();
    for branch in fixture["branches"].as_object().unwrap().values() {
        for (index, log) in branch["logs"].as_array().unwrap().iter().enumerate() {
            if log["topics"][0].as_str() != Some(LAUNCH_CREATED) {
                continue;
            }
            let data = data_bytes(log);
            let pool_id = log["topics"][1].as_str().unwrap();
            let (label, recorded) = fixture["launches"]
                .as_object()
                .unwrap()
                .iter()
                .find(|(_, l)| s(l, "poolId") == pool_id)
                .unwrap();
            let installation = &fixture["installations"][label];
            let instance = fixture_instance(fixture, s(recorded, "instance"));
            instance.validate().unwrap();
            assert_eq!(address(s(log, "address")), instance.extension);
            assert_eq!(address(s(recorded, "extension")), instance.extension);
            assert_eq!(address(s(recorded, "periphery")), instance.periphery);
            assert_eq!(address(s(recorded, "quote")), instance.quote());

            // Head: PoolKey (3 words), PositionId, liquidity, offset of LaunchParameters.
            let key = pool_key(
                word_address(&data, 0),
                word_address(&data, 1),
                &data[64..96],
            );
            assert_eq!(key.token0, address(s(&recorded["poolKey"], "token0")));
            assert_eq!(key.token1, address(s(&recorded["poolKey"], "token1")));
            assert_eq!(&data[64..96], &b256(s(&recorded["poolKey"], "config"))[..]);
            assert_eq!(key.config.extension, instance.extension);
            assert_eq!(
                keccak256(&data[..96]),
                b256(pool_id),
                "poolId = keccak(abi.encode(poolKey))"
            );
            let p = word(&data, 5).to::<usize>() / 32;
            let (name, symbol) = (abi_string(&data, p, p), abi_string(&data, p, p + 1));
            let decimals = word(&data, p + 2).to::<u8>();
            let extension_salt = B256::from(word(&data, p + 12).to_be_bytes::<32>());

            // Token: the indexed topic, the receipt, the preview and the SDK prediction agree.
            let token = topic_address(log, 2);
            let controller = topic_address(log, 3);
            assert_eq!(
                controller, instance.periphery,
                "the periphery is the controller"
            );
            let owner = address(s(installation, "owner"));
            let user_salt = b256(s(installation, "userSalt"));
            assert_eq!(token, address(s(recorded, "token")));
            assert_eq!(token, address(s(installation, "predictedToken")));
            assert_eq!(b256(s(recorded, "userSalt")), user_salt);
            assert_eq!(periphery_launch_salt(owner, user_salt), extension_salt);
            assert_eq!(b256(s(installation, "extensionSalt")), extension_salt);
            assert_eq!(
                periphery_launch_token_address(
                    instance.extension,
                    instance.periphery,
                    owner,
                    user_salt,
                    &name,
                    &symbol,
                    decimals
                ),
                token,
                "{label} CREATE2 prediction"
            );
            assert_eq!(
                launch_token_address(
                    instance.extension,
                    controller,
                    extension_salt,
                    &name,
                    &symbol,
                    decimals
                ),
                token
            );
            assert_ne!(
                periphery_launch_token_address(
                    instance.extension,
                    instance.periphery,
                    instance.periphery,
                    user_salt,
                    &name,
                    &symbol,
                    decimals
                ),
                token,
                "another owner is another namespace"
            );

            // The initial owner of record follows in the same transaction.
            let owner_log = branch["logs"].as_array().unwrap()[index + 1..]
                .iter()
                .find(|l| l["topics"][0].as_str() == Some(LAUNCH_OWNER_CHANGED))
                .unwrap();
            assert_eq!(owner_log["transactionHash"], log["transactionHash"]);
            assert_eq!(address(s(owner_log, "address")), instance.periphery);
            assert_eq!(owner_log["topics"][1].as_str(), Some(pool_id));
            assert_eq!(topic_address(owner_log, 2), Address::ZERO);
            assert_eq!(topic_address(owner_log, 3), owner);

            let is1 = token == key.token1;
            assert_eq!(
                is1,
                instance.quote_kind == ZeroSeedLaunchQuoteKind::Native,
                "native launches are token1, WETH launches token0"
            );
            let range = ZeroSeedLaunchRange {
                launch_token_is_token1: is1,
                ask_tick: word_i32(&data, p + 5),
                upper_tick: word_i32(&data, p + 6),
                tick_spacing: word(&data, p + 7).to::<u32>(),
            };
            let position = word(&data, 3).to_be_bytes::<32>();
            let (lower, upper) = range.pool_bounds();
            assert_eq!(
                (
                    i32::from_be_bytes(position[24..28].try_into().unwrap()),
                    i32::from_be_bytes(position[28..32].try_into().unwrap())
                ),
                (lower, upper)
            );
            let config = ZeroSeedLaunchConfig {
                range,
                liquidity: word_u128(&data, 4),
                fee: ZeroSeedLaunchFeeSchedule {
                    trading_start: word(&data, p + 8).to::<u64>(),
                    fee_duration: word(&data, p + 9).to::<u32>(),
                    initial_fee: word(&data, p + 10).to::<u64>(),
                    final_fee: word(&data, p + 11).to::<u64>(),
                },
            };
            assert_eq!(word_u128(&data, p + 4), config.liquidity);
            assert_eq!(
                word_u128(&data, p + 3),
                num::<u128>(installation, "actualInstalledSupply")
            );
            assert_eq!(
                config.liquidity,
                num::<u128>(installation, "actualLiquidity")
            );
            assert_eq!(
                config.fee.trading_start,
                num::<u64>(installation, "tradingStart")
            );
            // The installed pair is exactly the one previewed for the requested supply.
            let parameters = ZeroSeedLaunchParameters {
                supply: num(installation, "requestedSupply"),
                range,
                fee: config.fee,
            };
            let preview = preview_installation_math(&parameters, 0).unwrap();
            assert_eq!(preview.liquidity, config.liquidity);
            assert_eq!(preview.installed_supply, word_u128(&data, p + 3));

            let created_state = initial_state(&range, config.liquidity);
            let previous = launches.insert(
                label.clone(),
                IndexedLaunch {
                    label: label.clone(),
                    instance,
                    key,
                    config,
                    token,
                    created_state,
                },
            );
            assert!(previous.is_none());
        }
    }
    assert_eq!(launches.len(), 4);
    launches
}

#[test]
fn indexer_launches_decode_bind_and_predict() {
    let fixture = indexer();
    let launches = indexed_launches(&fixture);
    for launch in launches.values() {
        let pool = EvmZeroSeedLaunchPool::new(
            launch.key,
            launch.config,
            launch.created_state,
            &launch.instance,
        )
        .unwrap();
        assert_eq!(pool.state(), launch.created_state);
        // The other instance is not an alias for this launch.
        let other = fixture_instance(
            &fixture,
            if launch.instance.quote_kind == ZeroSeedLaunchQuoteKind::Native {
                "weth"
            } else {
                "native"
            },
        );
        other.validate().unwrap();
        assert_eq!(
            EvmZeroSeedLaunchPool::new(launch.key, launch.config, launch.created_state, &other),
            Err(ZeroSeedLaunchPoolConstructionError::UnsupportedQuoteToken)
        );
        assert_ne!(launch.token, Address::ZERO, "{}", launch.label);
    }
}

#[derive(Clone, Default)]
struct Ledger {
    state: Option<ZeroSeedLaunchPoolState>,
    accrued: [u128; 2],
    claimed: [u128; 2],
    paid: [u128; 2],
    owner: Address,
}

/// Replays every block of the receipt: SDK quotes against the `LaunchSwapped` and `Core` swap
/// logs, the fee ledger (accrued from `LaunchSwapped`, claimed from the extension's
/// `CreatorFeesClaimed` only, with the periphery payout as a separate record of the same claim),
/// owners from `LaunchOwnerChanged`, and every recorded snapshot: `Core` state, `creatorFees`,
/// `feeAt(block time)`, owner and controller.
#[test]
fn indexer_trades_ledgers_owners_and_fees_replay() {
    let fixture = indexer();
    let launches = indexed_launches(&fixture);
    let mut prefix = HashMap::new();
    let (mut swaps_checked, mut claims_checked, mut snapshots_checked) = (0, 0, 0);
    for branch_name in ["prefix", "alternate", "canonical"] {
        let branch = &fixture["branches"][branch_name];
        let mut ledgers: HashMap<String, Ledger> = prefix.clone();
        for block in branch["blocks"].as_array().unwrap() {
            let number = block["number"].as_u64().unwrap();
            let timestamp = block["timestamp"].as_u64().unwrap();
            let logs: Vec<_> = branch["logs"]
                .as_array()
                .unwrap()
                .iter()
                .filter(|l| hex_u64(l, "blockNumber") == number)
                .collect();
            let by_topic = |topic: &str| -> Vec<&Value> {
                logs.iter()
                    .filter(|l| l["topics"][0].as_str() == Some(topic))
                    .copied()
                    .collect()
            };
            let mut swaps = by_topic(LAUNCH_SWAPPED).into_iter();
            let mut claims = by_topic(CREATOR_FEES_CLAIMED).into_iter();
            let mut payouts = by_topic(LAUNCH_FEES_CLAIMED).into_iter();
            let mut owner_changes = by_topic(LAUNCH_OWNER_CHANGED).into_iter();
            for action in block["actions"].as_array().unwrap() {
                let action: Vec<_> = action.as_str().unwrap().split_whitespace().collect();
                match action[0] {
                    "create" => {
                        let launch = &launches[action[1]];
                        let event = owner_changes.next().unwrap();
                        assert_eq!(topic_address(event, 2), Address::ZERO);
                        ledgers.insert(
                            action[1].to_owned(),
                            Ledger {
                                state: Some(launch.created_state),
                                owner: topic_address(event, 3),
                                ..Ledger::default()
                            },
                        );
                    }
                    "transfer" => {
                        let ledger = ledgers.get_mut(action[1]).unwrap();
                        let event = owner_changes.next().unwrap();
                        assert_eq!(
                            address(s(event, "address")),
                            launches[action[1]].instance.periphery
                        );
                        assert_eq!(topic_address(event, 2), ledger.owner);
                        assert_eq!(topic_address(event, 2), address(action[2]));
                        assert_eq!(topic_address(event, 3), address(action[4]));
                        ledger.owner = topic_address(event, 3);
                    }
                    "claim" => {
                        let launch = &launches[action[1]];
                        let ledger = ledgers.get_mut(action[1]).unwrap();
                        assert_eq!(address(action[3]), ledger.owner, "only the owner claims");
                        let event = claims.next().unwrap();
                        assert_eq!(address(s(event, "address")), launch.instance.extension);
                        assert_eq!(topic_address(event, 2), launch.instance.periphery);
                        let data = data_bytes(event);
                        let amounts = [word_u128(&data, 0), word_u128(&data, 1)];
                        for (side, amount) in amounts.into_iter().enumerate() {
                            assert_eq!(
                                amount,
                                ledger.accrued[side] - ledger.claimed[side],
                                "{branch_name} {number}: the claim takes the whole ledger"
                            );
                            ledger.claimed[side] += amount;
                        }
                        let payout = payouts.next().unwrap();
                        assert_eq!(payout["transactionHash"], event["transactionHash"]);
                        assert_eq!(address(s(payout, "address")), launch.instance.periphery);
                        assert_eq!(topic_address(payout, 2), ledger.owner);
                        assert_eq!(topic_address(payout, 3), address(action[5]));
                        let paid = data_bytes(payout);
                        for (side, amount) in amounts.into_iter().enumerate() {
                            assert_eq!(word_u128(&paid, side), amount);
                            ledger.paid[side] += amount;
                        }
                        claims_checked += 1;
                    }
                    "buy" | "sell" => {
                        let launch = &launches[action[1]];
                        let ledger = ledgers.get_mut(action[1]).unwrap();
                        let before = ledger.state.unwrap();
                        let pool = EvmZeroSeedLaunchPool::new(
                            launch.key,
                            launch.config,
                            before,
                            &launch.instance,
                        )
                        .unwrap();
                        let quote_token = launch.instance.quote();
                        let token = match (action[0], action[2]) {
                            ("buy", "exact-in") | ("sell", "exact-out") => quote_token,
                            _ => launch.token,
                        };
                        let amount: i128 = action[3].parse().unwrap();
                        let q = pool
                            .quote(QuoteParams {
                                token_amount: TokenAmount { token, amount },
                                sqrt_ratio_limit: None,
                                override_state: None,
                                meta: timestamp,
                            })
                            .unwrap();
                        let event = swaps.next().unwrap();
                        assert_eq!(address(s(event, "address")), launch.instance.extension);
                        let core_log = logs.iter().find(|l| {
                            l["transactionHash"] == event["transactionHash"]
                                && l["topics"].as_array().unwrap().is_empty()
                                && s(l, "data").len() == 234
                        });
                        let recorded = if let Some(core_log) = core_log {
                            let data = &s(core_log, "data")[2..];
                            assert_eq!(
                                format!("0x{}", &data[40..104]),
                                s(&fixture["launches"][action[1]], "poolId")
                            );
                            indexer_state(&format!("0x{}", &data[168..232]))
                        } else {
                            before
                        }; // A no-bid zero fill emits no Core swap, but does emit LaunchSwapped.
                        assert_eq!(q.state_after, recorded, "{branch_name} {number}");
                        let data = data_bytes(event);
                        let specified_is1 = token == pool.key().token1;
                        assert_eq!(
                            word_i128(&data, usize::from(specified_is1)),
                            q.consumed_amount
                        );
                        let calculated = word_i128(&data, usize::from(!specified_is1));
                        assert_eq!(calculated.unsigned_abs(), q.calculated_amount);
                        assert_eq!(word(&data, 2), U256::from(pool.fee_at(timestamp)));
                        assert_eq!(word_u128(&data, 3), q.fees_paid);
                        assert_eq!(word(&data, 4), U256::from(u8::from(!specified_is1)));
                        ledger.accrued[usize::from(!specified_is1)] += q.fees_paid;
                        ledger.state = Some(q.state_after);
                        swaps_checked += 1;
                    }
                    _ => {}
                }
            }
            assert!(swaps.next().is_none() && claims.next().is_none());
            assert!(payouts.next().is_none() && owner_changes.next().is_none());

            let snapshot = branch["states"]
                .as_array()
                .unwrap()
                .iter()
                .find(|st| st["blockNumber"].as_u64() == Some(number))
                .unwrap();
            for observed in snapshot["pools"].as_array().unwrap() {
                let label = s(observed, "label");
                let launch = &launches[label];
                let ledger = &ledgers[label];
                assert_eq!(
                    indexer_state(s(observed, "poolStateWord")),
                    ledger.state.unwrap(),
                    "{branch_name} {number} {label} state"
                );
                let fees = &observed["creatorFees"];
                for side in 0..2 {
                    assert_eq!(
                        fees[side].as_str().unwrap().parse::<u128>().unwrap(),
                        ledger.accrued[side] - ledger.claimed[side],
                        "{branch_name} {number} {label} ledger"
                    );
                    assert_eq!(ledger.paid[side], ledger.claimed[side], "no double count");
                }
                assert_eq!(address(s(observed, "launchOwner")), ledger.owner);
                assert_eq!(
                    address(s(observed, "controller")),
                    launch.instance.periphery
                );
                assert_eq!(
                    launch.config.fee.fee_at(timestamp),
                    num::<u64>(observed, "feeAtBlockTime"),
                    "{branch_name} {number} {label} feeAt"
                );
                snapshots_checked += 1;
            }
            assert_eq!(snapshot["pools"].as_array().unwrap().len(), ledgers.len());
        }
        if branch_name == "prefix" {
            prefix = ledgers;
        }
    }
    assert_eq!(
        (swaps_checked, claims_checked, snapshots_checked),
        (19, 8, 41)
    );
}

// ---------------------------------------------------------------------------------------------
// Foundry parity vectors.
// ---------------------------------------------------------------------------------------------

/// The parity instance observation: its runtimes are executed code of the target, but its
/// extension and periphery addresses are the test harness's, not a supported pin.
fn parity_instance(created: &Value) -> ZeroSeedLaunchInstance {
    let quote = address(s(created, "constructorQuote"));
    ZeroSeedLaunchInstance {
        chain_id: 31337,
        extension: address(s(created, "extension")),
        extension_runtime: U256::from_str(s(created, "extensionCodehash")).unwrap(),
        periphery: address(s(created, "periphery")),
        periphery_runtime: U256::from_str(s(created, "peripheryCodehash")).unwrap(),
        core: address("0x00000000000014aa86c5d3c41765bb24e11bd701"),
        core_runtime: U256::from_str(s(created, "coreCodehash")).unwrap(),
        constructor_quote: quote,
        quote_token_getter: quote,
        quote_kind: if s(created, "quoteKind") == "native" {
            ZeroSeedLaunchQuoteKind::Native
        } else {
            ZeroSeedLaunchQuoteKind::Erc20 {
                quote_runtime: U256::from_str(s(created, "quoteCodehash")).unwrap(),
            }
        },
    }
}

fn pool_inputs_from_created(created: &Value) -> (EvmZeroSeedLaunchPoolKey, ZeroSeedLaunchConfig) {
    let token0 = address(s(created, "token0"));
    let token1 = address(s(created, "token1"));
    let token = address(s(created, "token"));
    let tick_spacing: u32 = num(created, "tickSpacing");
    let key = EvmZeroSeedLaunchPoolKey {
        token0,
        token1,
        config: PoolConfig {
            extension: address(s(created, "extension")),
            fee: num(created, "fee"),
            pool_type_config: TickSpacing(tick_spacing),
        },
    };
    let config = ZeroSeedLaunchConfig {
        range: ZeroSeedLaunchRange {
            launch_token_is_token1: token == token1,
            ask_tick: num(created, "askTick"),
            upper_tick: num(created, "upperTick"),
            tick_spacing,
        },
        liquidity: num(created, "liquidity"),
        fee: fee_schedule(created),
    };
    assert_eq!(
        config.range.pool_bounds(),
        (num(created, "tickLower"), num(created, "tickUpper"))
    );
    (key, config)
}

/// Builds the pool from `LaunchCreated` fields only. The harness instance is refused by the
/// supported constructor, so the arithmetic constructor is used.
fn pool_from_created(created: &Value, state: ZeroSeedLaunchPoolState) -> EvmZeroSeedLaunchPool {
    let (key, config) = pool_inputs_from_created(created);
    assert_eq!(
        parity_instance(created).validate(),
        Err(ZeroSeedLaunchParameterError::UnsupportedInstance)
    );
    assert!(EvmZeroSeedLaunchPool::new(key, config, state, &parity_instance(created)).is_err());
    EvmZeroSeedLaunchPool::new_math(key, config, state).unwrap()
}

fn optional_limit(step: &Value) -> Option<U256> {
    let limit = U256::from_str(s(step, "limit")).unwrap();
    (!limit.is_zero()).then_some(limit)
}

fn pair(v: &Value, field: &str) -> [u128; 2] {
    let mut parts = s(v, field).split(',').map(|x| x.parse().unwrap());
    [parts.next().unwrap(), parts.next().unwrap()]
}

#[derive(Default)]
struct GasSample {
    measured: u64,
    estimate: u64,
    ticks_crossed: u32,
    extra_lookups: u32,
}

#[test]
fn parity_with_local_core_state_and_events() {
    let vectors: Value = serde_json::from_str(PARITY).unwrap();
    let pins: Value = serde_json::from_str(PINS).unwrap();
    let scenarios = vectors["scenarios"].as_array().unwrap();
    assert_eq!(scenarios.len(), 11);
    let mut compared = 0;
    let mut refused = 0;
    let mut claims = 0;
    let mut native = 0;
    let mut gas = Vec::new();

    for scenario in scenarios {
        let name = s(scenario, "name");
        let created = &scenario["create"];
        assert_eq!(
            s(created, "coreCodehash"),
            "0xc5f90c9d0dbc5037f8f9e248f4bb292e7c1824f584eb6550cb4cad525b38c71a"
        );
        // The harness runs the pinned extension code (same constructor arguments, runtime
        // independent of its address) at an unpinned address.
        let fixture =
            &pins["localFixtures"][s(created, "quoteKind").replace("erc20", "weth").as_str()];
        if s(created, "quoteDecimals") == "18" {
            assert_eq!(
                s(created, "extensionCodehash"),
                s(fixture, "extensionRuntimeKeccak")
            );
            assert_ne!(
                address(s(created, "extension")),
                address(s(fixture, "extension"))
            );
        }
        let core_state = state(&created["state"]);
        let pool = pool_from_created(created, core_state);
        // The SDK's installation state equals what Core holds after create.
        assert_eq!(
            initial_state(&pool.launch().range, pool.launch().liquidity),
            core_state,
            "{name} initial state"
        );
        let launch_is1 = pool.launch().range.launch_token_is_token1;
        if s(created, "quoteKind") == "native" {
            assert_eq!(pool.key().token0, Address::ZERO, "{name}");
            assert!(launch_is1, "{name}: native quote is token0");
            native += 1;
        }
        // The token address is the periphery-namespaced CREATE2 prediction.
        let periphery = address(s(created, "periphery"));
        assert_eq!(address(s(created, "controller")), periphery);
        let extension_salt = b256(s(created, "extensionSalt"));
        assert_eq!(
            periphery_launch_salt(address(s(created, "owner")), b256(s(created, "userSalt"))),
            extension_salt
        );
        assert_eq!(
            launch_token_address(
                pool.key().config.extension,
                periphery,
                extension_salt,
                s(created, "name"),
                s(created, "symbol"),
                num(created, "decimals"),
            ),
            address(s(created, "token")),
            "{name} token prediction"
        );

        let mut current = pool.state();
        let mut fees = [0u128; 2];
        let mut first_fill = true;
        for step in scenario["steps"].as_array().unwrap() {
            let label = format!("{name} #{} {}", num::<u32>(step, "i"), s(step, "label"));
            if s(step, "label") == "sellClaimedExactIn" {
                // The owner's claim through the periphery withdraws exactly the fees the SDK
                // charged, once, and leaves the pool alone.
                let claim = &scenario["claim"];
                assert_eq!(
                    [num::<u128>(claim, "amount0"), num::<u128>(claim, "amount1")],
                    fees,
                    "{name} claimed ledger"
                );
                assert_eq!(
                    pair(claim, "extensionEvent"),
                    fees,
                    "{name} CreatorFeesClaimed"
                );
                assert_eq!(
                    pair(claim, "peripheryEvent"),
                    fees,
                    "{name} LaunchFeesClaimed"
                );
                assert_eq!(pair(claim, "returned"), fees, "{name} claimFees return");
                assert_eq!(pair(claim, "ledgerAfter"), [0, 0], "{name} ledger emptied");
                assert_eq!(
                    state(&claim["post"]),
                    current,
                    "{name} claim moved the pool"
                );
                fees = [0, 0];
                claims += 1;
            }
            assert_eq!(state(&step["pre"]), current, "{label}: chained pre state");
            let ts: u64 = num(step, "ts");
            let amount: i128 = num(step, "amount");
            let is_token1 = step["specified_is_token1"].as_bool().unwrap();
            let result = pool.simulate_swap(current, amount, is_token1, optional_limit(step), ts);

            if !step["ok"].as_bool().unwrap() {
                assert_eq!(
                    step["pre_balances"], step["post_balances"],
                    "{label}: rollback conservation"
                );
                let error = s(step, "error");
                assert_eq!(
                    state(&step["post"]),
                    current,
                    "{label}: reverted swap moved"
                );
                match error {
                    TRADING_NOT_STARTED => assert_eq!(
                        result,
                        Err(ZeroSeedLaunchPoolQuoteError::TradingNotStarted),
                        "{label}"
                    ),
                    SQRT_RATIO_LIMIT_WRONG_DIRECTION => assert_eq!(
                        result,
                        Err(ZeroSeedLaunchPoolQuoteError::SqrtRatioLimitWrongDirection),
                        "{label}"
                    ),
                    SAFE_CAST_OVERFLOW => assert_eq!(
                        result,
                        Err(ZeroSeedLaunchPoolQuoteError::Overflow),
                        "{label}"
                    ),
                    TRANSFER_FROM_FAILED => {
                        // Settlement, not pool math: the test account cannot pay what the swap
                        // needs.
                        let swap = result.unwrap();
                        let (token_owed, quote_owed) = if launch_is1 {
                            (swap.delta1, swap.delta0)
                        } else {
                            (swap.delta0, swap.delta1)
                        };
                        let held_token: u128 = num(step, "held_token");
                        let token_allowance = U256::from_str(s(step, "token_allowance")).unwrap();
                        let held_quote = U256::from_str(s(step, "held_quote")).unwrap();
                        let core_quote = U256::from_str(s(step, "core_quote")).unwrap();
                        assert!(
                            (token_owed > 0 && token_owed as u128 > held_token)
                                || (token_owed > 0
                                    && U256::from(token_owed as u128) > token_allowance)
                                || (quote_owed > 0 && U256::from(quote_owed as u128) > held_quote)
                                || (quote_owed < 0
                                    && U256::from(quote_owed.unsigned_abs()) > core_quote),
                            "{label}: owes {token_owed}/{quote_owed}, holds {held_token}/{held_quote}"
                        );
                    }
                    other => panic!("{label}: unexpected revert {other}"),
                }
                refused += 1;
                continue;
            }

            let swap = result.unwrap_or_else(|e| panic!("{label}: {e}"));
            for (i, delta) in [swap.delta0, swap.delta1].into_iter().enumerate() {
                let pre =
                    |k: usize| U256::from_str(step["pre_balances"][k].as_str().unwrap()).unwrap();
                let post =
                    |k: usize| U256::from_str(step["post_balances"][k].as_str().unwrap()).unwrap();
                let amount = U256::from(delta.unsigned_abs());
                let expected_core = if delta >= 0 {
                    pre(i).checked_add(amount)
                } else {
                    pre(i).checked_sub(amount)
                }
                .unwrap();
                let expected_holder = if delta >= 0 {
                    pre(i + 2).checked_sub(amount)
                } else {
                    pre(i + 2).checked_add(amount)
                }
                .unwrap();
                assert_eq!(post(i), expected_core, "{label}: Core balance delta");
                assert_eq!(
                    post(i + 2),
                    expected_holder,
                    "{label}: holder balance delta"
                );
                assert_eq!(
                    pre(i).checked_add(pre(i + 2)),
                    post(i).checked_add(post(i + 2)),
                    "{label}: asset conservation"
                );
            }
            let event = &step["event"];
            assert_eq!(swap.delta0, num::<i128>(step, "delta0"), "{label} delta0");
            assert_eq!(swap.delta1, num::<i128>(step, "delta1"), "{label} delta1");
            assert_eq!(
                swap.delta0,
                num::<i128>(event, "delta0"),
                "{label} event delta0"
            );
            assert_eq!(
                swap.delta1,
                num::<i128>(event, "delta1"),
                "{label} event delta1"
            );
            assert_eq!(swap.fee_rate, num::<u64>(event, "fee_rate"), "{label} rate");
            assert_eq!(swap.fee_rate, num::<u64>(step, "fee_at"), "{label} feeAt");
            assert_eq!(
                swap.fee_amount,
                num::<u128>(event, "fee_amount"),
                "{label} fee"
            );
            assert_eq!(
                swap.fee_is_token1,
                event["fee_is_token1"].as_bool().unwrap(),
                "{label} fee side"
            );
            let ledger = [
                num::<u128>(step, "ledger_delta0"),
                num::<u128>(step, "ledger_delta1"),
            ];
            let side = usize::from(swap.fee_is_token1);
            assert_eq!(ledger[side], swap.fee_amount, "{label} ledger");
            assert_eq!(ledger[1 - side], 0, "{label} other ledger");
            fees[side] += swap.fee_amount;
            assert_eq!(swap.state_after, state(&step["post"]), "{label} post state");

            // The Pool interface reports the same fill.
            let specified_token = if is_token1 {
                pool.key().token1
            } else {
                pool.key().token0
            };
            let quote = pool
                .quote(QuoteParams {
                    token_amount: TokenAmount {
                        token: specified_token,
                        amount,
                    },
                    sqrt_ratio_limit: optional_limit(step),
                    override_state: Some(current),
                    meta: ts,
                })
                .unwrap();
            let (specified, calculated) = if is_token1 {
                (swap.delta1, swap.delta0)
            } else {
                (swap.delta0, swap.delta1)
            };
            assert_eq!(quote.consumed_amount, specified, "{label} consumed");
            assert_eq!(
                quote.calculated_amount,
                calculated.unsigned_abs(),
                "{label} calc"
            );
            assert_eq!(quote.fees_paid, swap.fee_amount);
            assert_eq!(quote.state_after, swap.state_after);

            if swap.delta0 != 0 || swap.delta1 != 0 {
                let r = swap.resources;
                let sample = GasSample {
                    measured: num(step, "gas"),
                    estimate: r.uncalibrated_gas_estimate(),
                    ticks_crossed: r.concentrated.initialized_ticks_crossed,
                    extra_lookups: r.concentrated.extra_distinct_bitmap_lookups,
                };
                if !first_fill {
                    gas.push((label.clone(), sample));
                }
                first_fill = false;
            }
            current = swap.state_after;
            compared += 1;
        }
    }
    assert_eq!(native, 3);
    assert_eq!(claims, 10);
    assert_eq!(compared + refused, 507);
    assert!(compared >= 300, "compared {compared}");

    // Gas: the uncalibrated estimate stays within 40% of the measured in-test gas for every fill
    // except the first of each launch and the two that write a zero storage slot (the first fee
    // after the claim, the first tokens bought after the holder sold out), which it
    // underestimates. Set ZERO_SEED_GAS_TABLE to print the table.
    let mut worst = 0f64;
    let mut cold = 0;
    for (label, g) in &gas {
        let error = (g.estimate as f64 - g.measured as f64) / g.measured as f64;
        if std::env::var_os("ZERO_SEED_GAS_TABLE").is_some() {
            println!(
                "{label}\tmeasured={}\testimate={}\tticks={}\tlookups={}\terr={:+.3}",
                g.measured, g.estimate, g.ticks_crossed, g.extra_lookups, error
            );
        }
        if label.ends_with("sellClaimedExactIn") || label.ends_with("farFutureBuy") {
            assert!(
                g.estimate < g.measured && g.measured - g.estimate < 30_000,
                "{label}"
            );
            cold += 1;
            continue;
        }
        worst = worst.max(error.abs());
    }
    assert_eq!(cold, 20);
    println!("parity: {compared} executed, {refused} refused, {claims} claims; gas worst={worst}");
    assert!(worst < 0.40, "worst gas estimate error {worst}");
}

fn parameters_of(preview: &Value) -> ZeroSeedLaunchParameters {
    let label = s(preview, "label");
    ZeroSeedLaunchParameters {
        supply: num(preview, "supply"),
        range: ZeroSeedLaunchRange {
            launch_token_is_token1: label.starts_with("t1"),
            ask_tick: num(preview, "askTick"),
            upper_tick: num(preview, "upperTick"),
            tick_spacing: num(preview, "tickSpacing"),
        },
        fee: fee_schedule(preview),
    }
}

/// Decodes a contract revert into the SDK error it corresponds to.
fn decode_error(data: &str) -> ZeroSeedLaunchParameterError {
    let word = |i: usize| -> u128 {
        let start = 10 + 64 * i;
        u128::from_str_radix(&data[start + 32..start + 64], 16).unwrap()
    };
    match &data[..10] {
        "0xe5239090" => ZeroSeedLaunchParameterError::InvalidParameters,
        "0xcd4e6167" => ZeroSeedLaunchParameterError::FeeTooHigh,
        "0xf75a271a" => ZeroSeedLaunchParameterError::InvalidFeeSchedule,
        "0xe0839259" => ZeroSeedLaunchParameterError::InvalidTradingStart,
        "0x89fd41b1" => ZeroSeedLaunchParameterError::BoundsTickSpacing,
        "0x10074548" => ZeroSeedLaunchParameterError::ZeroLiquidity,
        // solady SafeCastLib `Overflow()`
        "0x35278d12" => ZeroSeedLaunchParameterError::Overflow,
        "0x20ea795f" => ZeroSeedLaunchParameterError::LiquidityAboveTickCap {
            liquidity: word(0),
            cap: word(1),
        },
        "0xad00b597" => ZeroSeedLaunchParameterError::SupplyNotExactlyInstallable {
            requested: word(0),
            installable: word(1),
        },
        other => panic!("unknown revert {other}"),
    }
}

#[test]
fn installation_preview_and_binding_match_the_contract() {
    let vectors: Value = serde_json::from_str(PARITY).unwrap();
    let mut by_label = HashMap::new();
    let mut ok = 0;
    let previews = vectors["previews"].as_array().unwrap();
    for preview in previews {
        let label = s(preview, "label");
        let parameters = parameters_of(preview);
        let now: u64 = num(preview, "now");
        let result = preview_installation_math(&parameters, now);
        if label.starts_with("t1_18_18") {
            assert_eq!(address(s(preview, "quote")), Address::ZERO, "native quote");
        }
        if preview["ok"].as_bool().unwrap() {
            let installation = result.unwrap_or_else(|e| panic!("{label}: {e}"));
            let token_is0 = s(preview, "token") == s(preview, "token0");
            assert_eq!(
                token_is0, !parameters.range.launch_token_is_token1,
                "{label}"
            );
            assert_eq!(
                installation.tick_lower,
                num::<i32>(preview, "tickLower"),
                "{label}"
            );
            assert_eq!(
                installation.tick_upper,
                num::<i32>(preview, "tickUpper"),
                "{label}"
            );
            assert_eq!(
                installation.initial_tick,
                num::<i32>(preview, "initialTick"),
                "{label}"
            );
            assert_eq!(
                installation.liquidity,
                num::<u128>(preview, "liquidity"),
                "{label}"
            );
            assert_eq!(
                installation.installed_supply,
                num::<u128>(preview, "installedSupply"),
                "{label}"
            );
            assert!(
                installation.installed_supply <= parameters.supply,
                "{label}"
            );
            ok += 1;
        } else {
            assert_eq!(result, Err(decode_error(s(preview, "err"))), "{label}");
        }
        by_label.insert(label.to_owned(), parameters);
    }
    assert_eq!(previews.len(), 108);
    assert_eq!(ok, 44);

    let bindings = vectors["bindings"].as_array().unwrap();
    assert_eq!(bindings.len(), 4 * ok);
    for binding in bindings {
        let label = s(binding, "label");
        let mut parameters = by_label[label];
        parameters.supply = num(binding, "supply");
        let liquidity: u128 = num(binding, "liquidity");
        // Creation happens in the block after the preview's timestamp in the generator, at the
        // same timestamp.
        let result = check_launch_binding_math(&parameters, liquidity, 1);
        if binding["ok"].as_bool().unwrap() {
            let installation = result.unwrap_or_else(|e| panic!("{label}: {e}"));
            assert_eq!(installation.installed_supply, parameters.supply);
            assert_eq!(installation.liquidity, liquidity);
        } else {
            assert_eq!(
                result,
                Err(decode_error(s(binding, "err"))),
                "{label} {liquidity}"
            );
        }
    }

    // The documented trap: previewing the installed supply again does not return the same pair.
    let frozen = &by_label["t0_18_6_frozen"];
    let first = preview_installation_math(frozen, 1).unwrap();
    let mut again = *frozen;
    again.supply = first.installed_supply;
    let second = preview_installation_math(&again, 1).unwrap();
    assert_eq!(second.liquidity, first.liquidity - 1);
    assert!(second.installed_supply < first.installed_supply);
}

#[test]
fn frozen_integer_vectors() {
    let vectors: Value = serde_json::from_str(FROZEN).unwrap();
    let fixture = &vectors["fixture"];
    let fee = |duration: u32| ZeroSeedLaunchFeeSchedule {
        trading_start: num(fixture, "trading_start"),
        fee_duration: duration,
        initial_fee: num(fixture, "fee_initial_q64"),
        final_fee: num(fixture, "fee_final_q64"),
    };
    let start: u64 = num(fixture, "trading_start");

    for entry in vectors["fee"].as_array().unwrap() {
        let duration: u32 = num(entry, "duration");
        let offset: i128 = num(entry, "t_minus_start");
        let t = u64::try_from(i128::from(start) + offset).unwrap();
        assert_eq!(
            fee(duration).fee_at(t),
            num::<u64>(entry, "fee_q64"),
            "{entry}"
        );
    }

    let mut pools = HashMap::new();
    for entry in vectors["create"].as_array().unwrap() {
        let is1 = s(entry, "order") == "t1";
        let decimals = s(entry, "dec");
        // t1 at 18 decimals is the native ETH quote, address(0).
        let quote = match (is1, decimals) {
            (false, _) => address(QUOTE_HIGH),
            (true, "18/18") => Address::ZERO,
            (true, _) => address(QUOTE_LOW),
        };
        let range = ZeroSeedLaunchRange {
            launch_token_is_token1: is1,
            ask_tick: num(entry, "ask"),
            upper_tick: num(entry, "upper"),
            tick_spacing: num(fixture, "tick_spacing"),
        };
        let parameters = ZeroSeedLaunchParameters {
            supply: num(entry, "requested"),
            range,
            fee: fee(3600),
        };
        let installation = preview_installation_math(&parameters, 1).unwrap();
        assert_eq!(
            installation.installed_supply,
            num::<u128>(entry, "installed")
        );
        assert_eq!(installation.liquidity, num::<u128>(entry, "liquidity"));
        assert_eq!(installation.tick_lower, num::<i32>(entry, "tickLower"));
        assert_eq!(installation.tick_upper, num::<i32>(entry, "tickUpper"));
        assert_eq!(installation.initial_tick, num::<i32>(entry, "initialTick"));

        // A launch token address on the right side of the fixture quote.
        let token = address(if is1 {
            "0x00000000000000000000000000000000000f0000"
        } else {
            "0x00000000000000000000000000000000000a0000"
        });
        let (token0, token1) = if is1 { (quote, token) } else { (token, quote) };
        let pool = EvmZeroSeedLaunchPool::new_math(
            PoolKey {
                token0,
                token1,
                config: PoolConfig {
                    extension: address("0x5100000000000000000000000000000000000000"),
                    fee: 0,
                    pool_type_config: TickSpacing(range.tick_spacing),
                },
            },
            ZeroSeedLaunchConfig {
                range,
                liquidity: installation.liquidity,
                fee: fee(3600),
            },
            initial_state(&range, installation.liquidity),
        )
        .unwrap();
        pools.insert(
            format!("{}|{decimals}", s(entry, "order")),
            (pool, token, quote),
        );
    }

    let quote_fill = |pool: &EvmZeroSeedLaunchPool,
                      state: ZeroSeedLaunchPoolState,
                      token: Address,
                      amount: i128| {
        pool.quote(QuoteParams {
            token_amount: TokenAmount { token, amount },
            sqrt_ratio_limit: None,
            override_state: Some(state),
            meta: start,
        })
        .unwrap()
    };

    let mut checked = 0;
    for entry in vectors["trade"].as_array().unwrap() {
        let key = format!("{}|{}", s(entry, "order"), s(entry, "decimals"));
        let (pool, token, quote) = &pools[&key];
        let state = pool.state();
        match s(entry, "step") {
            "buyExactIn" => {
                let q = quote_fill(pool, state, *quote, num(entry, "quoteIn"));
                assert_eq!(q.calculated_amount, num::<u128>(entry, "net"), "{entry}");
                assert_eq!(q.fees_paid, num::<u128>(entry, "fee"), "{entry}");
                assert_eq!(
                    q.calculated_amount + q.fees_paid,
                    num::<u128>(entry, "gross"),
                    "{entry}"
                );
                checked += 1;
            }
            "buyExactOut" => {
                // After the exact-input buy of one quote unit.
                let unit = 10i128.pow(if key.ends_with("18/6") { 6 } else { 18 });
                let first = quote_fill(pool, state, *quote, unit);
                let net: i128 = num(entry, "tokenOut");
                let q = quote_fill(pool, first.state_after, *token, -net);
                assert_eq!(q.consumed_amount, -net);
                assert_eq!(q.calculated_amount, num::<u128>(entry, "paid"), "{entry}");
                assert_eq!(q.fees_paid, num::<u128>(entry, "fee"), "{entry}");
                assert_eq!(
                    q.calculated_amount - q.fees_paid,
                    num::<u128>(entry, "calcQuote"),
                    "{entry}"
                );
                // Then sell half of the 2 * net held, exact input.
                let sell = vectors["trade"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .find(|e| {
                        s(e, "order") == s(entry, "order")
                            && s(e, "decimals") == s(entry, "decimals")
                            && s(e, "step") == "sellExactIn"
                    })
                    .unwrap();
                let held = 2 * net;
                assert_eq!(num::<i128>(sell, "tokenIn"), held / 2);
                let q = quote_fill(pool, q.state_after, *token, held / 2);
                assert_eq!(q.calculated_amount, num::<u128>(sell, "quoteOut"), "{sell}");
                checked += 2;
            }
            _ => {}
        }
    }
    assert_eq!(checked, 12);

    // Upper residue is not Core's accumulated unowned dust. Preserve per-asset raw units.
    let residues = vectors["residue_metrics"]["scenarios"].as_array().unwrap();
    assert_eq!(residues.len(), 4);
    for (entry, expected) in residues.iter().zip([89u128, 89, 94, 90]) {
        let residue: u128 = num(entry, "upper_residue_raw_token");
        assert_eq!(residue, expected);
        assert_eq!(
            num::<u128>(entry, "position_token_before_exhaust")
                - num::<u128>(entry, "delivered_raw_token"),
            residue
        );
        let before = &entry["core_dust_before_exhaust"];
        let after = &entry["core_dust_after_exhaust"];
        assert_eq!(
            num::<u128>(after, "raw_token"),
            num::<u128>(before, "raw_token") + residue
        );
        assert!(num::<u128>(after, "raw_quote") >= num::<u128>(before, "raw_quote"));
    }

    // The deployed router fixture's 1e18 quote buy (WETH and native) and the one-unit dust buy.
    for entry in vectors["router"].as_array().unwrap() {
        let (pool, _, quote) = &pools[&format!("{}|18/18", s(entry, "order"))];
        let q = quote_fill(pool, pool.state(), *quote, num(entry, "paid"));
        assert_eq!(q.calculated_amount, num::<u128>(entry, "got"), "{entry}");
    }
    let dust = &vectors["other"][0];
    assert_eq!(s(dust, "kind"), "dust");
    let (pool, _, quote) = &pools["t0|18/18"];
    let q = quote_fill(pool, pool.state(), *quote, num(dust, "quoteIn"));
    assert_eq!(
        (q.calculated_amount, q.fees_paid),
        (num(dust, "net"), num(dust, "fee"))
    );
}

#[test]
fn full_fill_refusal_and_explicit_partial_result() {
    let vectors: Value = serde_json::from_str(PARITY).unwrap();
    let mut overflow_checked = false;
    let mut checked = 0;
    for scenario in vectors["scenarios"].as_array().unwrap() {
        let created = &scenario["create"];
        let pool = pool_from_created(created, state(&created["state"]));
        let find = |label: &str| {
            scenario["steps"]
                .as_array()
                .unwrap()
                .iter()
                .find(|step| s(step, "label") == label)
                .unwrap()
        };
        let params = |step: &Value| {
            let token = if step["specified_is_token1"].as_bool().unwrap() {
                pool.key().token1
            } else {
                pool.key().token0
            };
            QuoteParams {
                token_amount: TokenAmount {
                    token,
                    amount: num(step, "amount"),
                },
                sqrt_ratio_limit: optional_limit(step),
                override_state: Some(state(&step["pre"])),
                meta: num(step, "ts"),
            }
        };

        if s(scenario, "name").starts_with("overflow") {
            // Near the top of the price range an exact-input buy can take all its input and pay
            // out nothing (the creator fee takes the last rounded unit); an exact-output buy of
            // one raw token does not fit an int128 and reverts.
            for label in ["buyMaxExactIn", "buyHalfMaxExactIn"] {
                let step = find(label);
                let q = pool.quote(params(step)).unwrap();
                assert_eq!(q.consumed_amount, num::<i128>(step, "amount"), "{label}");
                assert_eq!(q.calculated_amount, 0, "{label}");
                assert_eq!(
                    pool.quote_full_fill(params(step)),
                    Err(ZeroSeedLaunchFullFillError::ZeroOutput),
                    "{label}"
                );
            }
            assert_eq!(
                pool.quote_full_fill(params(find("buyOneTokenExactOut"))),
                Err(ZeroSeedLaunchFullFillError::Quote(
                    ZeroSeedLaunchPoolQuoteError::Overflow
                ))
            );
            overflow_checked = true;
            continue;
        }
        // Buying beyond the inventory: the low-level quote is the explicit partial fill Core
        // executes at the upper bound; the full-fill variant refuses it.
        for label in ["exhaustExactIn", "exhaustExactOut", "buyToMidLimit"] {
            let step = find(label);
            let partial = pool.quote(params(step)).unwrap();
            let requested: i128 = num(step, "amount");
            assert!(partial.consumed_amount.abs() < requested.abs(), "{label}");
            assert_eq!(
                pool.quote_full_fill(params(step)),
                Err(ZeroSeedLaunchFullFillError::PartialFill {
                    requested,
                    filled: partial.consumed_amount
                }),
                "{label}"
            );
        }
        let upper = pool.launch().range.pool_bounds();
        let exhausted = state(&find("exhaustExactIn")["post"]);
        let bound = if pool.launch().range.launch_token_is_token1 {
            upper.0
        } else {
            upper.1
        };
        assert_eq!(exhausted.sqrt_ratio, to_sqrt_ratio::<Evm>(bound).unwrap());
        // Nothing left above the upper bound and no bid at the ask: zero fills.
        for label in [
            "afterUpperExactIn",
            "afterUpperExactOut",
            "noBidSellExactIn",
            "noBidSellExactOut",
        ] {
            let step = find(label);
            let q = pool.quote(params(step)).unwrap();
            assert_eq!(
                (q.consumed_amount, q.calculated_amount, q.fees_paid),
                (0, 0, 0),
                "{label}"
            );
            assert!(matches!(
                pool.quote_full_fill(params(step)),
                Err(ZeroSeedLaunchFullFillError::PartialFill { filled: 0, .. })
            ));
        }
        // A full exact-input fill that pays out nothing is refused too.
        let step = find("dustSellExactIn");
        let q = pool.quote(params(step)).unwrap();
        if q.calculated_amount == 0 {
            assert_eq!(
                pool.quote_full_fill(params(step)),
                Err(ZeroSeedLaunchFullFillError::ZeroOutput)
            );
        }
        // An ordinary buy passes.
        assert!(pool.quote_full_fill(params(find("buyExactIn"))).is_ok());
        checked += 1;
    }
    assert!(overflow_checked);
    assert_eq!(checked, 10);
}

#[test]
fn unsupported_instances_and_quotes_fail_closed() {
    let fixture = indexer();
    let launches = indexed_launches(&fixture);
    for launch in launches.values() {
        let (key, config, core) = (launch.key, launch.config, launch.created_state);
        let mut observed = launch.instance;
        observed.extension_runtime = U256::ZERO;
        assert!(EvmZeroSeedLaunchPool::new(key, config, core, &observed).is_err());
        let mut wrong_key = key;
        wrong_key.config.fee = 1;
        assert_eq!(
            EvmZeroSeedLaunchPool::new(wrong_key, config, core, &launch.instance),
            Err(ZeroSeedLaunchPoolConstructionError::FeeMustBeZero)
        );
        let mut wrong_key = key;
        wrong_key.config.extension = Address::ZERO;
        assert!(EvmZeroSeedLaunchPool::new(wrong_key, config, core, &launch.instance).is_err());
        // A pool whose quote is not the instance's constructor quote.
        let mut wrong_key = key;
        if config.range.launch_token_is_token1 {
            wrong_key.token0 = address("0x0000000000000000000000000000000000000001");
        } else {
            wrong_key.token1 = address("0xfffffffffffffffffffffffffffffffffffffffe");
        }
        assert_eq!(
            EvmZeroSeedLaunchPool::new(wrong_key, config, core, &launch.instance),
            Err(ZeroSeedLaunchPoolConstructionError::UnsupportedQuoteToken)
        );
        for (ask, upper) in [(i32::MIN, 0), (0, i32::MAX), (0, i32::MIN)] {
            let mut invalid = config;
            invalid.range.ask_tick = ask;
            invalid.range.upper_tick = upper;
            assert_eq!(
                EvmZeroSeedLaunchPool::new(key, invalid, core, &launch.instance),
                Err(ZeroSeedLaunchPoolConstructionError::InvalidLaunchConfig)
            );
        }
        // The native quote, address(0), can only be token0: a "launch token" at address(0) is
        // refused by the arithmetic constructor too.
        if launch.instance.quote_kind == ZeroSeedLaunchQuoteKind::Native {
            let mut flipped = config;
            flipped.range.launch_token_is_token1 = false;
            assert!(EvmZeroSeedLaunchPool::new_math(key, flipped, core).is_err());
        }
    }
}

#[test]
fn manifest_and_local_producer_negative_controls() {
    let fixture = indexer();
    let launches = indexed_launches(&fixture);
    for label in ["l1", "l2"] {
        let launch = &launches[label];
        let observed = launch.instance;
        observed.validate().unwrap();
        let key = launch.key;
        let native = observed.quote_kind == ZeroSeedLaunchQuoteKind::Native;

        // Each provenance component is essential, not merely an arbitrary caller allowlist.
        for i in 0..11 {
            let mut bad = observed;
            match i {
                0 => bad.chain_id = 8453,
                1 => bad.extension = Address::ZERO,
                2 => bad.extension_runtime = U256::ZERO,
                3 => bad.periphery = observed.extension,
                4 => bad.periphery_runtime = observed.extension_runtime,
                5 => bad.core = Address::ZERO,
                6 => bad.core_runtime = U256::ZERO,
                7 => bad.constructor_quote = address(QUOTE_LOW),
                8 => bad.quote_token_getter = address(QUOTE_LOW),
                9 => {
                    bad.quote_kind = if native {
                        // A native quote has no runtime to bind; claiming one is refused.
                        ZeroSeedLaunchQuoteKind::Erc20 {
                            quote_runtime: U256::from_str(
                                "0x8a3a1f6a9f9dce633117adee5b458245835a8645a8c8726a26382a4622508b1c",
                            )
                            .unwrap(),
                        }
                    } else {
                        ZeroSeedLaunchQuoteKind::Native
                    }
                }
                // Any other quote runtime, or an ERC-20 kind for the native address.
                _ => {
                    bad.quote_kind = ZeroSeedLaunchQuoteKind::Erc20 {
                        quote_runtime: U256::ZERO,
                    }
                }
            }
            assert_eq!(
                bad.validate(),
                Err(ZeroSeedLaunchParameterError::UnsupportedInstance),
                "{label} component {i}"
            );
            assert!(
                EvmZeroSeedLaunchPool::new(key, launch.config, launch.created_state, &bad).is_err()
            );
        }
        let mut bad = observed;
        let pins: Value = serde_json::from_str(PINS).unwrap();
        bad.extension_runtime = U256::from_str(s(
            &pins["ZeroSeedLaunch"]["templateRuntime"],
            "zeroFilledKeccak",
        ))
        .unwrap();
        assert!(
            bad.validate().is_err(),
            "zero-filled template is not executed provenance"
        );

        for sink in [
            Address::ZERO,
            observed.core,
            observed.extension,
            observed.periphery,
            key.token0,
            key.token1,
        ] {
            assert_eq!(
                validate_claim_recipient(&observed, &key, sink),
                Err(ZeroSeedLaunchParameterError::InvalidRecipient)
            );
        }
        validate_claim_recipient(
            &observed,
            &key,
            address("0x0000000000000000000000000000000000000001"),
        )
        .unwrap();

        let installation = &fixture["installations"][label];
        let mut parameters = ZeroSeedLaunchParameters {
            supply: num(installation, "requestedSupply"),
            range: launch.config.range,
            fee: launch.config.fee,
        };
        parameters.fee.trading_start = 301;
        let mut context = ZeroSeedLaunchLocalPreview {
            instance: &observed,
            owner: address(s(installation, "owner")),
            salt: b256(s(installation, "userSalt")),
            name: "éééééééééééééééa",
            symbol: "ZERO",
            decimals: 18,
            predicted_token_has_code: false,
            build_time: 1,
            execution_expiry: 301,
        };
        assert_eq!(context.name.len(), 31);
        assert_eq!(
            context.predicted_token() < observed.quote(),
            !parameters.range.launch_token_is_token1
        );
        let preview = preview_installation(&parameters, 1, &context).unwrap();
        let requested = parameters.supply;
        parameters.supply = preview.installed_supply;
        assert!(parameters.supply <= requested);
        check_launch_binding(&parameters, preview.liquidity, 1, &context).unwrap();
        assert!(check_launch_binding(&parameters, preview.liquidity + 1, 1, &context).is_err());

        let mut flipped = parameters;
        flipped.range.launch_token_is_token1 = !flipped.range.launch_token_is_token1;
        assert_eq!(
            context.validate(&flipped, 1),
            Err(ZeroSeedLaunchParameterError::TokenOrderMismatch)
        );

        context.name = "éééééééééééééééé"; // 16 characters, 32 bytes.
        assert_eq!(
            preview_installation(&parameters, 1, &context),
            Err(ZeroSeedLaunchParameterError::MetadataTooLong)
        );
        context.name = "ZERO";
        context.symbol = "éééééééééééééééé";
        assert_eq!(
            context.validate(&parameters, 1),
            Err(ZeroSeedLaunchParameterError::MetadataTooLong)
        );
        context.symbol = "";
        context.predicted_token_has_code = true;
        assert_eq!(
            context.validate(&parameters, 1),
            Err(ZeroSeedLaunchParameterError::LaunchTokenExists)
        );
        context.predicted_token_has_code = false;
        for start in [1, 300, 86402] {
            parameters.fee.trading_start = start;
            assert_eq!(
                context.validate(&parameters, 1),
                Err(ZeroSeedLaunchParameterError::InvalidLocalTiming)
            );
        }
        for start in [301, 86401] {
            parameters.fee.trading_start = start;
            context.execution_expiry = start;
            context.validate(&parameters, 1).unwrap();
            for expiry in [0, 1, start + 1] {
                context.execution_expiry = expiry;
                assert!(context.validate(&parameters, 1).is_err());
            }
        }
        parameters.fee.trading_start = 301;
        context.execution_expiry = 301;
        assert!(context.validate(&parameters, 0).is_err(), "future build");
        assert!(
            context.validate(&parameters, 2).is_err(),
            "fresh margin must remain"
        );
        assert!(
            context.validate(&parameters, 301).is_err(),
            "expired at equality"
        );
        parameters.fee.trading_start = 86401;
        context.execution_expiry = 2;
        assert!(
            context.validate(&parameters, 2).is_err(),
            "expiry with ample start margin"
        );
        context.build_time = u64::MAX - 299;
        context.execution_expiry = u64::MAX;
        assert_eq!(
            context.validate(&parameters, context.build_time),
            Err(ZeroSeedLaunchParameterError::Overflow)
        );
        context.build_time = 1;
        assert_eq!(
            context.validate(&parameters, u64::MAX),
            Err(ZeroSeedLaunchParameterError::Overflow)
        );
    }
}

// ---------------------------------------------------------------------------------------------
// Pinned ABIs against the consumer manifest.
// ---------------------------------------------------------------------------------------------

fn canonical_type(param: &Value) -> String {
    let ty = s(param, "type");
    match ty.strip_prefix("tuple") {
        Some(suffix) => format!(
            "({}){suffix}",
            param["components"]
                .as_array()
                .unwrap()
                .iter()
                .map(canonical_type)
                .collect::<Vec<_>>()
                .join(",")
        ),
        None => ty.to_owned(),
    }
}

fn entry_signature(entry: &Value) -> String {
    format!(
        "{}({})",
        s(entry, "name"),
        entry["inputs"]
            .as_array()
            .unwrap()
            .iter()
            .map(canonical_type)
            .collect::<Vec<_>>()
            .join(",")
    )
}

/// Every function selector, event topic and error selector of the consumer manifest (56) is
/// recomputed from the pinned ABI files, and each ABI file is byte-for-byte the manifest's
/// canonical JSON (`jq -cS .abi`, no trailing newline).
#[test]
fn pinned_abis_match_the_consumer_manifest() {
    let pins: Value = serde_json::from_str(PINS).unwrap();
    let manifest = &pins["consumerManifest"];
    assert_eq!(
        s(manifest, "frozenCommit"),
        "4f1a3060b099e8a50469848118f44c0c65cfab9a"
    );
    let mut entries = 0;
    for (name, abi) in [
        ("ZeroSeedLaunch", ABI_LAUNCH),
        ("ZeroSeedLaunchPeriphery", ABI_PERIPHERY),
        ("MintableERC20", ABI_TOKEN),
    ] {
        assert!(!abi.ends_with('\n'));
        let digest = sha256_hex(abi.as_bytes());
        assert_eq!(digest, s(&manifest["abiSha256"], name), "{name}");
        assert_eq!(digest, s(&pins[name], "abiSha256"), "{name}");
        let parsed: Value = serde_json::from_str(abi).unwrap();
        assert_eq!(
            serde_json::to_string(&parsed).unwrap(),
            abi,
            "{name} canonical"
        );
        let Some(expected) = manifest["abi"].get(name) else {
            continue;
        };
        for (kind, table, width) in [
            ("function", "functions", 4),
            ("event", "events", 32),
            ("error", "errors", 4),
        ] {
            let computed: HashMap<String, String> = parsed
                .as_array()
                .unwrap()
                .iter()
                .filter(|e| s(e, "type") == kind)
                .map(|e| {
                    let signature = entry_signature(e);
                    let hash = keccak256(signature.as_bytes());
                    (signature, format!("0x{}", hex::encode(&hash[..width])))
                })
                .collect();
            let expected = expected[table].as_object().unwrap();
            assert_eq!(computed.len(), expected.len(), "{name} {table}");
            for (signature, value) in expected {
                assert_eq!(
                    computed.get(signature).map(String::as_str),
                    value.as_str(),
                    "{name} {signature}"
                );
                entries += 1;
            }
        }
    }
    assert_eq!(entries, 56);
    for (topic, signature) in [
        (LAUNCH_CREATED, "LaunchCreated"),
        (LAUNCH_SWAPPED, "LaunchSwapped"),
        (CREATOR_FEES_CLAIMED, "CreatorFeesClaimed"),
    ] {
        let found = manifest["abi"]["ZeroSeedLaunch"]["events"]
            .as_object()
            .unwrap()
            .iter()
            .find(|(k, _)| k.starts_with(&format!("{signature}(")))
            .unwrap();
        assert_eq!(found.1.as_str(), Some(topic));
    }
    for (topic, signature) in [
        (LAUNCH_OWNER_CHANGED, "LaunchOwnerChanged"),
        (LAUNCH_FEES_CLAIMED, "LaunchFeesClaimed"),
    ] {
        let found = manifest["abi"]["ZeroSeedLaunchPeriphery"]["events"]
            .as_object()
            .unwrap()
            .iter()
            .find(|(k, _)| k.starts_with(&format!("{signature}(")))
            .unwrap();
        assert_eq!(found.1.as_str(), Some(topic));
    }

    // The embedded MintableERC20 creation code is the pinned artifact's.
    let creation = keccak256(&MINTABLE_ERC20_CREATION_CODE[..]);
    assert_eq!(creation, b256(MINTABLE_ERC20_CREATION_CODE_KECCAK));
    assert_eq!(
        creation,
        b256(s(&pins["MintableERC20"]["creation"], "keccak"))
    );
    assert_eq!(
        MINTABLE_ERC20_CREATION_CODE.len(),
        pins["MintableERC20"]["creation"]["bytes"].as_u64().unwrap() as usize
    );
    assert_eq!(
        extension_token_salt(Address::ZERO, B256::ZERO),
        keccak256([0u8; 64])
    );

    // The SDK's compiled-in pins are exactly the two pinned local fixtures.
    let fixture = indexer();
    for (label, entry) in pins["localFixtures"].as_object().unwrap() {
        let instance = fixture_instance(&fixture, label);
        instance.validate().unwrap();
        assert_eq!(instance.extension, address(s(entry, "extension")));
        assert_eq!(instance.periphery, address(s(entry, "periphery")));
        assert_eq!(
            instance.extension_runtime,
            U256::from_str(s(entry, "extensionRuntimeKeccak")).unwrap()
        );
        assert_eq!(
            instance.periphery_runtime,
            U256::from_str(s(entry, "peripheryRuntimeKeccak")).unwrap()
        );
        assert_eq!(instance.quote(), address(s(entry, "quote")));
    }
}
