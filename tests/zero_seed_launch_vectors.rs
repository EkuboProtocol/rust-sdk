//! Reproduces the `ZeroSeedLaunch` vectors in `tests/vectors`: the contract's frozen integer
//! vectors, the parity vectors read from local `Core`, extension, periphery and token state and
//! events, the indexer's LOCAL anvil receipt of the supported instance, and the pinned ABIs.
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
                ZERO_SEED_LAUNCH_MAX_CREATOR_FEE, ZeroSeedLaunchConfig, ZeroSeedLaunchFeeSchedule,
                ZeroSeedLaunchFullFillError, ZeroSeedLaunchInstallation, ZeroSeedLaunchInstance,
                ZeroSeedLaunchLocalPreview, ZeroSeedLaunchParameterError, ZeroSeedLaunchParameters,
                ZeroSeedLaunchPoolConstructionError, ZeroSeedLaunchPoolQuoteError,
                ZeroSeedLaunchPoolState, ZeroSeedLaunchQuoteKind, ZeroSeedLaunchQuoteObservation,
                ZeroSeedLaunchRange, extension_token_salt, installation_math, launch_token_address,
                periphery_launch_salt, periphery_launch_token_address, preview_installation,
                preview_installation_math, validate_claim_recipient,
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

const TARGET_COMMIT: &str = "550afc40280423128c02eb5ffd213aa959b34e2a";
const CORE_RUNTIME: &str = "0xc5f90c9d0dbc5037f8f9e248f4bb292e7c1824f584eb6550cb4cad525b38c71a";

/// Fixture quote tokens of the contract tests: the high one makes the launch token token0.
const QUOTE_HIGH: &str = "0xffffffffffffffffffffffffffffffffffffffff";
const QUOTE_LOW: &str = "0x0000000000000000000000000000000000010000";

const TRANSFER_FROM_FAILED: &str = "0x7939f424";
const TRADING_NOT_STARTED: &str = "0xacf75be8";
const SQRT_RATIO_LIMIT_WRONG_DIRECTION: &str = "0xa574a6b4";
/// solady `SafeCastLib.Overflow()`: a delta does not fit an int128.
const SAFE_CAST_OVERFLOW: &str = "0x35278d12";

const LAUNCH_CREATED: &str = "0x3a4e811187f4a8c0b72396e9d7ca13aeed62eb97a599a24af1ed99066041098f";
const LAUNCH_SWAPPED: &str = "0x3e58795f52a8e88efdec2da89ea3798175f8764145ccd7bf5e40633a7d571f6d";
const CREATOR_FEES_CLAIMED: &str =
    "0xf0ffdfa84530baef2e9f8bbb160545a59bfef8da319fa27aa69e4f3c8f05a41d";
const LAUNCH_OWNER_CHANGED: &str =
    "0x478004cf03e8c3b648608ce0259ce479c813aa671a383230ee7763fe5da22391";
const LAUNCH_FEES_CLAIMED: &str =
    "0x908c6b2c19765fe47aef218b4f71ea1a10a9e156d9d5c3500c3a298e01428805";
/// Core `PositionUpdated(address,bytes32,bytes32,int128,bytes32,bytes32)`.
const POSITION_UPDATED: &str = "0x704b3ab4a76158ad4d66625a2a43be81edbffd24630e8fde5174e97035370a07";
/// ERC-20 `Transfer(address,address,uint256)`.
const TRANSFER: &str = "0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef";

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

/// A quote observation with the recorded runtime keccak, `None` for an address without code.
fn quote_observation(
    chain_id: u64,
    quote: Address,
    runtime: Option<&str>,
) -> ZeroSeedLaunchQuoteObservation {
    ZeroSeedLaunchQuoteObservation {
        chain_id,
        quote,
        quote_runtime: runtime.map(|r| U256::from_str(r).unwrap()),
    }
}

/// Requested, installed and sink supply of one creation, as recorded, against the SDK's
/// installation for the requested supply.
fn assert_supply(v: &Value, installation: &ZeroSeedLaunchInstallation, label: &str) {
    let requested: u128 = num(v, "requestedSupply");
    let installed: u128 = num(v, "installedSupply");
    let sink: u128 = num(v, "sinkSupply");
    assert_eq!(
        installation.installed_supply, installed,
        "{label} installed"
    );
    assert_eq!(installation.sink_supply, sink, "{label} sink");
    assert_eq!(
        installed + sink,
        requested,
        "{label} requested = installed + sink"
    );
    assert!(0 < installed && installed <= requested, "{label}");
    if v.get("totalSupply").is_some() {
        assert_eq!(
            num::<u128>(v, "totalSupply"),
            requested,
            "{label} totalSupply"
        );
        assert_eq!(
            num::<u128>(v, "balanceOfZero"),
            sink,
            "{label} balanceOf(0)"
        );
        assert_eq!(
            num::<i128>(v, "positionTokenDelta"),
            installed as i128,
            "{label} Core position delta"
        );
    }
}

// ---------------------------------------------------------------------------------------------
// Supported LOCAL fixture: one extension and periphery for every quote, `pins.localFixture`.
// ---------------------------------------------------------------------------------------------

fn pins() -> Value {
    serde_json::from_str(PINS).unwrap()
}

/// The supported instance exactly as `pins.localFixture` records it.
fn pinned_instance() -> ZeroSeedLaunchInstance {
    let pins = pins();
    let f = &pins["localFixture"];
    ZeroSeedLaunchInstance {
        chain_id: f["chainId"].as_u64().unwrap(),
        extension: address(s(f, "extension")),
        extension_runtime: U256::from_str(s(f, "extensionRuntimeKeccak")).unwrap(),
        periphery: address(s(f, "periphery")),
        periphery_runtime: U256::from_str(s(f, "peripheryRuntimeKeccak")).unwrap(),
        core: address(s(f, "core")),
        core_runtime: U256::from_str(s(f, "coreRuntimeKeccak")).unwrap(),
    }
}

/// The reviewed LOCAL ERC-20 quote, `pins.localQuotes[0]`.
fn pinned_erc20_quote() -> ZeroSeedLaunchQuoteObservation {
    let pins = pins();
    let q = &pins["localQuotes"][0];
    quote_observation(
        q["chainId"].as_u64().unwrap(),
        address(s(q, "quote")),
        Some(s(q, "runtimeKeccak")),
    )
}

/// A launch on the supported instance.
struct SupportedLaunch {
    key: EvmZeroSeedLaunchPoolKey,
    config: ZeroSeedLaunchConfig,
    state: ZeroSeedLaunchPoolState,
    quote: ZeroSeedLaunchQuoteObservation,
    requested: u128,
}

/// The two launches of the parity test that share one extension (native and ERC-20 quote), moved
/// onto the supported instance's extension: pool math does not depend on the extension address.
/// The ERC-20 quote is observed with the reviewed local quote's runtime.
fn supported_launches() -> Vec<SupportedLaunch> {
    let vectors: Value = serde_json::from_str(PARITY).unwrap();
    let instance = pinned_instance();
    vectors["scenarios"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|scenario| s(scenario, "name").starts_with("shared_"))
        .map(|scenario| {
            let created = &scenario["create"];
            let (mut key, config) = pool_inputs_from_created(created);
            key.config.extension = instance.extension;
            let quote = if s(created, "quoteKind") == "native" {
                quote_observation(instance.chain_id, Address::ZERO, None)
            } else {
                pinned_erc20_quote()
            };
            assert_eq!(quote.quote, config.quote_token);
            SupportedLaunch {
                key,
                config,
                state: state(&created["state"]),
                quote,
                requested: num(created, "requestedSupply"),
            }
        })
        .collect()
}

// ---------------------------------------------------------------------------------------------
// Indexer LOCAL receipt: the single supported instance and its launches of every quote, decoded
// from the emitted logs.
// ---------------------------------------------------------------------------------------------

fn indexer() -> Value {
    serde_json::from_str(INDEXER).unwrap()
}

/// The single instance observation exactly as the indexer receipt records it.
fn fixture_instance(fixture: &Value) -> ZeroSeedLaunchInstance {
    let instances = fixture["instances"].as_array().unwrap();
    assert_eq!(instances.len(), 1, "one extension serves every quote");
    let entry = &instances[0];
    assert!(entry.get("quote").is_none(), "an instance has no quote");
    ZeroSeedLaunchInstance {
        chain_id: fixture["chainId"].as_u64().unwrap(),
        extension: address(s(entry, "extension")),
        extension_runtime: U256::from_str(s(entry, "extensionRuntimeKeccak")).unwrap(),
        periphery: address(s(entry, "periphery")),
        periphery_runtime: U256::from_str(s(entry, "peripheryRuntimeKeccak")).unwrap(),
        core: address(s(&fixture["addresses"], "core")),
        core_runtime: U256::from_str(s(&fixture["provenance"], "coreRuntimeKeccak")).unwrap(),
    }
}

/// The launch's own quote as the receipt records it.
fn fixture_quote(fixture: &Value, recorded: &Value) -> ZeroSeedLaunchQuoteObservation {
    let quote = address(s(recorded, "quote"));
    let runtime = match s(recorded, "quoteKind") {
        "native" => {
            assert_eq!(quote, Address::ZERO);
            None
        }
        "erc20" => {
            // The receipt's one ERC-20 quote and its executed runtime.
            assert_eq!(quote, address(s(&fixture["addresses"], "erc20Quote")));
            Some(s(&fixture["provenance"], "erc20QuoteRuntimeKeccak"))
        }
        other => panic!("quote kind {other}"),
    };
    quote_observation(fixture["chainId"].as_u64().unwrap(), quote, runtime)
}

/// The creation transaction's own records of the installation: the `Installation` the periphery
/// returned, Core's `PositionUpdated` (launch-token delta == installed supply, quote delta 0,
/// liquidity delta == computed liquidity), the launch token's mint to Core and the sink mint to
/// `address(0)`, and the recorded `totalSupply` and sink balance.
fn assert_receipt_installation(
    branch_logs: &[Value],
    created: &Value,
    recorded: &Value,
    installation: &Value,
    expected: &ZeroSeedLaunchInstallation,
    key: &EvmZeroSeedLaunchPoolKey,
    token: Address,
    instance: &ZeroSeedLaunchInstance,
) {
    let label = s(recorded, "label");
    let requested: u128 = num(installation, "requestedSupply");
    let installed: u128 = num(installation, "installedSupply");
    let sink: u128 = num(installation, "sinkSupply");
    assert_eq!(expected.installed_supply, installed, "{label} installed");
    assert_eq!(expected.sink_supply, sink, "{label} sink");
    assert_eq!(installed + sink, requested, "{label}");
    assert_eq!(
        num::<u128>(installation, "totalSupply"),
        requested,
        "{label}"
    );
    assert_eq!(num::<u128>(installation, "sinkBalance"), sink, "{label}");
    assert_eq!(num::<u128>(installation, "coreInstalledDelta"), installed);
    assert_eq!(num::<u128>(installation, "coreQuoteDelta"), 0);
    assert_eq!(
        num::<u128>(installation, "coreLiquidityDelta"),
        expected.liquidity
    );
    for field in [
        "requestedSupply",
        "installedSupply",
        "sinkSupply",
        "liquidity",
    ] {
        assert_eq!(
            s(recorded, field),
            s(installation, field),
            "{label} {field}"
        );
    }
    assert_eq!(s(recorded, "quote"), s(installation, "quote"));
    assert_eq!(s(recorded, "quoteKind"), s(installation, "quoteKind"));
    assert_eq!(
        recorded["tokenIsToken1"].as_bool(),
        Some(token == key.token1),
        "{label} order"
    );
    assert_eq!(num::<i32>(recorded, "initialTick"), expected.initial_tick);

    // The returned Installation struct.
    let returned = &installation["installation"];
    assert_eq!(address(s(returned, "token")), token);
    assert_eq!(address(s(&returned["poolKey"], "token0")), key.token0);
    assert_eq!(address(s(&returned["poolKey"], "token1")), key.token1);
    assert_eq!(s(returned, "positionId"), s(recorded, "positionId"));
    assert_eq!(num::<i32>(returned, "initialTick"), expected.initial_tick);
    assert_eq!(num::<u128>(returned, "liquidity"), expected.liquidity);
    assert_eq!(num::<u128>(returned, "installedSupply"), installed);

    // The raw logs of the creation transaction.
    let tx = &created["transactionHash"];
    assert_eq!(tx.as_str(), Some(s(installation, "creationTransaction")));
    assert_eq!(
        hex_u64(created, "blockNumber"),
        installation["creationBlock"].as_u64().unwrap()
    );
    let in_tx: Vec<&Value> = branch_logs
        .iter()
        .filter(|l| &l["transactionHash"] == tx)
        .collect();
    let updates: Vec<_> = in_tx
        .iter()
        .filter(|l| {
            address(s(l, "address")) == instance.core
                && l["topics"][0].as_str() == Some(POSITION_UPDATED)
        })
        .collect();
    assert_eq!(updates.len(), 1, "{label} one PositionUpdated");
    let data = data_bytes(updates[0]);
    assert_eq!(word_address(&data, 0), instance.extension, "locker");
    assert_eq!(
        format!("{:#066x}", word(&data, 1)),
        s(recorded, "poolId"),
        "{label} pool id"
    );
    assert_eq!(
        format!("{:#066x}", word(&data, 2)),
        s(recorded, "positionId"),
        "{label} position"
    );
    assert_eq!(
        word_i128(&data, 3),
        expected.liquidity as i128,
        "{label} liquidity delta"
    );
    let delta0 = i128::from_be_bytes(data[128..144].try_into().unwrap());
    let delta1 = i128::from_be_bytes(data[144..160].try_into().unwrap());
    let (token_delta, quote_delta) = if token == key.token1 {
        (delta1, delta0)
    } else {
        (delta0, delta1)
    };
    assert_eq!(
        token_delta, installed as i128,
        "{label} Core installed delta"
    );
    assert_eq!(quote_delta, 0, "{label} no quote side");
    let mints: Vec<(Address, u128)> = in_tx
        .iter()
        .filter(|l| {
            address(s(l, "address")) == token
                && l["topics"][0].as_str() == Some(TRANSFER)
                && topic_address(l, 1) == Address::ZERO
        })
        .map(|l| (topic_address(l, 2), word_u128(&data_bytes(l), 0)))
        .collect();
    let mut expected_mints = vec![(instance.core, installed)];
    if sink != 0 {
        expected_mints.push((Address::ZERO, sink));
    }
    assert_eq!(
        mints, expected_mints,
        "{label} mints: installed to Core, sink to address(0)"
    );
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
    quote: ZeroSeedLaunchQuoteObservation,
    key: EvmZeroSeedLaunchPoolKey,
    config: ZeroSeedLaunchConfig,
    token: Address,
    created_state: ZeroSeedLaunchPoolState,
}

fn indexed_launches(fixture: &Value) -> HashMap<String, IndexedLaunch> {
    assert_eq!(s(&fixture["provenance"], "evmContractsHead"), TARGET_COMMIT);
    let instance = fixture_instance(fixture);
    instance.validate().unwrap();
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
            let quote = fixture_quote(fixture, recorded);
            assert_eq!(address(s(log, "address")), instance.extension);
            assert_eq!(address(s(recorded, "extension")), instance.extension);
            assert_eq!(address(s(recorded, "periphery")), instance.periphery);

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
            assert_eq!(key.config.fee, 0);
            assert_eq!(
                keccak256(&data[..96]),
                b256(pool_id),
                "poolId = keccak(abi.encode(poolKey))"
            );
            // LaunchParameters: name, symbol, decimals, supply, quoteToken, askTick, upperTick,
            // tickSpacing, tradingStart, feeDuration, initialFee, finalFee, salt.
            let p = word(&data, 5).to::<usize>() / 32;
            let (name, symbol) = (abi_string(&data, p, p), abi_string(&data, p, p + 1));
            let decimals = word(&data, p + 2).to::<u8>();
            let requested = word_u128(&data, p + 3);
            assert_eq!(word_address(&data, p + 4), quote.quote, "per-launch quote");
            let extension_salt = B256::from(word(&data, p + 12).to_be_bytes::<32>());

            // Token: the indexed topic, the receipt, the preview and the SDK prediction agree.
            let token = topic_address(log, 2);
            let controller = topic_address(log, 3);
            assert_eq!(
                controller, instance.periphery,
                "the periphery is the controller"
            );
            assert_ne!(token, quote.quote);
            let (token0, token1) = if token < quote.quote {
                (token, quote.quote)
            } else {
                (quote.quote, token)
            };
            assert_eq!(
                (key.token0, key.token1),
                (token0, token1),
                "sorted(token, quote)"
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
            if quote.quote_runtime.is_none() {
                assert!(is1, "native launches are token1");
            }
            let range = ZeroSeedLaunchRange {
                launch_token_is_token1: is1,
                ask_tick: word_i32(&data, p + 5),
                upper_tick: word_i32(&data, p + 6),
                tick_spacing: word(&data, p + 7).to::<u32>(),
            };
            assert_eq!(range.tick_spacing, key.config.pool_type_config.0);
            let position = word(&data, 3).to_be_bytes::<32>();
            let (lower, upper) = range.pool_bounds();
            assert_eq!(&position[..24], &[0u8; 24], "position salt 0");
            assert_eq!(
                (
                    i32::from_be_bytes(position[24..28].try_into().unwrap()),
                    i32::from_be_bytes(position[28..32].try_into().unwrap())
                ),
                (lower, upper)
            );
            let config = ZeroSeedLaunchConfig {
                quote_token: quote.quote,
                range,
                liquidity: word_u128(&data, 4),
                fee: ZeroSeedLaunchFeeSchedule {
                    trading_start: word(&data, p + 8).to::<u64>(),
                    fee_duration: word(&data, p + 9).to::<u32>(),
                    initial_fee: word(&data, p + 10).to::<u64>(),
                    final_fee: word(&data, p + 11).to::<u64>(),
                },
            };
            assert!(config.liquidity > 0);
            assert!(requested > 0 && requested <= i128::MAX as u128);
            assert_eq!(requested, num::<u128>(installation, "requestedSupply"));
            assert_eq!(config.liquidity, num::<u128>(installation, "liquidity"));
            assert_eq!(
                config.fee.trading_start,
                num::<u64>(installation, "tradingStart")
            );
            // Creation installs exactly the preview of the requested supply, which is never
            // rewritten: the event carries the requested supply and the computed liquidity.
            let parameters = ZeroSeedLaunchParameters {
                supply: requested,
                quote_token: quote.quote,
                range,
                fee: config.fee,
            };
            let installed = installation_math(&parameters, 0).unwrap();
            assert_eq!(
                installed,
                preview_installation_math(&parameters, 0).unwrap()
            );
            assert_eq!(installed.liquidity, config.liquidity);
            assert_receipt_installation(
                branch["logs"].as_array().unwrap(),
                log,
                recorded,
                installation,
                &installed,
                &key,
                token,
                &instance,
            );

            let created_state = initial_state(&range, config.liquidity);
            let previous = launches.insert(
                label.clone(),
                IndexedLaunch {
                    label: label.clone(),
                    instance,
                    quote,
                    key,
                    config,
                    token,
                    created_state,
                },
            );
            assert!(previous.is_none());
        }
    }
    assert_eq!(
        launches.len(),
        fixture["launches"].as_object().unwrap().len()
    );
    let kinds: Vec<_> = launches
        .values()
        .map(|l| l.quote.supported_kind())
        .collect();
    assert!(kinds.contains(&Ok(ZeroSeedLaunchQuoteKind::Native)));
    assert!(
        kinds
            .iter()
            .any(|k| matches!(k, Ok(ZeroSeedLaunchQuoteKind::Erc20 { .. })))
    );
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
            &launch.quote,
        )
        .unwrap();
        assert_eq!(pool.state(), launch.created_state);
        // Another launch's quote is not an alias for this launch's.
        for other in launches
            .values()
            .filter(|o| o.quote.quote != launch.quote.quote)
        {
            assert_eq!(
                EvmZeroSeedLaunchPool::new(
                    launch.key,
                    launch.config,
                    launch.created_state,
                    &launch.instance,
                    &other.quote
                ),
                Err(ZeroSeedLaunchPoolConstructionError::UnsupportedQuoteToken)
            );
        }
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
/// `feeAt(block time)`, owner and controller. `l5` and `l6` are created at the highest rate,
/// `2**64 - 1`: their swaps at that rate net `floor(gross / 2**64)` (exact input) and pay
/// `calc * 2**64` (exact output).
#[test]
fn indexer_trades_ledgers_owners_and_fees_replay() {
    let fixture = indexer();
    let launches = indexed_launches(&fixture);
    let mut prefix = HashMap::new();
    let (mut swaps_checked, mut claims_checked, mut snapshots_checked) = (0, 0, 0);
    let (mut swap_actions, mut claim_actions) = (0, 0);
    // Per launch: swaps, claims, snapshots, and swaps at the highest rate.
    let mut per_launch: HashMap<&str, [usize; 4]> = HashMap::new();
    let mut max_rate_fills = Vec::new();
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
                        claim_actions += 1;
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
                        per_launch.entry(action[1]).or_default()[1] += 1;
                    }
                    "buy" | "sell" => {
                        swap_actions += 1;
                        let launch = &launches[action[1]];
                        let ledger = ledgers.get_mut(action[1]).unwrap();
                        let before = ledger.state.unwrap();
                        let pool = EvmZeroSeedLaunchPool::new(
                            launch.key,
                            launch.config,
                            before,
                            &launch.instance,
                            &launch.quote,
                        )
                        .unwrap();
                        let quote_token = launch.config.quote_token;
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
                        let counts = per_launch.entry(action[1]).or_default();
                        counts[0] += 1;
                        if pool.fee_at(timestamp) == ZERO_SEED_LAUNCH_MAX_CREATOR_FEE {
                            counts[3] += 1;
                            if amount < 0 {
                                assert_eq!(
                                    q.calculated_amount,
                                    (q.calculated_amount - q.fees_paid) << 64
                                );
                            } else {
                                assert_eq!(
                                    q.calculated_amount,
                                    (q.calculated_amount + q.fees_paid) >> 64
                                );
                            }
                            max_rate_fills.push((
                                action[1],
                                amount,
                                q.calculated_amount,
                                q.fees_paid,
                            ));
                        }
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
                let installation = &fixture["installations"][label];
                assert_eq!(
                    s(observed, "totalSupply"),
                    s(installation, "requestedSupply")
                );
                assert_eq!(s(observed, "sinkBalance"), s(installation, "sinkSupply"));
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
                per_launch.entry(label).or_default()[2] += 1;
            }
            assert_eq!(snapshot["pools"].as_array().unwrap().len(), ledgers.len());
        }
        if branch_name == "prefix" {
            prefix = ledgers;
        }
    }
    assert_eq!(swaps_checked, swap_actions);
    assert_eq!(claims_checked, claim_actions);
    assert_eq!(
        (swaps_checked, claims_checked, snapshots_checked),
        (26, 10, 62)
    );
    for (label, counts) in [
        ("l1", [10, 5, 17, 0]),
        ("l2", [4, 2, 16, 0]),
        ("l3", [1, 0, 2, 0]),
        ("l4", [4, 1, 9, 0]),
        ("l5", [5, 1, 9, 2]),
        ("l6", [2, 1, 9, 2]),
    ] {
        assert_eq!(per_launch[label], counts, "{label}");
    }
    // Both maximum-rate launches are created normally at `2**64 - 1`.
    let l5 = &launches["l5"].config.fee;
    assert_eq!(
        (l5.initial_fee, l5.final_fee, l5.fee_duration),
        (u64::MAX, 55_340_232_221_128_654, 3600)
    );
    let l6 = &launches["l6"].config.fee;
    assert_eq!(
        (l6.initial_fee, l6.final_fee, l6.fee_duration),
        (u64::MAX, u64::MAX, 1)
    );
    let paid = 184_817_928_874_495_997_640_704;
    assert_eq!(paid, 10_019 << 64);
    for label in ["l5", "l6"] {
        let fills: Vec<_> = max_rate_fills
            .iter()
            .filter(|f| f.0 == label)
            .map(|f| (f.1, f.2, f.3))
            .collect();
        assert_eq!(fills.len(), 2, "{label}");
        assert_eq!(
            (fills[0].0, fills[0].1),
            (1_000_000_000_000_000_000, 54_160)
        );
        assert_eq!(fills[1], (-10_000_000_000, paid, paid - 10_019));
    }
    assert_eq!(
        max_rate_fills[0].3, 999_083_373_736_809_197_195_735,
        "l5 exact-in fee"
    );
}

/// The receipt's single instance and its ERC-20 quotes are exactly the pinned local fixture, which
/// the SDK compiles in.
#[test]
fn local_fixture_pins_match_the_indexer_receipt() {
    let fixture = indexer();
    let pins = pins();
    assert_eq!(s(&fixture["provenance"], "evmContractsHead"), TARGET_COMMIT);
    let instance = fixture_instance(&fixture);
    assert_eq!(instance, pinned_instance());
    instance.validate().unwrap();
    let entry = &fixture["instances"][0];
    let pinned = &pins["localFixture"];
    for field in ["extension", "periphery"] {
        assert_eq!(
            address(s(entry, field)),
            address(s(pinned, field)),
            "{field}"
        );
    }
    for field in ["extensionSalt", "peripherySalt"] {
        assert_eq!(s(entry, field), s(pinned, field), "{field}");
    }
    let provenance = &fixture["provenance"];
    assert_eq!(s(provenance, "coreRuntimeKeccak"), CORE_RUNTIME);
    for (contract, template, creation, abi) in [
        (
            "ZeroSeedLaunch",
            "launchRuntimeTemplateKeccak",
            "launchCreationKeccak",
            "launchAbiSha256",
        ),
        (
            "ZeroSeedLaunchPeriphery",
            "peripheryRuntimeTemplateKeccak",
            "peripheryCreationKeccak",
            "peripheryAbiSha256",
        ),
    ] {
        let pinned = &pins[contract];
        assert_eq!(
            s(provenance, template),
            s(&pinned["templateRuntime"], "zeroFilledKeccak")
        );
        assert_eq!(s(provenance, creation), s(&pinned["creation"], "keccak"));
        assert_eq!(s(provenance, abi), s(pinned, "abiSha256"));
    }
    assert_eq!(
        s(entry, "extensionRuntimeTemplateKeccak"),
        s(provenance, "launchRuntimeTemplateKeccak")
    );
    assert_eq!(
        s(entry, "peripheryRuntimeTemplateKeccak"),
        s(provenance, "peripheryRuntimeTemplateKeccak")
    );
    let mut kinds = Vec::new();
    for recorded in fixture["launches"].as_object().unwrap().values() {
        assert_eq!(s(recorded, "instance"), s(entry, "label"));
        kinds.push(s(recorded, "quoteKind"));
        let quote = fixture_quote(&fixture, recorded);
        match quote.supported_kind().unwrap() {
            ZeroSeedLaunchQuoteKind::Native => assert_eq!(quote.quote, Address::ZERO),
            ZeroSeedLaunchQuoteKind::Erc20 { .. } => assert_eq!(quote, pinned_erc20_quote()),
        }
    }
    kinds.sort_unstable();
    assert_eq!(
        kinds,
        ["erc20", "erc20", "erc20", "native", "native", "native"]
    );
}

// ---------------------------------------------------------------------------------------------
// Foundry parity vectors.
// ---------------------------------------------------------------------------------------------

/// The parity instance observation: its runtimes are executed code of the target, but its
/// extension and periphery addresses are the test harness's, not the supported pin.
fn parity_instance(created: &Value) -> ZeroSeedLaunchInstance {
    ZeroSeedLaunchInstance {
        chain_id: 31337,
        extension: address(s(created, "extension")),
        extension_runtime: U256::from_str(s(created, "extensionCodehash")).unwrap(),
        periphery: address(s(created, "periphery")),
        periphery_runtime: U256::from_str(s(created, "peripheryCodehash")).unwrap(),
        core: address("0x00000000000014aa86c5d3c41765bb24e11bd701"),
        core_runtime: U256::from_str(s(created, "coreCodehash")).unwrap(),
    }
}

/// The parity launch's quote as executed: native ETH, or a harness ERC-20 with its runtime.
fn parity_quote(created: &Value) -> ZeroSeedLaunchQuoteObservation {
    let runtime = s(created, "quoteCodehash");
    quote_observation(
        31337,
        address(s(created, "quote")),
        (runtime != "none").then_some(runtime),
    )
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
        quote_token: address(s(created, "quote")),
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
    assert_eq!(
        EvmZeroSeedLaunchPool::new(
            key,
            config,
            state,
            &parity_instance(created),
            &parity_quote(created)
        ),
        Err(ZeroSeedLaunchPoolConstructionError::UnsupportedInstance)
    );
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
    let pins = pins();
    let scenarios = vectors["scenarios"].as_array().unwrap();
    assert_eq!(scenarios.len(), 13);
    let mut compared = 0;
    let mut refused = 0;
    let mut claims = 0;
    let mut native = 0;
    let mut routed = 0;
    let mut shared = Vec::new();
    let mut gas = Vec::new();

    for scenario in scenarios {
        let name = s(scenario, "name");
        let created = &scenario["create"];
        assert_eq!(s(created, "coreCodehash"), CORE_RUNTIME);
        // The harness runs the pinned extension code (constructor `(core)`, runtime independent
        // of its address and of every quote) at an unpinned address.
        assert_eq!(
            s(created, "extensionCodehash"),
            s(&pins["localFixture"], "extensionRuntimeKeccak")
        );
        assert_ne!(
            address(s(created, "extension")),
            address(s(&pins["localFixture"], "extension"))
        );
        let core_state = state(&created["state"]);
        let pool = pool_from_created(created, core_state);
        // The SDK's installation state equals what Core holds after create.
        assert_eq!(
            initial_state(&pool.launch().range, pool.launch().liquidity),
            core_state,
            "{name} initial state"
        );
        // Requested supply submitted unchanged; installed + sink = requested = totalSupply.
        let requested: u128 = num(created, "requestedSupply");
        assert_eq!(
            num::<u128>(created, "supply"),
            requested,
            "{name} emitted supply"
        );
        let installation = installation_math(
            &ZeroSeedLaunchParameters {
                supply: requested,
                quote_token: pool.launch().quote_token,
                range: pool.launch().range,
                fee: pool.launch().fee,
            },
            num(created, "createTs"),
        )
        .unwrap();
        assert_eq!(installation.liquidity, pool.launch().liquidity, "{name}");
        assert_supply(created, &installation, name);

        let launch_is1 = pool.launch().range.launch_token_is_token1;
        let quote = parity_quote(created);
        assert_eq!(quote.validate_code(), Ok(()));
        if s(created, "quoteKind") == "native" {
            assert_eq!(pool.key().token0, Address::ZERO, "{name}");
            assert!(launch_is1, "{name}: native quote is token0");
            assert_eq!(quote.supported_kind(), Ok(ZeroSeedLaunchQuoteKind::Native));
            native += 1;
        } else {
            // The harness ERC-20 quotes are not the reviewed local quote.
            assert_eq!(
                quote.supported_kind(),
                Err(ZeroSeedLaunchParameterError::QuoteNotReviewed)
            );
        }
        if name.starts_with("shared_") {
            shared.push((
                pool.key().config.extension,
                address(s(created, "periphery")),
                s(created, "quoteKind").to_owned(),
            ));
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
            let via_router = step["via_router"].as_bool().unwrap();
            routed += usize::from(via_router);
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

            // Gas is fitted to the test locker's forwarded frame; the shared-extension scenario
            // also measures the router frame and is not part of the calibration set.
            if (swap.delta0 != 0 || swap.delta1 != 0) && !name.starts_with("shared_") {
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
    assert_eq!(native, 4);
    assert_eq!(claims, 10);
    assert_eq!(compared + refused, 522);
    assert_eq!(routed, 11);
    assert!(compared >= 300, "compared {compared}");
    // One extension and one periphery serve both the native and the ERC-20 launch.
    assert_eq!(shared.len(), 2);
    assert_eq!((shared[0].0, shared[0].1), (shared[1].0, shared[1].1));
    assert_ne!(shared[0].2, shared[1].2);

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

/// Decodes a contract revert into the SDK error it corresponds to.
fn decode_error(data: &str) -> ZeroSeedLaunchParameterError {
    let word = |i: usize| -> u128 {
        let start = 10 + 64 * i;
        u128::from_str_radix(&data[start + 32..start + 64], 16).unwrap()
    };
    match &data[..10] {
        "0xe5239090" => ZeroSeedLaunchParameterError::InvalidParameters,
        "0xf75a271a" => ZeroSeedLaunchParameterError::InvalidFeeSchedule,
        "0xe0839259" => ZeroSeedLaunchParameterError::InvalidTradingStart,
        "0x89fd41b1" => ZeroSeedLaunchParameterError::BoundsTickSpacing,
        "0x10074548" => ZeroSeedLaunchParameterError::ZeroLiquidity,
        "0x658d8331" => ZeroSeedLaunchParameterError::UnsupportedQuoteToken,
        "0x85b8e2f4" => ZeroSeedLaunchParameterError::MetadataTooLong,
        "0xf68475cd" => ZeroSeedLaunchParameterError::LaunchTokenExists,
        // solady SafeCastLib `Overflow()`
        "0x35278d12" => ZeroSeedLaunchParameterError::Overflow,
        "0x20ea795f" => ZeroSeedLaunchParameterError::LiquidityAboveTickCap {
            liquidity: word(0),
            cap: word(1),
        },
        other => panic!("unknown revert {other}"),
    }
}

/// Every periphery `previewInstallation` and the `create` that follows it with the requested
/// supply unchanged: the SDK's contract preview (quote code, metadata, parameters, collision,
/// installation) equals the contract's result, and every creation installs exactly that preview,
/// with `totalSupply` the requested supply and the remainder at `address(0)`.
#[test]
fn installation_preview_and_creation_match_the_contract() {
    let vectors: Value = serde_json::from_str(PARITY).unwrap();
    let previews = vectors["previews"].as_array().unwrap();
    let creations = vectors["creations"].as_array().unwrap();
    assert_eq!(previews.len(), 129);
    assert_eq!(creations.len(), previews.len());
    let mut ok = 0;
    let mut refusals = HashMap::new();
    for (preview, creation) in previews.iter().zip(creations) {
        let label = s(preview, "label");
        assert_eq!(s(creation, "label"), label);
        let quote = address(s(preview, "quote"));
        let predicted = address(s(preview, "predictedToken"));
        let parameters = ZeroSeedLaunchParameters {
            supply: num(preview, "supply"),
            quote_token: quote,
            range: ZeroSeedLaunchRange {
                launch_token_is_token1: quote < predicted,
                ask_tick: num(preview, "askTick"),
                upper_tick: num(preview, "upperTick"),
                tick_spacing: num(preview, "tickSpacing"),
            },
            fee: fee_schedule(preview),
        };
        let instance = ZeroSeedLaunchInstance {
            chain_id: 31337,
            extension: address(s(preview, "extension")),
            extension_runtime: U256::ZERO,
            periphery: address(s(preview, "periphery")),
            periphery_runtime: U256::ZERO,
            core: Address::ZERO,
            core_runtime: U256::ZERO,
        };
        let quote_runtime = s(preview, "quoteCodehash");
        let context = ZeroSeedLaunchLocalPreview {
            instance: &instance,
            owner: address(s(preview, "owner")),
            salt: b256(s(preview, "userSalt")),
            name: s(preview, "name"),
            symbol: s(preview, "symbol"),
            decimals: num(preview, "decimals"),
            quote_runtime: (quote_runtime != "none")
                .then(|| U256::from_str(quote_runtime).unwrap()),
            predicted_token_has_code: s(preview, "tokenHasCode") == "1",
            build_time: 0,
            execution_expiry: 0,
        };
        assert_eq!(
            context.predicted_token(),
            predicted,
            "{label} token prediction"
        );
        if label.starts_with("t1_18_18") && !label.ends_with("codelessQuote") {
            assert_eq!(quote, Address::ZERO, "native quote");
        }
        let now: u64 = num(preview, "now");
        let result = context.contract_preview(&parameters, now);
        assert_eq!(
            preview["ok"].as_bool().unwrap(),
            creation["ok"].as_bool().unwrap(),
            "{label}: creation succeeds iff the preview does"
        );
        if preview["ok"].as_bool().unwrap() {
            let installation = result.unwrap_or_else(|e| panic!("{label}: {e}"));
            assert_eq!(
                installation,
                preview_installation_math(&parameters, now).unwrap()
            );
            assert_eq!(address(s(preview, "token")), predicted);
            assert_eq!(
                s(preview, "token") == s(preview, "token0"),
                !parameters.range.launch_token_is_token1,
                "{label}"
            );
            for (field, value) in [
                ("tickLower", installation.tick_lower),
                ("tickUpper", installation.tick_upper),
                ("initialTick", installation.initial_tick),
            ] {
                assert_eq!(value, num::<i32>(preview, field), "{label} {field}");
            }
            assert_eq!(installation.liquidity, num::<u128>(preview, "liquidity"));
            assert_eq!(
                installation.installed_supply,
                num::<u128>(preview, "installedSupply"),
                "{label}"
            );
            assert_eq!(installation.sink_supply, num::<u128>(preview, "sinkSupply"));
            // Creation, one block later at the same timestamp, with the same requested supply.
            let created = installation_math(&parameters, now).unwrap();
            assert_eq!(created, installation);
            assert_eq!(num::<u128>(creation, "requestedSupply"), parameters.supply);
            assert_eq!(num::<u128>(creation, "liquidity"), created.liquidity);
            assert_supply(creation, &created, label);
            ok += 1;
        } else {
            let expected = decode_error(s(preview, "err"));
            assert_eq!(result, Err(expected), "{label}");
            assert_eq!(s(creation, "err"), s(preview, "err"), "{label}");
            *refusals
                .entry(
                    format!("{expected:?}")
                        .split(' ')
                        .next()
                        .unwrap()
                        .to_owned(),
                )
                .or_insert(0) += 1;
        }
    }
    assert_eq!(ok, 56);
    // The former 99% ceiling plus one and the highest rate, flat or decaying, are accepted in every
    // group and created normally.
    for suffix in ["_feeAboveFormerCap", "_feeAtCap", "_feeMaxEncodable"] {
        let accepted: Vec<_> = previews
            .iter()
            .filter(|p| s(p, "label").ends_with(suffix))
            .collect();
        assert_eq!(accepted.len(), 4, "{suffix}");
        for preview in accepted {
            assert!(preview["ok"].as_bool().unwrap(), "{}", s(preview, "label"));
            assert!(
                fee_schedule(preview).initial_fee > 18_262_276_632_972_456_099,
                "{suffix}"
            );
        }
    }
    assert!(!refusals.contains_key("FeeTooHigh"));
    for (refusal, count) in [
        ("InvalidFeeSchedule", 8),
        ("UnsupportedQuoteToken", 4),
        ("MetadataTooLong", 8),
        ("LaunchTokenExists", 5),
        ("ZeroLiquidity", 6),
        ("LiquidityAboveTickCap", 6),
    ] {
        assert_eq!(refusals.get(refusal), Some(&count), "{refusal}");
    }
}

/// The contract's `creator_fee_range` verdicts: every `uint64` rate is valid, `final <= initial`
/// and `duration > 0` are the only checks (`InvalidFeeSchedule`), and `2**64` is not a `uint64`
/// at all (the contract fails ABI decoding with empty revert data). The SDK's fee fields are
/// `u64`, so such a value is refused when it is parsed from its decimal string, never truncated
/// or wrapped; there is no `FeeTooHigh` refusal.
#[test]
fn creator_fee_range_verdicts() {
    let vectors: Value = serde_json::from_str(FROZEN).unwrap();
    let range = &vectors["creator_fee_range"];
    assert_eq!(s(range, "min_q64"), "0");
    assert_eq!(
        s(range, "max_q64"),
        ZERO_SEED_LAUNCH_MAX_CREATOR_FEE.to_string()
    );
    assert_eq!(ZERO_SEED_LAUNCH_MAX_CREATOR_FEE, u64::MAX);
    assert_eq!(
        s(&vectors["fixture"], "max_creator_fee_q64"),
        u64::MAX.to_string()
    );
    assert_eq!(s(range, "error"), "InvalidFeeSchedule() 0xf75a271a");
    assert_eq!(s(&range["removed"], "selector"), "0xcd4e6167");
    for unencodable in [
        s(&range["unencodable"], "value"),
        s(&range["unencodable"]["dirty_high_bits"], "value"),
    ] {
        assert!(U256::from_str(unencodable).unwrap() > U256::from(u64::MAX));
        assert!(u64::from_str(unencodable).is_err(), "{unencodable}");
    }

    let base = ZeroSeedLaunchParameters {
        supply: 1_000_000_000_000_000_000_000_000_000,
        quote_token: Address::ZERO,
        range: ZeroSeedLaunchRange {
            launch_token_is_token1: true,
            ask_tick: -13_815_500,
            upper_tick: -13_815_500 + 4_605_200,
            tick_spacing: 100,
        },
        fee: ZeroSeedLaunchFeeSchedule {
            trading_start: 1_000,
            fee_duration: 3_600,
            initial_fee: 0,
            final_fee: 0,
        },
    };
    let mut verdicts = HashMap::new();
    for vector in range["vectors"].as_array().unwrap() {
        let verdict = s(vector, "verdict");
        *verdicts.entry(verdict).or_insert(0) += 1;
        let (initial, final_fee) = (
            u64::from_str(s(vector, "initialFee")),
            u64::from_str(s(vector, "finalFee")),
        );
        let duration = vector["feeDuration"].as_u64().unwrap();
        if verdict == "abi_decoding_failure" {
            assert!(initial.is_err() || final_fee.is_err(), "{vector}");
            #[cfg(feature = "serde")]
            {
                let json = format!(
                    r#"{{"trading_start":1000,"fee_duration":{duration},"initial_fee":{},"final_fee":{}}}"#,
                    s(vector, "initialFee"),
                    s(vector, "finalFee"),
                );
                assert!(serde_json::from_str::<ZeroSeedLaunchFeeSchedule>(&json).is_err());
            }
            continue;
        }
        let fee = ZeroSeedLaunchFeeSchedule {
            trading_start: 1_000,
            fee_duration: u32::try_from(duration).unwrap(),
            initial_fee: initial.unwrap(),
            final_fee: final_fee.unwrap(),
        };
        #[cfg(feature = "serde")]
        assert_eq!(
            serde_json::from_str::<ZeroSeedLaunchFeeSchedule>(&format!(
                r#"{{"trading_start":1000,"fee_duration":{duration},"initial_fee":{},"final_fee":{}}}"#,
                fee.initial_fee, fee.final_fee
            ))
            .unwrap(),
            fee
        );
        let parameters = ZeroSeedLaunchParameters { fee, ..base };
        let result = preview_installation_math(&parameters, 1_000).map(|_| ());
        match verdict {
            "accept" => {
                assert_eq!(result, Ok(()), "{vector}");
                assert_eq!(fee.fee_at(1_000), fee.initial_fee);
                assert_eq!(
                    fee.fee_at(1_000 + u64::from(fee.fee_duration)),
                    fee.final_fee
                );
                let mut previous = fee.initial_fee;
                for t in [1, 2, 599, 600, 1800, 3599, 3600, 76_799, 76_800, 131_072] {
                    let rate = fee.fee_at(1_000 + t);
                    assert!(fee.final_fee <= rate && rate <= previous, "{vector} {t}");
                    previous = rate;
                }
                if fee.fee_duration == u32::MAX {
                    assert_eq!(fee.fee_at(1_000 + 76_800), fee.final_fee);
                }
            }
            "InvalidFeeSchedule" => assert_eq!(
                result,
                Err(ZeroSeedLaunchParameterError::InvalidFeeSchedule),
                "{vector}"
            ),
            other => panic!("verdict {other}"),
        }
    }
    assert_eq!(
        verdicts,
        HashMap::from([
            ("accept", 6),
            ("InvalidFeeSchedule", 4),
            ("abi_decoding_failure", 2)
        ])
    );
    for label in ["fixture", "consumer_default"] {
        let schedule = &range["reference_schedules"][label];
        let fee = ZeroSeedLaunchFeeSchedule {
            trading_start: 1_000,
            fee_duration: num(schedule, "feeDuration"),
            initial_fee: num(schedule, "initialFee"),
            final_fee: num(schedule, "finalFee"),
        };
        assert_eq!(
            preview_installation_math(&ZeroSeedLaunchParameters { fee, ..base }, 1_000).map(|_| ()),
            Ok(())
        );
    }
    assert_eq!(
        num::<u64>(
            &range["reference_schedules"]["consumer_default"],
            "initialFee"
        ),
        1 << 63
    );
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
    let mut sinks = Vec::new();
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
            quote_token: quote,
            range,
            fee: fee(3600),
        };
        let installation = installation_math(&parameters, 1).unwrap();
        assert_eq!(
            installation,
            preview_installation_math(&parameters, 1).unwrap()
        );
        assert_eq!(
            installation.installed_supply,
            num::<u128>(entry, "installed")
        );
        assert_eq!(installation.liquidity, num::<u128>(entry, "liquidity"));
        assert_eq!(installation.tick_lower, num::<i32>(entry, "tickLower"));
        assert_eq!(installation.tick_upper, num::<i32>(entry, "tickUpper"));
        assert_eq!(installation.initial_tick, num::<i32>(entry, "initialTick"));
        assert_eq!(
            installation.installed_supply + installation.sink_supply,
            parameters.supply
        );
        sinks.push((
            format!("{}|{decimals}", s(entry, "order")),
            installation.sink_supply,
        ));

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
                quote_token: quote,
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
    // The sink of the 1,000,000,000-token round supply in each order and decimal pair.
    sinks.sort();
    assert_eq!(
        sinks,
        [
            ("t0|18/18".to_owned(), 790),
            ("t0|18/6".to_owned(), 697_343_214),
            ("t1|18/18".to_owned(), 578),
            ("t1|18/6".to_owned(), 717_714_600),
        ]
    );

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

    // The test router's 1e18 quote buy (plain ERC-20 and native) and the one-unit dust buy.
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
        if s(scenario, "name").starts_with("shared_") {
            continue;
        }
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

// ---------------------------------------------------------------------------------------------
// Supported instance, per-launch quote support and LOCAL producer checks.
// ---------------------------------------------------------------------------------------------

#[test]
fn supported_instance_serves_native_and_erc20_quotes() {
    let instance = pinned_instance();
    instance.validate().unwrap();
    let launches = supported_launches();
    assert_eq!(launches.len(), 2);
    let kinds: Vec<_> = launches
        .iter()
        .map(|l| l.quote.supported_kind().unwrap())
        .collect();
    assert_eq!(kinds[0], ZeroSeedLaunchQuoteKind::Native);
    assert!(matches!(kinds[1], ZeroSeedLaunchQuoteKind::Erc20 { .. }));
    for launch in &launches {
        let pool = EvmZeroSeedLaunchPool::new(
            launch.key,
            launch.config,
            launch.state,
            &instance,
            &launch.quote,
        )
        .unwrap();
        assert_eq!(pool.key().config.extension, instance.extension);
        // The installation of the requested supply is the one the pool was created with.
        let installation = installation_math(
            &ZeroSeedLaunchParameters {
                supply: launch.requested,
                quote_token: launch.config.quote_token,
                range: launch.config.range,
                fee: launch.config.fee,
            },
            1,
        )
        .unwrap();
        assert_eq!(installation.liquidity, launch.config.liquidity);
        assert!(installation.sink_supply > 0);
    }
    // Each launch's quote observation is its own: the other launch's quote is refused.
    assert_eq!(
        EvmZeroSeedLaunchPool::new(
            launches[0].key,
            launches[0].config,
            launches[0].state,
            &instance,
            &launches[1].quote
        ),
        Err(ZeroSeedLaunchPoolConstructionError::UnsupportedQuoteToken)
    );
}

#[test]
fn unsupported_instances_and_quotes_fail_closed() {
    type C = ZeroSeedLaunchPoolConstructionError;
    let instance = pinned_instance();
    for launch in supported_launches() {
        let (key, config, core, quote) = (launch.key, launch.config, launch.state, launch.quote);
        let mut observed = instance;
        observed.extension_runtime = U256::ZERO;
        assert_eq!(
            EvmZeroSeedLaunchPool::new(key, config, core, &observed, &quote),
            Err(C::UnsupportedInstance)
        );
        let mut wrong_key = key;
        wrong_key.config.fee = 1;
        assert_eq!(
            EvmZeroSeedLaunchPool::new(wrong_key, config, core, &instance, &quote),
            Err(C::FeeMustBeZero)
        );
        for extension in [
            Address::ZERO,
            address("0x5100000000000000000000000000000000000000"),
        ] {
            let mut wrong_key = key;
            wrong_key.config.extension = extension;
            assert_eq!(
                EvmZeroSeedLaunchPool::new(wrong_key, config, core, &instance, &quote),
                Err(C::UnsupportedInstance)
            );
        }
        // A pool key whose quote is not the launch's own quote.
        let mut wrong_key = key;
        if config.range.launch_token_is_token1 {
            wrong_key.token0 = address("0x0000000000000000000000000000000000000001");
        } else {
            wrong_key.token1 = address("0xfffffffffffffffffffffffffffffffffffffffe");
        }
        assert_eq!(
            EvmZeroSeedLaunchPool::new(wrong_key, config, core, &instance, &quote),
            Err(C::InvalidLaunchConfig)
        );
        // Quote observations that are not this launch's supported quote.
        let mut bad_quotes = vec![
            ZeroSeedLaunchQuoteObservation {
                chain_id: 8453,
                ..quote
            },
            ZeroSeedLaunchQuoteObservation {
                quote: address("0x0000000000000000000000000000000000000001"),
                ..quote
            },
        ];
        if quote.quote_runtime.is_some() {
            bad_quotes.push(ZeroSeedLaunchQuoteObservation {
                quote_runtime: None,
                ..quote
            });
            bad_quotes.push(ZeroSeedLaunchQuoteObservation {
                quote_runtime: Some(U256::from(1)),
                ..quote
            });
        } else {
            bad_quotes.push(ZeroSeedLaunchQuoteObservation {
                quote_runtime: Some(U256::from(1)),
                ..quote
            });
        }
        for bad in bad_quotes {
            assert_eq!(
                EvmZeroSeedLaunchPool::new(key, config, core, &instance, &bad),
                Err(C::UnsupportedQuoteToken),
                "{bad:?}"
            );
        }
        for (ask, upper) in [(i32::MIN, 0), (0, i32::MAX), (0, i32::MIN)] {
            let mut invalid = config;
            invalid.range.ask_tick = ask;
            invalid.range.upper_tick = upper;
            assert_eq!(
                EvmZeroSeedLaunchPool::new(key, invalid, core, &instance, &quote),
                Err(C::InvalidLaunchConfig)
            );
        }
        // The native quote, address(0), can only be token0: a "launch token" at address(0) is
        // refused by the arithmetic constructor too.
        if quote.quote_runtime.is_none() {
            let mut flipped = config;
            flipped.range.launch_token_is_token1 = false;
            assert!(EvmZeroSeedLaunchPool::new_math(key, flipped, core).is_err());
        }
    }
}

/// Quote support is per launch: native ETH always, an ERC-20 only with a reviewed `(chain,
/// address, runtime keccak)` entry; a nonzero quote without code is the contract's own refusal.
#[test]
fn quote_support_policy() {
    type E = ZeroSeedLaunchParameterError;
    let native = quote_observation(31337, Address::ZERO, None);
    assert_eq!(native.supported_kind(), Ok(ZeroSeedLaunchQuoteKind::Native));
    // Native is eligible on any chain; launch support still requires the supported instance.
    assert_eq!(
        quote_observation(8453, Address::ZERO, None).supported_kind(),
        Ok(ZeroSeedLaunchQuoteKind::Native)
    );
    let local = pinned_erc20_quote();
    assert_eq!(
        local.supported_kind(),
        Ok(ZeroSeedLaunchQuoteKind::Erc20 {
            quote_runtime: local.quote_runtime.unwrap()
        })
    );
    for (observation, expected) in [
        // The live list is empty: the same address and runtime elsewhere is not reviewed.
        (
            ZeroSeedLaunchQuoteObservation {
                chain_id: 8453,
                ..local
            },
            E::QuoteNotReviewed,
        ),
        (
            ZeroSeedLaunchQuoteObservation {
                chain_id: 1,
                ..local
            },
            E::QuoteNotReviewed,
        ),
        (
            ZeroSeedLaunchQuoteObservation {
                quote_runtime: Some(U256::ZERO),
                ..local
            },
            E::QuoteNotReviewed,
        ),
        (
            ZeroSeedLaunchQuoteObservation {
                quote: address(QUOTE_LOW),
                ..local
            },
            E::QuoteNotReviewed,
        ),
        (
            ZeroSeedLaunchQuoteObservation {
                quote_runtime: None,
                ..local
            },
            E::UnsupportedQuoteToken,
        ),
        (
            ZeroSeedLaunchQuoteObservation {
                quote_runtime: local.quote_runtime,
                ..native
            },
            E::QuoteNotReviewed,
        ),
    ] {
        assert_eq!(
            observation.supported_kind(),
            Err(expected),
            "{observation:?}"
        );
    }
    assert_eq!(
        quote_observation(31337, address(QUOTE_LOW), None).validate_code(),
        Err(E::UnsupportedQuoteToken)
    );
    assert_eq!(native.validate_code(), Ok(()));
}

#[test]
fn manifest_and_local_producer_negative_controls() {
    let instance = pinned_instance();
    instance.validate().unwrap();
    let pins = pins();
    for launch in supported_launches() {
        let key = launch.key;
        let native = launch.quote.quote_runtime.is_none();

        // Each provenance component is essential, not merely an arbitrary caller allowlist.
        for i in 0..7 {
            let mut bad = instance;
            match i {
                0 => bad.chain_id = 8453,
                1 => bad.extension = Address::ZERO,
                2 => bad.extension_runtime = U256::ZERO,
                3 => bad.periphery = instance.extension,
                4 => bad.periphery_runtime = instance.extension_runtime,
                5 => bad.core = Address::ZERO,
                _ => bad.core_runtime = U256::ZERO,
            }
            assert_eq!(
                bad.validate(),
                Err(ZeroSeedLaunchParameterError::UnsupportedInstance),
                "component {i}"
            );
            assert!(
                EvmZeroSeedLaunchPool::new(key, launch.config, launch.state, &bad, &launch.quote)
                    .is_err()
            );
        }
        for template in [
            &pins["ZeroSeedLaunch"]["templateRuntime"],
            &pins["ZeroSeedLaunchPeriphery"]["templateRuntime"],
        ] {
            let mut bad = instance;
            bad.extension_runtime = U256::from_str(s(template, "zeroFilledKeccak")).unwrap();
            bad.periphery_runtime = bad.extension_runtime;
            assert!(
                bad.validate().is_err(),
                "zero-filled template is not executed provenance"
            );
        }

        for sink in [
            Address::ZERO,
            instance.core,
            instance.extension,
            instance.periphery,
            key.token0,
            key.token1,
        ] {
            assert_eq!(
                validate_claim_recipient(&instance, &key, sink),
                Err(ZeroSeedLaunchParameterError::InvalidRecipient)
            );
        }
        validate_claim_recipient(
            &instance,
            &key,
            address("0x0000000000000000000000000000000000000001"),
        )
        .unwrap();
        let mut foreign = key;
        foreign.config.extension = address("0x5100000000000000000000000000000000000000");
        assert_eq!(
            validate_claim_recipient(
                &instance,
                &foreign,
                address("0x0000000000000000000000000000000000000001")
            ),
            Err(ZeroSeedLaunchParameterError::UnsupportedInstance)
        );

        let mut parameters = ZeroSeedLaunchParameters {
            supply: launch.requested,
            quote_token: launch.config.quote_token,
            range: launch.config.range,
            fee: launch.config.fee,
        };
        parameters.fee.trading_start = 301;
        let mut context = ZeroSeedLaunchLocalPreview {
            instance: &instance,
            owner: address("0x70997970C51812dc3A010C7d01b50e0d17dc79C8"),
            salt: B256::from(U256::from(7).to_be_bytes::<32>()),
            name: "éééééééééééééééa",
            symbol: "ZERO",
            decimals: 18,
            quote_runtime: launch.quote.quote_runtime,
            predicted_token_has_code: false,
            build_time: 1,
            execution_expiry: 301,
        };
        assert_eq!(context.name.len(), 31);
        assert_eq!(context.quote(&parameters), launch.quote);
        assert_eq!(
            context.predicted_token() < parameters.quote_token,
            !parameters.range.launch_token_is_token1
        );
        let preview = preview_installation(&parameters, 1, &context).unwrap();
        assert_eq!(preview, context.contract_preview(&parameters, 1).unwrap());
        assert_eq!(preview, installation_math(&parameters, 1).unwrap());
        // The requested supply is submitted unchanged: the preview never rewrites it.
        assert_eq!(parameters.supply, launch.requested);
        assert_eq!(
            preview.installed_supply + preview.sink_supply,
            parameters.supply
        );
        assert_eq!(preview.liquidity, launch.config.liquidity);

        let mut flipped = parameters;
        flipped.range.launch_token_is_token1 = !flipped.range.launch_token_is_token1;
        assert_eq!(
            context.validate(&flipped, 1),
            Err(ZeroSeedLaunchParameterError::TokenOrderMismatch)
        );

        // Quote observations: a nonzero quote without code is the contract's refusal; an
        // unreviewed runtime is the SDK's.
        if !native {
            context.quote_runtime = None;
            assert_eq!(
                preview_installation(&parameters, 1, &context),
                Err(ZeroSeedLaunchParameterError::UnsupportedQuoteToken)
            );
            assert_eq!(
                context.contract_preview(&parameters, 1),
                Err(ZeroSeedLaunchParameterError::UnsupportedQuoteToken)
            );
            context.quote_runtime = Some(U256::from(1));
            assert_eq!(
                preview_installation(&parameters, 1, &context),
                Err(ZeroSeedLaunchParameterError::QuoteNotReviewed)
            );
            assert_eq!(context.contract_preview(&parameters, 1), Ok(preview));
            context.quote_runtime = launch.quote.quote_runtime;
        }

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

/// Every function selector, event topic and error selector of the consumer manifest (91) is
/// recomputed from the pinned ABI files, and each ABI file is byte-for-byte the manifest's
/// canonical JSON (`jq -cS .abi`, no trailing newline).
#[test]
fn pinned_abis_match_the_consumer_manifest() {
    let pins = pins();
    let manifest = &pins["consumerManifest"];
    assert_eq!(s(manifest, "frozenCommit"), TARGET_COMMIT);
    assert_eq!(
        s(&pins, "source"),
        format!("EkuboProtocol/evm-contracts@{TARGET_COMMIT}")
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
        let expected = &manifest["abi"][name];
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
    assert_eq!(entries, 91);
    let tuple = "(string,string,uint8,uint128,address,int32,int32,uint32,uint64,uint32,uint64,uint64,bytes32)";
    let launch = &manifest["abi"]["ZeroSeedLaunch"];
    let periphery = &manifest["abi"]["ZeroSeedLaunchPeriphery"];
    assert_eq!(
        periphery["functions"][format!("create({tuple})")].as_str(),
        Some("0x662af306")
    );
    for table in [launch, periphery] {
        assert_eq!(
            table["functions"][format!("previewInstallation(address,{tuple})")].as_str(),
            Some("0x917c1163")
        );
    }
    // Removed at the target: the constructor quote getter, the supply binding error and the
    // creator-fee ceiling error `FeeTooHigh()` (0xcd4e6167), which no ABI file still declares.
    assert!(launch["functions"].get("quoteToken()").is_none());
    assert_eq!(
        manifest["removedFromAbi"],
        serde_json::json!({ "FeeTooHigh()": "0xcd4e6167" })
    );
    assert_eq!(
        format!("0x{}", hex::encode(&keccak256("FeeTooHigh()")[..4])),
        "0xcd4e6167"
    );
    for abi in [ABI_LAUNCH, ABI_PERIPHERY, ABI_TOKEN] {
        assert!(!abi.contains("FeeTooHigh"));
    }
    assert_eq!(
        s(manifest, "maxCreatorFeeQ64"),
        ZERO_SEED_LAUNCH_MAX_CREATOR_FEE.to_string()
    );
    assert_eq!(
        launch["errors"]["InvalidFeeSchedule()"].as_str(),
        Some("0xf75a271a")
    );
    assert!(
        !launch["errors"]
            .as_object()
            .unwrap()
            .keys()
            .any(|k| k.starts_with("SupplyNotExactlyInstallable"))
    );
    assert_eq!(
        s(&manifest["structs"], "LaunchParameters"),
        "(string name,string symbol,uint8 decimals,uint128 supply,address quoteToken,int32 askTick,int32 upperTick,uint32 tickSpacing,uint64 tradingStart,uint32 feeDuration,uint64 initialFee,uint64 finalFee,bytes32 salt)"
    );
    for (topic, signature) in [
        (LAUNCH_CREATED, "LaunchCreated"),
        (LAUNCH_SWAPPED, "LaunchSwapped"),
        (CREATOR_FEES_CLAIMED, "CreatorFeesClaimed"),
    ] {
        let found = launch["events"]
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
        let found = periphery["events"]
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

    // The SDK's compiled-in pins are exactly the pinned local fixture: one instance without a
    // quote, and one reviewed local ERC-20 quote.
    let fixture = &pins["localFixture"];
    assert!(fixture.get("quote").is_none());
    assert_eq!(s(fixture, "coreRuntimeKeccak"), CORE_RUNTIME);
    assert_eq!(
        s(fixture, "extensionConstructorArguments"),
        format!("0x{}{}", "0".repeat(24), &s(fixture, "core")[2..])
    );
    pinned_instance().validate().unwrap();
    let quotes = pins["localQuotes"].as_array().unwrap();
    assert_eq!(quotes.len(), 1);
    assert!(pinned_erc20_quote().supported_kind().is_ok());
}
