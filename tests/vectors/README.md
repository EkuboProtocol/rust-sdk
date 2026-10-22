# Zero-seed launch conformance (LOCAL evidence only)

Target: `EkuboProtocol/evm-contracts@550afc40280423128c02eb5ffd213aa959b34e2a`, tree
`dbbfe6a5eb5ddefe04974338b2b57bdf675c431e` (forward-only `ZeroSeedLaunch` with a per-launch
quote, requested supply with an `address(0)` sink, fixed-base fee table, the full `uint64`
creator-fee range, separate `ZeroSeedLaunchPeriphery`). Q0.64 Core/raw tick spacing, zero Core fee, separate creator fee.
Not Q0.16 `next`. Nothing here is deployed, audited or approved: there are no live instances, no
live reviewed quotes, and release is on HOLD.

## Interface at the target

- Extension constructor `(ICore core)`; periphery `(ICore core, IZeroSeedLaunch launch)`. There is
  no quote immutable and no `quoteToken()` getter: one extension and one periphery serve every
  quote.
- `LaunchParameters = (name, symbol, decimals, supply, quoteToken, askTick, upperTick,
  tickSpacing, tradingStart, feeDuration, initialFee, finalFee, salt)`. `quoteToken` is the
  launch's own quote and the non-launch token of its pool key (`ZeroSeedLaunchParameters` and
  `ZeroSeedLaunchConfig` carry it as `quote_token`). Liquidity is not an input.
- Creator fees: every `uint64` initial and final fee, `0..=2**64 - 1`, is valid; `_validate`
  checks only `finalFee <= initialFee` and `feeDuration > 0` (`InvalidFeeSchedule`,
  `0xf75a271a`). `FeeTooHigh()` (`0xcd4e6167`) is gone from the interface and the ABI, and so is
  the SDK's `ZeroSeedLaunchParameterError::FeeTooHigh` variant (a breaking change of that public
  enum for exhaustive matches); `ZERO_SEED_LAUNCH_MAX_CREATOR_FEE` is now `u64::MAX`, just under
  100%, never exactly 100%. `2**64` (100%) is not a `uint64`: the contract fails ABI decoding with
  empty revert data, and the SDK's `u64` fields refuse it when parsing, without truncating or
  wrapping. `new` and `new_math` accept every rate too.
- Selectors and topics: periphery `create 0x662af306`, `previewInstallation 0x917c1163`
  (extension and periphery), `LaunchCreated 0x3a4e8111...098f`, all unchanged from `40af6cb`.
  `SupplyNotExactlyInstallable` and `FeeTooHigh` are gone. Swap and claim forward payloads, pool
  config, pool id, the `Installation` struct, `LaunchSwapped`, `CreatorFeesClaimed`, the periphery's claim/transfer/owner functions and
  events, and the `MintableERC20` ABI and creation code are unchanged.
- Native ETH is `address(0)`: always token0, so the launch token is token1. It has no code, no
  `decimals()`, no approvals and no runtime hash. An ERC-20 quote above the launch token (the
  fixtures use the top of the address space) makes the launch token token0. Preview and creation
  refuse a nonzero quote without code (`UnsupportedQuoteToken`) and screen nothing else.
- Creation, fee claims and swaps all arrive through `Core.forward`. Swaps forward
  `abi.encode(PoolKey, SwapParameters)` from any locker (the parity test locker or
  `test/LaunchTestRouter.sol`). The forwarding locker of a creation is the launch `controller`;
  for `ZeroSeedLaunchPeriphery` it records the transferable owner (`LaunchOwnerChanged`) and pays
  claims (`LaunchFeesClaimed`, right after the extension's `CreatorFeesClaimed` with identical
  amounts: one claim, never counted twice).
- Token address: `CREATE2(extension, keccak256(abi.encode(controller, salt)),
  keccak256(MintableERC20.creationCode ++ abi.encode(extension, name, symbol, decimals)))`; through
  the periphery `salt = keccak256(abi.encode(owner, userSalt))` and `controller = periphery`. It
  does not depend on the quote, so the same owner, salt and metadata with another quote collide
  (`LaunchTokenExists`). The SDK computes all three (`periphery_launch_salt`,
  `extension_token_salt`, `launch_token_address`/`periphery_launch_token_address`) with the
  embedded `MintableERC20` creation code (keccak `0x25da7fd3...2f52`).
- Claim recipients refused by the periphery (`InvalidRecipient`): zero, Core, the extension, the
  periphery, token0, token1. `validate_claim_recipient` mirrors all six.

## Supply

All amounts are raw base-unit integers (decimal strings in JSON).

- requested supply: `LaunchParameters.supply` as submitted, `ZeroSeedLaunchParameters.supply`. It
  is the token's `totalSupply` and `LaunchCreated.parameters.supply`. Producers submit it
  unchanged; it is never rewritten to the installed supply.
- installed supply: `Installation.installedSupply`, `ZeroSeedLaunchInstallation.installed_supply`:
  the launch-token amount Core takes, rounded up, for the largest liquidity the requested supply
  buys (`LaunchCreated.liquidity`); `0 < installed <= requested`, all inside the position. Not in
  `LaunchCreated`; it is the token side of Core's `PositionUpdated` of the creation.
- sink supply: `requested - installed`, `ZeroSeedLaunchInstallation.sink_supply`, minted directly
  to `address(0)`. Never spendable and not an ERC-20 burn.

`preview_installation_math` mirrors `previewInstallation`; `installation_math` is what `create`
installs, which is the same calculation on the same inputs. For 1,000,000,000 tokens at 18
decimals the sink is 790 (token0) or 578 (token1, native) base units at 18/18, and 697,343,214 or
717,714,600 at 18/6.

## Fee schedule

`decay_q128(t)` is 0 for `t >= 131072`; otherwise start at `2**128` and, for each set bit `i` of
`t` in ascending order, `r = floor(r * TABLE[i] / 2**128)`, with the 17 constants
`TABLE[i] = round(2**128 * 2**(-2**i / 600))` (600 s half-life). Then

```
fee_at(t) = initial                                                    t <= trading_start
          = final + floor((initial - final) * (decay(e) - decay(D)) / (2**128 - decay(D)))   0 < e < D
          = final                                                      e >= D   (e = t - trading_start)
```

with 256-bit intermediates (`r * TABLE < 2**256`, numerator `< 2**192`, also at
`initial = 2**64 - 1`). There is no ceiling below the type: the highest rate is `2**64 - 1`. At it
an exact input nets `floor(gross / 2**64)` and an exact output pays `calc * 2**64`, which fits
`int128` up to `calc = 2**63 - 1`; above that the SDK returns `Overflow` (the contract's
`SafeCastLib.Overflow`) and from `calc = 2**64` `AmountBeforeFeeOverflow`. The canonical example
is 50% -> 0.3% over 3,600 s; 99% (`18262276632972456099`) remains only a study rate.

## Vectors (SHA-256)

| file | sha256 | source |
|---|---|---|
| `zero-seed-launch.json` | `4689b2cdfb533bb293dc2fda4f76189da5dc5f5c8e79a33bf5b216149bdc00b9` | the contract's `test/vectors/zero-seed-launch.json` (v5: `creator_fee_range`, `max_rate`), verbatim |
| `zero-seed-launch-fee-curve-all-seconds.json` | `fc9be5e4d59d8163f7a5566a7076bb9628d8ff30af5efde1eb554ba9b93bddce` | protocol generator's 250-digit `Decimal` output, every second of 12 curves, 25,212 `[initial, final, duration, elapsed, fee]` rows (delivered gzipped, gz sha256 `b1f5ff563c58869fd6667977614c89c30ea0b27353ecac40752fb24736951900`; stored decompressed so tests need no extra dependency) |
| `zero-seed-launch-fee-decay-vectors.json` | `7004b29f91540f1b29a568b525d215227565b36d1b490687ae604f5f145b835b` | `gen-fee-decay-table.py --json`: table, decay samples, 200 fee rows, digests (byte-identical at the target: its `max` is `2**64 - 1` and its `99` the same study rate as before) |
| `zero-seed-launch-fee-curve-rows.json` | `2b716bc9278b4cccaf3382f3624a16913cddf327e4a625c241bc219edc359f60` | the executed `VEC|` rows of `ZeroSeedLaunchFeeCurve.t.sol`: 100 `highRate` (identical to the previous target's, the `max` launches now created normally), 12 `createMax`, 2 `exactOutBounds` |
| `zero-seed-launch-parity.json` | `89db5c64817daad560c500e7c20b3e1f54477df8e8dfb47a39cb7d3e479f6b30` | `generator/ZeroSeedLaunchSdkParity.t.sol` |
| `zero-seed-launch-indexer.json` | `09d7745740af507a02304e26c0e20d6f27b1047fd707c056ef4d936c67a74fcc` | indexer `scripts/zeroSeedLaunchFixture.ts` LOCAL anvil receipt at this target, verbatim: one instance, three native and three ERC-20 launches (two of them created at `2**64 - 1`), swaps through `LaunchTestRouter` |
| `pins/pins.json` | `65be02a5c89195db32584e6a05cc105d63f988f5f3d16a5b8df0c516207c37f2` | `generator/pins_from_artifacts.py` |
| `pins/*.abi.json` | `efae9388...e41e`, `df24d9f0...7305`, `fa77fe07...abba` | canonical ABIs of `ZeroSeedLaunch`, `ZeroSeedLaunchPeriphery`, `MintableERC20` (only the first changed: `FeeTooHigh` removed) |

The consumer manifest is `zero-seed-interface-550afc4.json` (file sha256
`57d8485ee7aa34049269f66bedccbfb43b66869b2e37bddf5857d070df02ca0b`, its own `manifest_sha256`
`032f3c9bfe191f5bb074d1926f4c265af9e06e939140ca13edbd9181e0b2deed`), generated from the target's
compiled artifacts; its tables, `fee.max_creator_fee_q64`, `creator_fee_range` and
`removed_from_abi` are copied into `pins.json` under `consumerManifest`.

`check_vector_log.py` binds every emitted row of `ZeroSeedLaunch.t.sol` to the vectors. The
contract's v5 vectors still carry the `gas.create` values measured before the ceiling comparison
was removed (`1367815`/`1327004`); the target executes creation 34 gas cheaper
(`1367781`/`1326970`). The script tolerates exactly those two pairs and nothing else; the SDK
does not use the frozen gas rows.

What the tests check:

- `fee_curve_tests.rs` (unit): the table equals both the contract's and the generator's;
  `decay_q128(2**i) = TABLE[i]`; bit 0 equals the contract's conditional subtraction; zero cutoff
  without aliasing; monotone over all of `[0, 131072]`, first zero at 76,800 s; EVERY one of the
  25,212 oracle rows equals `decayed_fee` and `fee_at`; the 12 SHA-256 chains
  (`h = sha256(h || fee as 8-byte big-endian)`, `t = 0..D`, `h0 = 0^32`) recomputed from the oracle
  and from the SDK equal the contract's pins (and the generator's 10); the 200 generator rows and
  the contract's 18 `fee` rows; the contract's pinned deviation from the previous variable-base
  schedule (32/82/120/133/133 Q64 units); the 100 executed high-rate swap rows (50/75/90/99/max%,
  plain ERC-20 and native orders, 18/6); the contract's 16 `max_rate` trades (equal to the
  study's `max` rows) and the 12 `createMax` first buys (max -> 0.3%/3,600 s, flat max/1 s,
  max -> 0/`u32::MAX` s); the two `exact_output_bounds` vectors (equal to the study's rows),
  probed exactly: last valid output `calc = 2**63 - 1` paying `calc * 2**64`, the first and last
  output of `[2**63, 2**64 - 1]` -> `Overflow`, the next -> `AmountBeforeFeeOverflow`. Validation,
  `preview_installation_math` and `new_math` accept 0, 1, `2**64 - 2` and `2**64 - 1` as initial
  and final fee over 1 s, 3,600 s and `u32::MAX` s and refuse only a rising schedule or a zero
  duration. Every launch at `2**64 - 1` is built through `new_math`, never by overwriting state.
- `tests/zero_seed_launch_vectors.rs`:
  - `creator_fee_range`: the 12 verdict vectors (6 accept, 4 `InvalidFeeSchedule`, 2
    `abi_decoding_failure`, whose `2**64` and dirty-high-bits values fail `u64` parsing and
    serde deserialization instead of wrapping) and both reference schedules;
  - frozen contract vectors: fee rows, the four installations of the requested 1e27 supply
    (installed, liquidity, bounds and the 790/578/697,343,214/717,714,600 sinks), trades,
    residues, the test router's 1e18 buys and the dust buy;
  - parity: 13 scenarios, 522 step slots, all byte-identical to the previous target's (only
    the code hashes in each `create` changed). Eleven are the earlier programs (plain
    ERC-20 token0 and native token1 at 18/18 over 3,600 s and 600 s, 6-decimal quotes in both
    orders, 50% -> 0.3% over 3,600 s in both orders, 99% (a study rate) over 600 s, a
    near-max-tick overflow launch). Two more
    create a native-quote and an ERC-20-quote launch on ONE extension and periphery and trade them
    alternately through `LaunchTestRouter` and the test locker. Every successful step compares SDK
    deltas, fee amount and side, the `LaunchSwapped` rate, the ledger change, Core and holder
    balances (native ETH by value) and chained post-state; reverts map to SDK errors; partial
    fills at the upper bound, no-bid sells and zero fills are explicit; each periphery claim equals
    the SDK fee sum, its return value and both claim events. Every creation records requested,
    installed and sink supply, `totalSupply == requested`, `balanceOf(address(0)) == sink`, the
    sink `Transfer` and the Core `PositionUpdated` token delta `== installed` (asserted in the
    generator and again in the tests);
  - 129 periphery previews, each followed by `create` with the same requested supply (56
    succeed; the former ceiling plus one, max -> max and max -> 0.3% are accepted in all four
    groups, and nothing is refused for its rate): the SDK's
    `ZeroSeedLaunchLocalPreview::contract_preview` reproduces every result and refusal (including
    `UnsupportedQuoteToken` for a codeless quote, `MetadataTooLong`, `LaunchTokenExists` for a
    collision and for the same salt with another quote, `ZeroLiquidity`, `LiquidityAboveTickCap`),
    the predicted token, and every creation installs exactly its preview;
  - the supported instance serves the native and the ERC-20 launch, and every instance, quote
    observation, pool key, claim recipient, metadata, collision, token order and timing control
    fails closed;
  - the 91 manifest selectors, topics and errors recomputed from the pinned ABI files, whose bytes
    hash to the manifest's ABI sha256 (`jq -cS .abi`, no trailing newline); `FeeTooHigh` appears
    only under `removedFromAbi`;
  - indexer receipt: one instance with no quote, equal to the compiled-in pin (addresses,
    salts, executed runtimes, template runtimes, creation code and ABI hashes); every
    `LaunchCreated` decoded from raw log data with its per-launch quote, pool key
    `sorted(token, quote)`, owner of record, extension salt and the CREATE2 token prediction;
    requested, installed and sink supply against the SDK installation of the requested supply,
    the returned `Installation`, Core's `PositionUpdated` of the creation (launch-token delta ==
    installed, quote delta 0, liquidity delta == computed liquidity), the mints to Core and to
    `address(0)`, `totalSupply` and the sink balance; all six launches (three native, three
    ERC-20, one extension) quote through supported `new` and refuse each other's quote; all 26
    swaps replayed against `LaunchSwapped` and the Core swap log, 10 claims against the extension
    ledger (accrued from `LaunchSwapped`, claimed from `CreatorFeesClaimed` only, payouts equal and
    never added again), owner transfers, and all 62 snapshots (`Core` state, `creatorFees`, owner,
    controller, `feeAt(block time)`, `totalSupply`, sink balance), across the prefix and both
    reorg branches, with per-launch counts. `l5` (native, `2**64 - 1` -> 0.3% over 3,600 s) and
    `l6` (ERC-20, flat `2**64 - 1`, 1 s) are created normally at the highest rate: their four
    swaps at it (1e18 exact in -> 54,160 tokens; 1e10 tokens exact out -> `10019 * 2**64` paid)
    satisfy `net = floor(gross / 2**64)` and `paid = calc * 2**64`; `l5` also trades while
    decaying and at its final rate, and both claim.
- `pins/pins.json` (`generator/pins_from_artifacts.py`): per contract ABI hash, selectors, topics,
  errors, zero-filled runtime and creation keccak, all asserted equal to the consumer manifest;
  the local fixture (`localFixture`) recomputed from the artifacts: the extension at the first
  CREATE2 salt of the deterministic deployer whose address carries the call-point byte `0x51`, the
  periphery at salt 0, init-code keccaks, and the unique immutable assignment that turns each
  template runtime into the executed runtime (extension: `core`, `core`; periphery: `core`,
  `extension`, `core`); and the one reviewed LOCAL ERC-20 quote (`localQuotes`, the plain
  18-decimal `test/TestToken.sol` at the top of the address space). The script cross-checks both
  against the indexer receipt.

## Supported surface versus arithmetic

`ZeroSeedLaunchPool::new` requires a `ZeroSeedLaunchInstance` observation matching the one LOCAL
fixture instance (chain 31337, Core `0x00000000000014aa86c5d3c41765bb24e11bd701`, runtime
`0xc5f90c9d...c71a`; extension `0x511b4327c2a2b6fd803b4ae85f2f9d831e046d8b`, runtime
`0xb8c6d15f...a858`; periphery `0x2f0be2fc5a2825cecd23dbf6ed33ed8ff823ef64`, runtime
`0x49988478...999e`) and a `ZeroSeedLaunchQuoteObservation` of the launch's own quote that
`supported_kind` accepts:

| quote | supported |
|---|---|
| native ETH, `address(0)`, no code | always |
| nonzero, no code | never: the contract's `UnsupportedQuoteToken` |
| ERC-20 | only with a reviewed `(chain, address, runtime keccak)` entry: live list EMPTY; LOCAL `(31337, 0xffff...ffff, 0xe8ccd7c4...3e63)` only, otherwise `QuoteNotReviewed` |

Chain, extension and its runtime, periphery and its runtime, Core and its runtime are all
essential; the quote is checked per launch. These are caller-provided observations, NOT
cryptographic proof, RPC reads or a live attestation. The Foundry parity instance runs the same
extension runtime at another address and is refused, as are its harness ERC-20 quotes.

`new_math`, `preview_installation_math`, `installation_math` and `fee_at` are pure arithmetic,
not service support, calldata or plan production. `ZeroSeedLaunchLocalPreview::contract_preview`
adds the contract's quote-code, metadata and collision checks for any observed instance.
`preview_installation` also requires the supported instance, quote support and the LOCAL timing
rule `build_time+300 <= start <= build_time+86400`, `build_time < expiry <= start`, re-checked
with fresh time, with owner, user salt, metadata (31 UTF-8 bytes each) and decimals fixing the
predicted token and so the token order against the launch's quote (`TokenOrderMismatch`). Submit
the requested supply unchanged; the returned installation is for display.

## Gas

SDK gas constants are unchanged UNCALIBRATED estimates. Against the regenerated parity vectors the
error on the 370 test-locker fills that are neither a launch's first fill nor a known zero-slot
write is -39.5% to +26.8% (mean +1.5%); cold slots, first swaps, routers, calldata, transaction
base and UserOp costs are not predicted.

## Reproduce

```sh
cp -a <evm-contracts at 550afc4, built> <scratch>          # never edit the source checkout
cp <scratch>/test/vectors/zero-seed-launch.json tests/vectors/   # verbatim
cp tests/vectors/generator/ZeroSeedLaunchSdkParity.t.sol tests/vectors/generator/ZeroSeedLaunchLocalFixturePins.t.sol \
  <scratch>/test/extensions/
(cd <scratch> && forge test --offline --match-contract ZeroSeedLaunchSdkParity -vv) > <parity-log>
python3 tests/vectors/generator/parity_to_json.py < <parity-log> > tests/vectors/zero-seed-launch-parity.json
(cd <scratch> && forge test --offline --match-path test/extensions/ZeroSeedLaunchFeeCurve.t.sol -vv) \
  | python3 tests/vectors/generator/fee_curve_rows_to_json.py 550afc40280423128c02eb5ffd213aa959b34e2a \
  > tests/vectors/zero-seed-launch-fee-curve-rows.json
(cd <scratch> && forge test --offline --match-path test/extensions/ZeroSeedLaunch.t.sol -vv) > <main-log>
python3 tests/vectors/generator/check_vector_log.py tests/vectors/zero-seed-launch.json <main-log>
python3 <scratch>/test/vectors/gen-fee-decay-table.py --json <decay-json>
cmp <decay-json> tests/vectors/zero-seed-launch-fee-decay-vectors.json
cp <indexer>/tests/fixtures/zero-seed-launch/local-chain.json tests/vectors/zero-seed-launch-indexer.json   # verbatim
(cd <scratch> && forge test --offline --match-contract ZeroSeedLaunchLocalFixturePins -vv) > <pin-log>
python3 tests/vectors/generator/pins_from_artifacts.py <scratch> <consumer-manifest.json> <pin-log>
python3 tests/vectors/generator/verify_pins.py
cargo test --features evm,starknet,serde
python3 tests/vectors/generator/mutants.py
```

Known-safe SDK rollback is `main` (no launch support). NOT PROVEN: any live instance, network
registration or deployment, any live ERC-20 quote review, downstream preview/decoder/owner
enforcement, whole-stack QA, external audit, fee-parameter selection or release authorization.
