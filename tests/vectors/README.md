# Zero-seed launch conformance (LOCAL evidence only)

Target: `EkuboProtocol/evm-contracts@43d6628841b3ce91dafa048b7ceef64bed55fc8e`, tree
`9ab869d1a453b8df48d47c2e0e2fb2d4ca8f67bf` (forward-only `ZeroSeedLaunch` with a per-launch
quote, requested supply with an `address(0)` sink, the exact token0 installation, fixed-base fee
table, the full `uint64` creator-fee range, separate `ZeroSeedLaunchPeriphery`). Q0.64 Core/raw tick spacing, zero Core fee, separate creator fee.
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

Installed liquidity is the largest `L` whose rounded-up debit fits the requested supply `S`:

- token1 (native quote): `floor(S * 2**128 / (upper - lower))`, the exact inverse of
  `ceil(L * (upper - lower) / 2**128)`; unchanged.
- token0 (ERC-20 quote above the launch token): `floor(S * lower * upper / (2**128 * (upper -
  lower)))` over the fixed sqrt ratios. Core takes `ceil(ceil(L * 2**128 * (upper - lower) / upper)
  / lower)`, and `ceil(ceil(n / u) / l) = ceil(n / (u * l))`, so `debit(L) <= S` exactly when `L`
  is at most that floor. The SDK computes the product directly in 512 bits (below `2**511`); the
  contract factors the compact ratios instead; both give the same integer. Since `43d6628` this
  replaces the shared `maxLiquidityForToken0` helper, which floored `lower * upper / 2**128`
  first: at ticks `-88080384..-85983232` (spacing 524288) and `S = 1e30` it installed
  106,052,588,672 instead of 115,073,586,432 and sank about 7.84% of `S` instead of
  8,589,236,567,713,153,558 raw units (about `8.6e-12` of `S`).

Both saturate at `2**128 - 1`; zero liquidity refuses `ZeroLiquidity` and liquidity above the
per-tick cap refuses `LiquidityAboveTickCap(liquidity, cap)`, never capped. The sink is the
remainder for the maximal integer liquidity; how much quote that remainder could have bought
depends on the geometry and the quote's units, so no general bound in quote value is claimed.

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
| `zero-seed-launch.json` | `8398d4189a6b1a434e17376276a7e218c9597408754a9920ce34a4872809a879` | the contract's `test/vectors/zero-seed-launch.json` (v6: adds `installation`, measured creation gas), verbatim |
| `zero-seed-launch-installation.json` | `b06f6576e2280fa9851835655e899d3a21506bec317fa51af2d5a2efadbf330d` | the contract's `test/vectors/zero-seed-launch-installation.json`, verbatim: 41 rows from an independent integer oracle (exact tick table, Core's rounded debits, direct inverse and binary search), with the previous helper's liquidity, runtime/init-code pins and measured creation gas |
| `zero-seed-launch-fee-curve-all-seconds.json` | `fc9be5e4d59d8163f7a5566a7076bb9628d8ff30af5efde1eb554ba9b93bddce` | protocol generator's 250-digit `Decimal` output, every second of 12 curves, 25,212 `[initial, final, duration, elapsed, fee]` rows (delivered gzipped, gz sha256 `b1f5ff563c58869fd6667977614c89c30ea0b27353ecac40752fb24736951900`; stored decompressed so tests need no extra dependency) |
| `zero-seed-launch-fee-decay-vectors.json` | `7004b29f91540f1b29a568b525d215227565b36d1b490687ae604f5f145b835b` | `gen-fee-decay-table.py --json`: table, decay samples, 200 fee rows, digests (byte-identical at the target: its `max` is `2**64 - 1` and its `99` the same study rate as before) |
| `zero-seed-launch-fee-curve-rows.json` | `7a86930ae16e5f8cc6730f33bc6f71915f5d3c1375fd7788593153de03b16d81` | the executed `VEC|` rows of `ZeroSeedLaunchFeeCurve.t.sol`: 100 `highRate` (identical to the previous target's, the `max` launches now created normally), 12 `createMax`, 2 `exactOutBounds` |
| `zero-seed-launch-parity.json` | `e799f4de8bbaf8653cc938b7d8f6b3552b5f0b3fcfdc2623b38996787a479cb0` | `generator/ZeroSeedLaunchSdkParity.t.sol` |
| `zero-seed-launch-indexer.json` | `ec308953b8412e3ad76e7b6bf74b1e3ae56f6cbe0798032dbc6673bfedfae7d9` | indexer `scripts/zeroSeedLaunchFixture.ts` LOCAL anvil receipt at this target, verbatim: one instance, three native and five ERC-20 launches (two created at `2**64 - 1`, two at low-price token0 geometry), swaps through `LaunchTestRouter` |
| `pins/pins.json` | `a2de05ae1bc5fc640fda4cf2930c8ba1e85c7cab5023db67dc6351408d97ec14` | `generator/pins_from_artifacts.py` |
| `pins/*.abi.json` | `efae9388...e41e`, `df24d9f0...7305`, `fa77fe07...abba` | canonical ABIs of `ZeroSeedLaunch`, `ZeroSeedLaunchPeriphery`, `MintableERC20`, unchanged since `550afc4` |

The consumer manifest is `zero-seed-interface-43d6628.json` (file sha256
`7e351ef4fe1ee835f41870cbbab69a07d26b0a66ffebd5915ef4a42a18edcc6e`, its own `manifest_sha256`
`6be8bd0a5a54f6dd51f9f7836bd4d64922672deebff7e19a6ff821e318906629`), generated from the target's
compiled artifacts; its tables, `fee.max_creator_fee_q64`, `creator_fee_range` and
`removed_from_abi` are copied into `pins.json` under `consumerManifest`. Against `550afc4` only
the extension's runtime and creation code (20,125 -> 20,402 runtime bytes) and the periphery's
metadata hash changed, and with them the local instance's addresses and runtimes.

`check_vector_log.py` binds every emitted row of `ZeroSeedLaunch.t.sol` to the vectors exactly,
gas included: the v6 vectors carry the measured creation gas, so the former tolerance for two
stale `gas.create` values is gone. The SDK does not use the gas rows.

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
  - `tests/zero_seed_launch_installation.rs`: all 41 protocol installation rows (bounds, fixed
    sqrt ratios, tick cap, liquidity, installed and sink supply, refusals, Core's debit one unit
    above, and the previous helper's value for token0); the original vector and both
    counterexamples spelled out (1e30: 115,073,586,432 not 106,052,588,672; 17,380,183,081,064,167,375:
    2 not 1, no sink; the int128-scale full-width budget: 9,223,595,582,101,085,260, no sink); and
    6,000 deterministic cases over aligned ranges of both orders, every spacing class, compact-ratio
    region transitions, both tick-range ends, and supplies from 1 to `int128.max` including exact
    debit boundaries `debit(L)` and `debit(L) - 1`, each checked against a binary search on Core's
    own rounded debit (`debit(L) <= S < debit(L + 1)`, or the refusal it implies). The previous
    helper under-installs in hundreds of those cases, so the property detects the early floor;
  - 145 periphery previews, each followed by `create` with the same requested supply (68
    succeed; the former ceiling plus one, max -> max and max -> 0.3% are accepted in all four
    groups, and nothing is refused for its rate): the SDK's
    `ZeroSeedLaunchLocalPreview::contract_preview` reproduces every result and refusal (including
    `UnsupportedQuoteToken` for a codeless quote, `MetadataTooLong`, `LaunchTokenExists` for a
    collision and for the same salt with another quote, `ZeroLiquidity`, `LiquidityAboveTickCap`),
    the predicted token, and every creation installs exactly its preview. Per order and decimals
    group they include the low-price geometry at `1e30`, at a supply worth exactly two liquidity
    units (installs all of it), one unit short (`ZeroLiquidity`), and an int128-scale supply over
    the full width at spacing 1;
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
    `address(0)`, `totalSupply` and the sink balance; all eight launches (three native, five
    ERC-20, one extension) quote through supported `new` and refuse each other's quote; all 28
    swaps replayed against `LaunchSwapped` and the Core swap log, 10 claims against the extension
    ledger (accrued from `LaunchSwapped`, claimed from `CreatorFeesClaimed` only, payouts equal and
    never added again), owner transfers, and all 78 snapshots (`Core` state, `creatorFees`, owner,
    controller, `feeAt(block time)`, `totalSupply`, sink balance), across the prefix and both
    reorg branches, with per-launch counts. `l5` (native, `2**64 - 1` -> 0.3% over 3,600 s) and
    `l6` (ERC-20, flat `2**64 - 1`, 1 s) are created normally at the highest rate: their four
    swaps at it (1e18 exact in -> 54,160 tokens; 1e10 tokens exact out -> `10019 * 2**64` paid)
    satisfy `net = floor(gross / 2**64)` and `paid = calc * 2**64`; `l5` also trades while
    decaying and at its final rate, and both claim. `l7` (`1e30` over ticks
    `-88080384..-85983232`, spacing 524288) and `l8` (an int128-scale supply over the full width
    at spacing 1, no sink mint) are ERC-20 token0 launches at the exact maximum liquidity, each
    with one exact-output buy.
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
`0xc5f90c9d...c71a`; extension `0x519c5f793d3f6cf9ee439e4cc38d8285cf08211f`, runtime
`0xd6b4c7ce...8ed5`; periphery `0x0df4e2a76640b52e51479b435f52d0eb0e7e8ef4`, runtime
`0x2a9329db...974b`) and a `ZeroSeedLaunchQuoteObservation` of the launch's own quote that
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

## Second fee model: tick-rate decay (`evm-contracts@3d6378f`)

`EkuboProtocol/evm-contracts@3d6378f585591dc7eabeea6976932c30524bb8ea` (tree
`a8944891df9a814523bb29d3f8a4713318ccfd60`) replaces `uint32 feeDuration` with `uint64
decayRateX32` (unsigned Q32.32 ticks per second) in the same position of `LaunchParameters` and
`Launch`. Everything else above is unchanged. The fee model is a property of the deployment
(`ZeroSeedLaunchInstance::fee_model`), never inferred from an event: a deployment of `43d6628`
keeps `FixedBaseDurationV1` and its table math, a deployment of `3d6378f` uses `TickRateV2`.
Parameters or launches of the other model are refused (`FeeModelMismatch`).

- Fee after `tradingStart`: rate 0 is `initialFee`; `elapsed > MAX_DECAY_PRODUCT / rate`
  (`381061679028371455`, integer division first) is `finalFee`; otherwise
  `m = (rate * elapsed) >> 32` and `finalFee + ((initialFee - finalFee) * toFixed(tickToSqrtRatio(-m))) >> 128`
  (`tick_rate_decayed_fee`, using the SDK's EVM `to_sqrt_ratio`). `finalFee` is the long-run
  floor, reached only by rounding or by saturation; there is no fee end.
- Validation: only `finalFee <= initialFee`. Every `uint64` rate is valid, including 0.
- Selectors/topics: `create 0xf91810d2`, `previewInstallation 0xb665ec4d`, `LaunchCreated
  0x8f81ce1b...5888`. Executed runtimes: extension `0xe08ad382...dfc3`, periphery `0xfa8ef7df...0444`
  (asserted in every parity scenario).
- Half-life of the excess: `decay_rate_x32_for_half_life(H) = floor(HALF_LIFE_X32_E30 / (H * 10**30))`
  with the normative integer `ZERO_SEED_LAUNCH_HALF_LIFE_X32_E30 = 5954091920683119788732747343471285361579197626`;
  one day is `68913100933` (`ZERO_SEED_LAUNCH_DEFAULT_DECAY_RATE_X32`). `half_life_micros` and
  `saturation_elapsed_seconds` are display values.

Vectors in `tests/vectors/v2/`, checked by `tests/zero_seed_launch_tick_rate.rs`:

- `zero-seed-launch.json`: the contract's frozen vectors v7 verbatim (sha256 `4c1245ca...66605`):
  40 fee rows, the five curve tables, tick steps, saturation seconds, five SHA-256 chains pinned by
  the contract tests and the independent Python oracle, and the 13 fee-range verdicts.
- `zero-seed-launch-parity.json`: `ZeroSeedLaunchSdkParityV2.t.sol` executed on the frozen
  contracts: 17 scenarios at rates 0, 1, 2**30, the one-day default, the 600 s rate and 2**64 - 1,
  native ETH and 18/6-decimal ERC-20 quotes, both token orders, test locker and router; 722 steps
  (641 executed, 81 refused), 14 claims, 145 previews and creations. Deltas, `LaunchSwapped`,
  `feeAt`, fee ledger, Core and holder balances, post state and claims all match.

Reproduce (`ZeroSeedLaunchSdkParityV2.t.sol` is generated from the v1 generator):

```sh
python3 tests/vectors/generator/make_tick_rate_parity.py
cp -a <evm-contracts at 3d6378f, built> <scratch>
cp tests/vectors/generator/ZeroSeedLaunchSdkParityV2.t.sol <scratch>/test/extensions/
(cd <scratch> && forge test --offline --match-contract ZeroSeedLaunchSdkParityV2 -vv) > <parity-log>
python3 tests/vectors/generator/parity_to_json.py v2 < <parity-log> > tests/vectors/v2/zero-seed-launch-parity.json
cp <scratch>/test/vectors/zero-seed-launch.json tests/vectors/v2/zero-seed-launch.json   # verbatim
cargo test --features evm,starknet,serde --test zero_seed_launch_tick_rate
```

No v2 deployment exists. `ZeroSeedLaunchInstance::validate` accepts two LOCAL fixture instances, one
per model: the `43d6628` one and the indexer's `3d6378f` anvil fixture
(`tests/vectors/v2/zero-seed-launch-indexer.json`, verbatim, sha256 `52377ccd...1d2f`), each only with
its own fee model.

## Gas

SDK gas constants are unchanged UNCALIBRATED estimates. Against the regenerated parity vectors the
error on the 370 test-locker fills that are neither a launch's first fill nor a known zero-slot
write is -39.5% to +26.8% (mean +1.5%); cold slots, first swaps, routers, calldata, transaction
base and UserOp costs are not predicted.

## Reproduce

```sh
cp -a <evm-contracts at 43d6628, built> <scratch>          # never edit the source checkout
cp <scratch>/test/vectors/zero-seed-launch.json <scratch>/test/vectors/zero-seed-launch-installation.json \
  tests/vectors/   # verbatim
cp tests/vectors/generator/ZeroSeedLaunchSdkParity.t.sol tests/vectors/generator/ZeroSeedLaunchLocalFixturePins.t.sol \
  <scratch>/test/extensions/
(cd <scratch> && forge test --offline --match-contract ZeroSeedLaunchSdkParity -vv) > <parity-log>
python3 tests/vectors/generator/parity_to_json.py < <parity-log> > tests/vectors/zero-seed-launch-parity.json
(cd <scratch> && forge test --offline --match-path test/extensions/ZeroSeedLaunchFeeCurve.t.sol -vv) \
  | python3 tests/vectors/generator/fee_curve_rows_to_json.py 43d6628841b3ce91dafa048b7ceef64bed55fc8e \
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
