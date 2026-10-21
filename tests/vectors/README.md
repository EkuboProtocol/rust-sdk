# Zero-seed launch conformance (LOCAL evidence only)

Target: `EkuboProtocol/evm-contracts@40af6cb359b0de2f61f15e47b6622a00c48b5b08`, tree
`f9925da3e2047b5ab5e45729056a3595043aa804` (forward-only `ZeroSeedLaunch` with a per-launch
quote, requested supply with an `address(0)` sink, fixed-base fee table, separate
`ZeroSeedLaunchPeriphery`). Q0.64 Core/raw tick spacing, zero Core fee, separate creator fee.
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
- Selectors and topics: periphery `create 0x662af306`, `previewInstallation 0x917c1163`
  (extension and periphery), `LaunchCreated 0x3a4e8111...098f`. `SupplyNotExactlyInstallable`
  is gone. Swap and claim forward payloads, pool config, pool id, the `Installation` struct,
  `LaunchSwapped`, `CreatorFeesClaimed`, the periphery's claim/transfer/owner functions and
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

with 256-bit intermediates (`r * TABLE < 2**256`, numerator `< 2**192`). Cap `floor(99 * 2**64 /
100)` = `18262276632972456099`. The canonical example is 50% -> 0.3% over 3,600 s.

## Vectors (SHA-256)

| file | sha256 | source |
|---|---|---|
| `zero-seed-launch.json` | `869408e73a94f74c3cbd9d92a1f41b24ef7593a16759759fd89abc6a3b6a4776` | the contract's `test/vectors/zero-seed-launch.json`, verbatim |
| `zero-seed-launch-fee-curve-all-seconds.json` | `fc9be5e4d59d8163f7a5566a7076bb9628d8ff30af5efde1eb554ba9b93bddce` | protocol generator's 250-digit `Decimal` output, every second of 12 curves, 25,212 `[initial, final, duration, elapsed, fee]` rows (delivered gzipped, gz sha256 `b1f5ff563c58869fd6667977614c89c30ea0b27353ecac40752fb24736951900`; stored decompressed so tests need no extra dependency) |
| `zero-seed-launch-fee-decay-vectors.json` | `7004b29f91540f1b29a568b525d215227565b36d1b490687ae604f5f145b835b` | `gen-fee-decay-table.py --json`: table, decay samples, 200 fee rows, digests |
| `zero-seed-launch-fee-curve-rows.json` | `96a8dbdee103f3da920fd2744e823e9469e118d20c478553e30cb029980988f2` | the 100 executed `VEC|highRate` rows of `ZeroSeedLaunchFeeCurve.t.sol` (rows identical to the previous target's; only the source commit changed) |
| `zero-seed-launch-parity.json` | `198f8cfe38ecdd2e94804b4c06e2bf6bda499a47bb8b1523865f5d09c55be491` | `generator/ZeroSeedLaunchSdkParity.t.sol` |
| `zero-seed-launch-indexer.json` | `c4cea4e1d1accf56fcf7beb90743321cd6b1c4761e304651c3636dc9136d482b` | indexer `scripts/zeroSeedLaunchFixture.ts` LOCAL anvil receipt, verbatim. This is still the receipt of the PREVIOUS target (`4f1a306`, two instances with constructor quotes); the receipt of this target replaces it, and the tests that read it are ignored until then |
| `pins/pins.json` | `36f4467d21c662a06ebdaf1864057c085bd7b57cbe5e41229f21589499a16884` | `generator/pins_from_artifacts.py` |
| `pins/*.abi.json` | `999068f8...d4bf`, `df24d9f0...7305`, `fa77fe07...abba` | canonical ABIs of `ZeroSeedLaunch`, `ZeroSeedLaunchPeriphery`, `MintableERC20` |

The consumer manifest is `zero-seed-interface-40af6cb.json` (file sha256
`6dce9c6bcb0dd1be2a542109b546a4199db55b01f5a0bdcfead13e721eadea6b`, its own `manifest_sha256`
`5eb115a68920aab6ed83f0fa61f961f841c5680e7cdb05be57b757ed74079dcb`), generated from the target's
compiled artifacts; its tables are copied into `pins.json` under `consumerManifest`.

What the tests check:

- `fee_curve_tests.rs` (unit): the table equals both the contract's and the generator's;
  `decay_q128(2**i) = TABLE[i]`; bit 0 equals the contract's conditional subtraction; zero cutoff
  without aliasing; monotone over all of `[0, 131072]`, first zero at 76,800 s; EVERY one of the
  25,212 oracle rows equals `decayed_fee` and `fee_at`; the 12 SHA-256 chains
  (`h = sha256(h || fee as 8-byte big-endian)`, `t = 0..D`, `h0 = 0^32`) recomputed from the oracle
  and from the SDK equal the contract's pins (and the generator's 10); the 200 generator rows and
  the contract's 18 `fee` rows; the contract's pinned deviation from the previous variable-base
  schedule (32/82/120/133/133 Q64 units); the 100 executed high-rate swap rows (50/75/90/99/max%,
  plain ERC-20 and native orders, 18/6) and the exact-output signed and helper bounds at the
  injected maximum rate. `2**64 - 1` is refused by validation and `new_math`; it is exercised
  only by overwriting a valid pool's stored initial fee inside the unit test, as the contract
  injects storage.
- `tests/zero_seed_launch_vectors.rs`:
  - frozen contract vectors: fee rows, the four installations of the requested 1e27 supply
    (installed, liquidity, bounds and the 790/578/697,343,214/717,714,600 sinks), trades,
    residues, the test router's 1e18 buys and the dust buy;
  - parity: 13 scenarios, 522 step slots. Eleven are the previous target's programs (plain
    ERC-20 token0 and native token1 at 18/18 over 3,600 s and 600 s, 6-decimal quotes in both
    orders, 50% -> 0.3% over 3,600 s in both orders, 99% over 600 s, a near-max-tick overflow
    launch); their 507 step slots (deltas, events, fee rates and amounts, ledgers, pre and post
    Core state) are byte-identical to the previous vectors, so the swap math is unchanged. Two more
    create a native-quote and an ERC-20-quote launch on ONE extension and periphery and trade them
    alternately through `LaunchTestRouter` and the test locker. Every successful step compares SDK
    deltas, fee amount and side, the `LaunchSwapped` rate, the ledger change, Core and holder
    balances (native ETH by value) and chained post-state; reverts map to SDK errors; partial
    fills at the upper bound, no-bid sells and zero fills are explicit; each periphery claim equals
    the SDK fee sum, its return value and both claim events. Every creation records requested,
    installed and sink supply, `totalSupply == requested`, `balanceOf(address(0)) == sink`, the
    sink `Transfer` and the Core `PositionUpdated` token delta `== installed` (asserted in the
    generator and again in the tests);
  - 129 periphery previews, each followed by `create` with the same requested supply: the SDK's
    `ZeroSeedLaunchLocalPreview::contract_preview` reproduces every result and refusal (including
    `UnsupportedQuoteToken` for a codeless quote, `MetadataTooLong`, `LaunchTokenExists` for a
    collision and for the same salt with another quote, `ZeroLiquidity`, `LiquidityAboveTickCap`),
    the predicted token, and every creation installs exactly its preview;
  - the supported instance serves the native and the ERC-20 launch, and every instance, quote
    observation, pool key, claim recipient, metadata, collision, token order and timing control
    fails closed;
  - the 92 manifest selectors, topics and errors recomputed from the pinned ABI files, whose bytes
    hash to the manifest's ABI sha256 (`jq -cS .abi`, no trailing newline);
  - ignored until the receipt of this target lands: `indexer_launches_decode_bind_and_predict`,
    `indexer_trades_ledgers_owners_and_fees_replay`, `local_fixture_pins_match_the_indexer_receipt`.
    They expect one `instances` entry without a quote, and per launch `quote`, `quoteKind`
    (`native`/`erc20`), `quoteRuntimeKeccak` (null for native) and installations with
    `requestedSupply`, `installedSupply`, `sinkSupply` and `liquidity`.
- `pins/pins.json` (`generator/pins_from_artifacts.py`): per contract ABI hash, selectors, topics,
  errors, zero-filled runtime and creation keccak, all asserted equal to the consumer manifest;
  the local fixture (`localFixture`) recomputed from the artifacts: the extension at the first
  CREATE2 salt of the deterministic deployer whose address carries the call-point byte `0x51`, the
  periphery at salt 0, init-code keccaks, and the unique immutable assignment that turns each
  template runtime into the executed runtime (extension: `core`, `core`; periphery: `core`,
  `extension`, `core`); and the one reviewed LOCAL ERC-20 quote (`localQuotes`, the plain
  18-decimal `test/TestToken.sol` at the top of the address space).

## Supported surface versus arithmetic

`ZeroSeedLaunchPool::new` requires a `ZeroSeedLaunchInstance` observation matching the one LOCAL
fixture instance (chain 31337, Core `0x00000000000014aa86c5d3c41765bb24e11bd701`, runtime
`0xc5f90c9d...c71a`; extension `0x519ddb6580e97e08e639d601dc6e378285c3ef34`, runtime
`0x32160cd1...88be`; periphery `0x094511cf93e73feca154da35a2404e8bde1111b4`, runtime
`0x91a98d26...e7c1`) and a `ZeroSeedLaunchQuoteObservation` of the launch's own quote that
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
cp -a <evm-contracts at 40af6cb, built> <scratch>          # never edit the source checkout
cp <scratch>/test/vectors/zero-seed-launch.json tests/vectors/   # verbatim
cp tests/vectors/generator/ZeroSeedLaunchSdkParity.t.sol tests/vectors/generator/ZeroSeedLaunchLocalFixturePins.t.sol \
  <scratch>/test/extensions/
(cd <scratch> && forge test --offline --match-contract ZeroSeedLaunchSdkParity -vv) > <parity-log>
python3 tests/vectors/generator/parity_to_json.py < <parity-log> > tests/vectors/zero-seed-launch-parity.json
(cd <scratch> && forge test --offline --match-path test/extensions/ZeroSeedLaunchFeeCurve.t.sol -vv) \
  | python3 tests/vectors/generator/fee_curve_rows_to_json.py 40af6cb359b0de2f61f15e47b6622a00c48b5b08 \
  > tests/vectors/zero-seed-launch-fee-curve-rows.json
(cd <scratch> && forge test --offline --match-path test/extensions/ZeroSeedLaunch.t.sol -vv) > <main-log>
python3 tests/vectors/generator/check_vector_log.py tests/vectors/zero-seed-launch.json <main-log>
(cd <scratch> && forge test --offline --match-contract ZeroSeedLaunchLocalFixturePins -vv) > <pin-log>
python3 tests/vectors/generator/pins_from_artifacts.py <scratch> <consumer-manifest.json> <pin-log>
python3 tests/vectors/generator/verify_pins.py
cargo test --features evm,starknet,serde
python3 tests/vectors/generator/mutants.py
```

Known-safe SDK rollback is `main` (no launch support). NOT PROVEN: any live instance, network
registration or deployment, any live ERC-20 quote review, downstream preview/decoder/owner
enforcement, whole-stack QA, external audit, fee-parameter selection or release authorization.
