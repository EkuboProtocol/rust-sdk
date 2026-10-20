# Zero-seed launch conformance (LOCAL evidence only)

Target: `EkuboProtocol/evm-contracts@4f1a3060b099e8a50469848118f44c0c65cfab9a`, tree
`64649a281f113674584f192ff11b642071fdeac3` (forward-only `ZeroSeedLaunch`, native ETH quote,
fixed-base fee table, separate `ZeroSeedLaunchPeriphery`). Q0.64 Core/raw tick spacing, zero Core
fee, separate creator fee. Not Q0.16 `next`. Nothing here is deployed, audited or approved: there
are no live instances, and release is on HOLD.

## Interface at the target

- `LaunchParameters = (name, symbol, decimals, supply, liquidity, askTick, upperTick, tickSpacing,
  tradingStart, feeDuration, initialFee, finalFee, salt)`. Neither `quoteToken` nor `decayFactor`
  is a parameter: the quote is the extension's constructor immutable `quoteToken()`, and the decay
  is fixed. `ZeroSeedLaunchParameters` has no quote and `ZeroSeedLaunchFeeSchedule` no factor.
- Native ETH is `address(0)`: always token0, so the launch token is token1. It has no code, no
  `decimals()`, no approvals and no runtime hash. An ERC-20 quote (WETH in the fixtures) at the top
  of the address space makes the launch token token0.
- Creation, fee claims and swaps all arrive through `Core.forward`. Swaps forward
  `abi.encode(PoolKey, SwapParameters)` from any locker (the Yul router's forwarded hop, or the
  parity test locker). The forwarding locker of a creation is the launch `controller`; for
  `ZeroSeedLaunchPeriphery` it records the transferable owner (`LaunchOwnerChanged`) and pays
  claims (`LaunchFeesClaimed`, right after the extension's `CreatorFeesClaimed` with identical
  amounts: one claim, never counted twice).
- Token address: `CREATE2(extension, keccak256(abi.encode(controller, salt)),
  keccak256(MintableERC20.creationCode ++ abi.encode(extension, name, symbol, decimals)))`; through
  the periphery `salt = keccak256(abi.encode(owner, userSalt))` and `controller = periphery`. The
  SDK computes all three (`periphery_launch_salt`, `extension_token_salt`,
  `launch_token_address`/`periphery_launch_token_address`) with the embedded `MintableERC20`
  creation code (keccak `0x25da7fd3...2f52`).
- Claim recipients refused by the periphery (`InvalidRecipient`): zero, Core, the extension, the
  periphery, token0, token1. `validate_claim_recipient` mirrors all six.

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
| `zero-seed-launch.json` | `3a9801ff630ff86ec90967a53b4ee6199b626a577e23c204e74db9bc70fb47da` | the contract's `test/vectors/zero-seed-launch.json`, verbatim |
| `zero-seed-launch-fee-curve-all-seconds.json` | `fc9be5e4d59d8163f7a5566a7076bb9628d8ff30af5efde1eb554ba9b93bddce` | protocol generator's 250-digit `Decimal` output, every second of 12 curves, 25,212 `[initial, final, duration, elapsed, fee]` rows (delivered gzipped, gz sha256 `b1f5ff563c58869fd6667977614c89c30ea0b27353ecac40752fb24736951900`; stored decompressed so tests need no extra dependency) |
| `zero-seed-launch-fee-decay-vectors.json` | `7004b29f91540f1b29a568b525d215227565b36d1b490687ae604f5f145b835b` | `gen-fee-decay-table.py --json`: table, decay samples, 200 fee rows, digests |
| `zero-seed-launch-fee-curve-rows.json` | `192d5529a5e73be83adeb29a8b9da681bdb45337cfdc4b2be34f45854191c4ce` | the 100 executed `VEC|highRate` rows of `ZeroSeedLaunchFeeCurve.t.sol` |
| `zero-seed-launch-parity.json` | `4184ecb6e84e1df8ec7f807c16a2c7990d1bbed9c46270607ac18c61b39eb040` | `generator/ZeroSeedLaunchSdkParity.t.sol` |
| `zero-seed-launch-indexer.json` | `c4cea4e1d1accf56fcf7beb90743321cd6b1c4761e304651c3636dc9136d482b` | indexer `scripts/zeroSeedLaunchFixture.ts` LOCAL anvil receipt, verbatim |
| `pins/pins.json` | `c0b95763a5d12af2e139415bb4d260d9353b828f84a8e0e851d3493ea6c25083` | `generator/pins_from_artifacts.py` |
| `pins/*.abi.json` | `21f9e2c0...254e`, `5c563488...8a75`, `fa77fe07...abba` | canonical ABIs of `ZeroSeedLaunch`, `ZeroSeedLaunchPeriphery`, `MintableERC20` |

What the tests check:

- `fee_curve_tests.rs` (unit): the table equals both the contract's and the generator's;
  `decay_q128(2**i) = TABLE[i]`; bit 0 equals the contract's conditional subtraction; zero cutoff
  without aliasing; monotone over all of `[0, 131072]`, first zero at 76,800 s; EVERY one of the
  25,212 oracle rows equals `decayed_fee` and `fee_at`; the 12 SHA-256 chains
  (`h = sha256(h || fee as 8-byte big-endian)`, `t = 0..D`, `h0 = 0^32`) recomputed from the oracle
  and from the SDK equal the contract's pins (and the generator's 10); the 200 generator rows and
  the contract's 18 `fee` rows; the contract's pinned deviation from the previous variable-base
  schedule (32/82/120/133/133 Q64 units); the 100 executed high-rate swap rows (50/75/90/99/max%,
  WETH and native orders, 18/6) and the exact-output signed and helper bounds at the injected
  maximum rate. `2**64 - 1` is refused by validation and `new_math`; it is exercised only by
  overwriting a valid pool's stored initial fee inside the unit test, as the contract injects
  storage.
- `tests/zero_seed_launch_vectors.rs`:
  - indexer receipt: every `LaunchCreated` decoded from raw log data; pool id, pool key, owner of
    record, extension salt and token equal the CREATE2 prediction from owner, user salt and the
    emitted metadata; both instances validate and quote through supported `new`; all 19 swaps
    replayed against `LaunchSwapped` and the Core swap log, 8 claims against the extension ledger
    (accrued from `LaunchSwapped`, claimed from `CreatorFeesClaimed` only, payouts equal and never
    added again), owner transfers, and all 41 snapshots (`Core` state, `creatorFees`, owner,
    controller, `feeAt(block time)`), across the prefix and both reorg branches;
  - parity: 11 scenarios (WETH token0 and native token1 at 18/18 over 3,600 s and 600 s, 6-decimal
    quotes in both orders, 50% -> 0.3% over 3,600 s in both orders, 99% over 600 s, a near-max-tick
    overflow launch), 507 step slots. Every successful step compares SDK deltas, fee amount and
    side, the `LaunchSwapped` rate, the ledger change, Core and holder balances (native ETH by
    value) and chained post-state; reverts map to SDK errors; partial fills at the upper bound,
    no-bid sells and zero fills are explicit; each periphery claim equals the SDK fee sum, its
    return value and both claim events. 108 previews and 176 binding attempts decoded from revert
    data;
  - the 56 manifest selectors, topics and errors recomputed from the pinned ABI files, whose bytes
    hash to the manifest's ABI sha256 (`jq -cS .abi`, no trailing newline).
- `pins/pins.json` (`generator/pins_from_artifacts.py`): per contract ABI hash, selectors, topics,
  errors, zero-filled runtime and creation keccak, all asserted equal to the consumer manifest; for
  each local fixture the constructor arguments, init-code keccak and the unique immutable
  assignment that turns the target's template runtime into the recorded executed runtime
  (extension: `core`, `core`, `quote`; periphery: `core`, `extension`, `core`).

## Supported surface versus arithmetic

`ZeroSeedLaunchPool::new` requires a `ZeroSeedLaunchInstance` observation matching one of the two
LOCAL indexer instances (chain 31337, Core `0x00000000000014aa86c5d3c41765bb24e11bd701`, runtime
`0xc5f90c9d...c71a`):

| | native | weth |
|---|---|---|
| quote | `0x0000000000000000000000000000000000000000`, `Native` (no runtime) | `0xffffffffffffffffffffffffffffffffffffffff`, `Erc20 { 0x8a3a1f6a...8b1c }` |
| extension | `0x5114703a4cf4256f0acb68f992c861d8c4d1b173`, runtime `0x846786a6...1bf7` | `0x519435a42752da78e395999218d0ecc4fdcbcf4b`, runtime `0x56e32aea...3750` |
| periphery | `0xb27e16c3d01850191c1e027f7a3372cd2e1fb324`, runtime `0x57d0ee27...4f2a` | `0x94e1b338def908449e6ea7c7d254630b45d27562`, runtime `0xb78ea649...9ac8` |

Chain, extension and its runtime, periphery and its runtime, Core and its runtime, constructor
quote, `quoteToken()` and quote kind (with the quote runtime iff ERC-20) are all essential. These
are caller-provided observations, NOT cryptographic proof, RPC reads or a live attestation. The
Foundry parity instances run the same extension runtime at another address and are refused.

`new_math`, `preview_installation_math`, `check_launch_binding_math` and `fee_at` are pure
arithmetic, not service support, calldata or plan production. `preview_installation` and
`check_launch_binding` also require `ZeroSeedLaunchLocalPreview`: owner, user salt, metadata
(31 UTF-8 bytes each) and decimals, which fix the predicted token and so the token order
(`TokenOrderMismatch`), observed code at the predicted address, and the LOCAL timing rule
`build_time+300 <= start <= build_time+86400`, `build_time < expiry <= start`, re-checked with
fresh time. Preview once with the requested supply and bind that preview's
`(installed_supply, liquidity)`; previewing the installed supply again returns `liquidity - 1`.

## Gas

SDK gas constants are unchanged UNCALIBRATED estimates. Against the regenerated parity vectors the
error on the 370 fills that are neither a launch's first fill nor a known zero-slot write is
-39.4% to +26.8% (mean +2.0%); cold slots, first swaps, router, calldata, transaction base and
UserOp costs are not predicted.

## Reproduce

```sh
cp -a <evm-contracts at 4f1a306, built> <scratch>          # never edit the source checkout
cp tests/vectors/generator/ZeroSeedLaunchSdkParity.t.sol <scratch>/test/extensions/
(cd <scratch> && forge test --offline --match-contract ZeroSeedLaunchSdkParity -vv) > <parity-log>
python3 tests/vectors/generator/parity_to_json.py < <parity-log> > tests/vectors/zero-seed-launch-parity.json
(cd <scratch> && forge test --offline --match-path test/extensions/ZeroSeedLaunchFeeCurve.t.sol -vv) \
  | python3 tests/vectors/generator/fee_curve_rows_to_json.py 4f1a3060b099e8a50469848118f44c0c65cfab9a \
  > tests/vectors/zero-seed-launch-fee-curve-rows.json
(cd <scratch> && forge test --offline --match-path test/extensions/ZeroSeedLaunch.t.sol -vv) > <main-log>
python3 tests/vectors/generator/check_vector_log.py tests/vectors/zero-seed-launch.json <main-log>
python3 tests/vectors/generator/pins_from_artifacts.py <scratch> <consumer-manifest.json>
python3 tests/vectors/generator/verify_pins.py
cargo test --features evm,starknet,serde
python3 tests/vectors/generator/mutants.py
```

Known-safe SDK rollback is `main` (no launch support). NOT PROVEN: any live instance, network
registration or deployment, downstream preview/decoder/owner enforcement, whole-stack QA, external
audit, fee-parameter selection or release authorization.
