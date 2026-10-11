# Current zero-seed conformance (draft LOCAL only)

Target: `EkuboProtocol/evm-contracts@d6aeb58d845aa29454f3ed8df15e84a306a6f26d`, tree
`28946ed5a980df9cd030931e365741fe6b971b50`, base `98d1be1b80f6945c50bf4c9b599ebe74b59549ee`.
Q0.64 Core/raw tick spacing, zero Core fee, separate creator fee. Not Q0.16 `next`.
No live instances/assets are approved; release is HOLD. Historical reviews are not new-head clearance.

- `zero-seed-launch.json`: the current 58 emitted vectors, copied unchanged from that revision;
  SHA256 `0a136d132d37de2d775e7f50b6bba413d2fda1cfd5c63e294d6bd060e28e8127`.
- `zero-seed-launch-parity.json`: 7 local scenarios, all 307 original step slots, 108 previews and
  160 binding attempts regenerated against the actual current Core/extension. Inputs and later
  branches follow the same complete program; changed quote settlement can change subsequent amounts.
  Every successful step compares SDK deltas, fee asset/amount, ledgers and chained state at the exact
  emitted timestamp. Per-asset Core/holder balance conservation and refusal rollback are checked.
- `pins/`: exact correction `pins.json` and three canonical ABIs. Constructor `(Core,address quote)`,
  `quoteToken()` and new errors are source-bound; public create/preview/claim/event shapes unchanged.
  `generator/verify_pins.py` verifies their SHA256 receipts and compares every emitted instance.

## Supported surface versus arithmetic

`ZeroSeedLaunchPool::new` requires an offline `ZeroSeedLaunchInstance` observation matching one of
the two LOCAL, chain-ID-31337, constructor-executed WETH fixtures. Extension/Core identity, constructor
quote, getter, executed extension runtime, Core runtime and actual WETH runtime are all essential.
These are caller-provided observations, NOT cryptographic proof, RPC reads or a live attestation.
Callers must read/bind them and pool state from one authentic local snapshot. There is no caller
allowlist override and no deserialization constructor bypass. Zero-filled template runtime is NEVER
an executed pin. A synthetic six-decimal quote with otherwise identical addresses fails support.

`new_math`, `preview_installation_math`, `check_launch_binding_math` and `fee_at` are deliberately
pure arithmetic APIs, not service support, calldata or plan production. Six-decimal tests use only
this surface. Service routing must NOT use `new_math` to evade the supported constructor.
Pure `fee_at` before start returns the initial rate; pool quotes before start refuse.

Supported `preview_installation`/`check_launch_binding` also require `ZeroSeedLaunchLocalPreview`:
31 UTF-8 **bytes** for both metadata fields, observed predicted-address collision refusal,
checked `build_time+300 <= start <= build_time+86400`, `build_time < expiry <= start`.
Revalidate at build/use/review with fresh time: future build, expiry at/before now, or remaining
start margin below 300 seconds refuse without rewriting signed start. Expiry equal to start is
valid at build, not a guarantee of mining before start. These are LOCAL draft references only.
Preview ONCE using requested supply; preserve requested supply separately and use that preview's
actual `(installed_supply, liquidity)` pair. Re-previewing the actual supply is not convergence.
`validate_claim_recipient` refuses exactly `{zero, Core, extension, token0, token1}`.

## MCP/owner handoff boundaries

The SDK has no RPC, ABI decoder, CREATE2 predictor, network registration reader, transaction builder,
wallet/signature/Permit2 flow, or actual contract-preview call. Collision code presence and all
provenance fields must be obtained and bound by the producer; this helper does not authenticate them.
MCP must perform the ONE actual `previewInstallation` and bind its token/pool/supply/L and ALL signed
calldata, metadata, creator, salt, decimals, rates, start/build/expiry/provenance in the owner summary.
Unsigned integer JSON decoding must reject negatives/fractions/overflow before these Rust types.
Do not invent fallback successes. Decode current ABI error payloads, including
`MetadataTooLong()` `0x85b8e2f4`, `LaunchTokenExists(address)` `0xf68475cd` (preserve address),
`UnsupportedQuoteToken()` `0x658d8331`, `InvalidRecipient()` `0x9c8d2cd2`.
LOCAL policy errors (`UnsupportedInstance`, `InvalidLocalTiming`) are not Solidity revert selectors.
Atomic full two-asset claims remain both-or-neither, rollback then retry to another valid recipient;
no per-side withdrawal or immutable-principal refund/rebalance/migration exists.
Permit2 defaults, mixed fee ledgers and creator fee recapture are disclosed, not permission.

## Distinct accounting metrics and gas

Upper residue is raw launch token held by the position before exhaustion minus delivered launch
token: canonical cases **89/89/94/90**. Core unowned dust is each asset's Core balance minus
rounded-down fixed-L position amount minus its creator ledger; token dust is **191/94478106/428919/91**,
quote dust **90/100/86/90** in the current vectors. There is NO shared <=90 bound. Neither is claimable
principal/fees. `residue_metrics` retains per-asset units and `dust_after.token=dust_before.token+residue`.

SDK gas constants are unchanged UNCALIBRATED estimates. Current WETH/synthetic harness non-cold fills
have up to 40% error, not the old synthetic quote's 30% bound. Cold slots/first swaps, router, calldata,
transaction base and UserOp costs are not predicted. The correction's same-WETH protocol baseline
comparison reports +100 create/+327 claim/0 swap under identical compiler settings; no new contract
gas optimization or bytecode change is claimed by this SDK re-pin.

## Reproduce, stop and reset

```sh
git -C <evm-contracts> worktree add --detach <task-parity-worktree> d6aeb58d845aa29454f3ed8df15e84a306a6f26d
cp tests/vectors/generator/ZeroSeedLaunchSdkParity.t.sol <task-parity-worktree>/test/extensions/
# Use that repository's pinned Foundry dependencies/toolchain; do not fetch providers.
(cd <task-parity-worktree> && forge test --offline --match-contract ZeroSeedLaunchSdkParity -vv) > <forge-log>
python3 tests/vectors/generator/parity_to_json.py < <forge-log> > tests/vectors/zero-seed-launch-parity.json
python3 tests/vectors/generator/verify_pins.py
cargo test --offline --features evm,serde --test zero_seed_launch_vectors
python3 tests/vectors/generator/mutants.py
```

Stop supported creation/routing/handoff and leave PR #40 draft/unmerged. Known-safe SDK rollback is
`main`/3.3.0 `32af2077663a9268612c206f8e6446cf024c2ba3` (NO launch support), never the obsolete
arbitrary-quote implementation. Local fixtures are in-memory Foundry runs: restart a fresh run to
reset; retain evidence and avoid other worktrees. No migrations or production data writes.

NOT PROVEN: authentic live instance/constructor/network/runtime/registration, full WETH CBOR metadata
reproduction, hosted timing parameters, downstream actual preview/decoder/owner enforcement,
whole-stack QA/Sage, provider/bundler/mined UserOp, external audit/legal/assets/retention/oncall/costs,
or release authorization. Local tests and guards do not close L-3 end-to-end.
