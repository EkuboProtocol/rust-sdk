# MEVCapture v2.1 contract fixtures

Source: EkuboProtocol/evm-contracts merge
`da368348238a46857d39b6db57bdb2b432c979df`, `test/data/mevcapture-v21`.
Design authority: EKU-946 rev6 `ad3e6585-8135-431e-82af-7a177d7f5282`.
The JSON metadata's rev5 labels are stale; the merged contract and expected
values include Q1 reference restoration on passing gates.

The JSON files are copied verbatim; SHA256SUMS pins their bytes.

## Supplementary vectors (EKU-1577)

`swapsSupplement.json` and `swapsNondefault.json` were generated from the
unmodified merged contract `da368348238a46857d39b6db57bdb2b432c979df` by
`generator/MEVCaptureV21SupplementVectors.t.sol`, which reuses the merged
`MEVCaptureV21SwapVectorsTest` writer, so every swap is also checked against
the reference twin pool. In the same environment the merged generator
reproduced `swaps.json` byte for byte. To regenerate, copy the generator to
`test/extensions/` of that commit and run
`FOUNDRY_PROFILE=v21vectors forge test --offline --mc MEVCaptureV21SupplementVectorsTest`.

They cover what `swaps.json` does not: Core word-boundary step splits with
liquidity, user `minFee` on away segments, the post-swap refresh raise and its
suppression by a position in the same timestamp, and a nondefault `getConfig`
tuple with decay clamping, capped segments and a pass-through swap.

## Replay coverage

- 120 anchor updates: compare gate outcome and all seven anchor fields.
- 24 gate scenarios / 1785 steps: first-touch, snapshots, wraparound, H1,
  refresh, Q1 quiet/warmup/idle-drop and failed-gate clocks.
- 288 mathematical schedules: compare each boundary, index, fee and toward tick.
- Executable swaps, replayed from inputs only (positions and swap parameters):
  `swaps.json` 32 swaps / 152 Core calls, supplement 9 / 61, nondefault 6 / 10.
  Each swap compares gate, every Core call (limit, minFee, remaining amount, in
  order), both deltas, pool sqrt ratio/tick/liquidity and all seven anchor
  fields; `Pool::quote` is checked against the same result when minFee is 0.
- The vector reference omits the no-op pass-through Core call that the contract
  makes for a zero amount or a price already at the user limit; the SDK reports
  it as `MevCaptureV21CallKind::PassThrough` and the replay checks it is a no-op.

## Representations

- `getConfig.maxFee`, pool fees and Core `minFee` are contract Q0.16. The SDK's
  EVM fee is Q0.64: lossless conversion of contract fees is `u64::from(fee) << 48`.
  Do not treat `32768` as an SDK fee or guess deployment defaults.
- Anchor is signed Q48.16 ticks. Schedule boundaries use mirrored coordinates
  internally; golden JSON boundaries use actual tick coordinates. Decreasing
  toward calls use ceil(anchor), increasing calls use floor(anchor).
- Swap golden sqrt ratios are raw compressed 96-bit contract `SqrtRatio`. The
  SDK keeps the 64.128 fixed-point value (`toFixed`); every SDK ratio is exactly
  representable, and the replay converts with `fixed_sqrt_ratio_to_contract_sqrt_ratio`
  and checks the round trip. Core step results are rounded with `Evm::round_sqrt_ratio`,
  which mirrors `toSqrtRatio`.
- Core's stored tick can be one below `sqrt_ratio_to_tick` after a decreasing
  swap stops exactly on a step tick; the SDK emulates Core's bitmap steps
  (initialized ticks, 256-spacing word ends, `skipAhead`) and keeps Core's tick.

## Focused commands

```sh
cargo test --features evm --test mev_capture_v21_golden   # 8 tests
cargo test --features evm,starknet mev_capture::
cargo clippy --features evm --lib --test mev_capture_v21_golden -- -D warnings
cargo fmt --all -- --check
```

The existing library-test macros reference Starknet unconditionally; focused
v1 library tests therefore need both `evm,starknet`. No SDK publish or deployment.
