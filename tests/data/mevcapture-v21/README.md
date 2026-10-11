# MEVCapture v2.1 contract fixtures

Source: EkuboProtocol/evm-contracts merge
`da368348238a46857d39b6db57bdb2b432c979df`, `test/data/mevcapture-v21`.
Design authority: EKU-946 rev6 `ad3e6585-8135-431e-82af-7a177d7f5282`.
The JSON metadata's rev5 labels are stale; the merged contract and expected
values include Q1 reference restoration on passing gates.

The JSON files are copied verbatim; SHA256SUMS pins their bytes.

## Current implementation checkpoint

- 120 anchor updates: compare gate outcome and all seven anchor fields.
- 24 gate scenarios / 1785 steps: first-touch, snapshots, wraparound, H1,
  refresh, Q1 quiet/warmup/idle-drop and failed-gate clocks.
- 288 mathematical schedules: compare each boundary, index, fee and toward tick.
- Nondefault configuration and nine existing v1 regression tests.

`swaps.json` is pinned for the next implementation step. Its 32 swaps / 152
Core calls have **not** yet been replayed by the SDK. The mathematical schedule
is not an executable quote: membership must be checked using sqrt ratios, and
execution must respect user limits, minFee, N1 slivers, checked signed sums,
remaining amount and the away-call budget.

## Representations

- `getConfig.maxFee`, pool fees and Core `minFee` are contract Q0.16. The SDK's
  EVM fee is Q0.64: lossless conversion of contract fees is `u64::from(fee) << 48`.
  Do not treat `32768` as an SDK fee or guess deployment defaults.
- Anchor is signed Q48.16 ticks. Schedule boundaries use mirrored coordinates
  internally; golden JSON boundaries use actual tick coordinates. Decreasing
  toward calls use ceil(anchor), increasing calls use floor(anchor).
- Swap golden sqrt ratios are raw compressed 96-bit contract `SqrtRatio`, not
  SDK U256 Q128.128. Conversion/rounding must be verified against
  `src/types/sqrtRatio.sol` and the SDK EVM chain adapter before swap parity is claimed.

## Focused commands

```sh
cargo test --features evm --test mev_capture_v21_golden
cargo test --features evm,starknet mev_capture::
cargo clippy --features evm --lib --test mev_capture_v21_golden -- -D warnings
cargo fmt --all -- --check
```

The existing library-test macros reference Starknet unconditionally; focused
v1 library tests therefore need both `evm,starknet`. No SDK publish or deployment.
