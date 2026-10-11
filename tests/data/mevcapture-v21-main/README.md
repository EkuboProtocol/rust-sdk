# MEVCapture v2.1 `main` variant fixtures

- `v21-main-quoter-vectors.json`: 21 scenarios / 266 Core calls traced from
  `MEVCaptureV21` on the current Core (EKU-1582, branch
  `eku-1582/mevcapture-v21-main` @ `75ed4cf`, Core `main` 98d1be1) by
  `forge test --offline --match-test test_vectors -vv`. Copied verbatim. The
  vectors carry the pool state but not the minted positions, so
  `tests/mev_capture_v21_main_vectors.rs` rebuilds each pool's initialized
  ticks from the `test_vectors_*` functions in
  `test/extensions/MEVCaptureV21Rules.t.sol`; the pool constructor checks
  the rebuilt ticks against the traced active liquidity.
- `anchorUpdates.json`, `gateScenarios.json`: the `next` extension's fixtures
  (EkuboProtocol/evm-contracts `da368348`, `test/data/mevcapture-v21`).
  `_refresh`, `_decayedReference`, `_raise` and `beforeUpdatePosition` are
  textually identical in the `main` extension. `_anchorUpdate` differs only in
  the movement allowance, which `main` rounds up (EKU-1582 `17b5e50`, V12
  F-13) where `next` floors, so the replay expects one extra unit on the case
  that the fractional floored allowance bound. The replay ignores the
  `next`-only config fields. The F-13 contract tests are ported as
  `f13_per_second_updates_cannot_freeze_anchor`, `dust_allowance_rounds_up`
  and `frequent_updates_never_slow_anchor`.

Re-run the vector generator against the merged contract commit before
shipping and replace the file if it changed.
