# AGENTS.md

## Complexity Policy
- `cargo clippy` enforces `clippy::cognitive_complexity`, enabled in `Cargo.toml`'s
  `[lints.clippy]` table with the threshold in `clippy.toml` (25, clippy's default,
  set explicitly). CI already runs clippy with `-D warnings`, so it is an error there
  and a warning locally — no CI change was needed.
- The lint is off by default upstream: it is in clippy's `restriction` group, and
  clippy's own docs say it does not measure cognitive complexity especially well. It
  is on here as a coarse guardrail against a function quietly becoming unreviewable,
  not as a precise metric. `clippy::excessive_nesting` and `clippy::too_many_lines`
  are the better-regarded lints if this repo ever wants a tighter structural gate.
- One exemption: `exp2` in `src/math/twamm/exp2.rs` carries
  `#[allow(clippy::cognitive_complexity)]`. It is binary exponentiation unrolled one
  bit at a time with per-bit magic constants — the branch count is the point, and the
  constants must stay bit-for-bit identical to the on-chain `exp2.sol` or TWAMM
  projections stop matching execution. A table-driven loop would change the rounding
  of the intermediate products.
- Any new `#[allow]` needs a comment saying why the branches are irreducible.
