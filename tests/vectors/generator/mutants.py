#!/usr/bin/env python3
"""Negative controls: applies one mutation at a time to src/quoting/pools/zero_seed_launch.rs and
expects `cargo test --test zero_seed_launch_vectors` to fail. Restores the file afterwards."""
import subprocess
import sys

PATH = "src/quoting/pools/zero_seed_launch.rs"
MUTANTS = [
    ("exact-out fee not grossed up",
     "amount_before_fee::<Evm>(calculated_abs, fee_rate).ok_or(E::AmountBeforeFeeOverflow)?\n                - calculated_abs",
     "compute_fee::<Evm>(calculated_abs, fee_rate)"),
    ("fee on the specified side", "let fee_is_token1 = !is_token1;", "let fee_is_token1 = is_token1;"),
    ("no clamp to the upper bound", "limit.min(self.upper_sqrt_ratio)", "limit"),
    ("no clamp to the lower bound", "limit.max(self.lower_sqrt_ratio)", "limit"),
    ("fee decay rounds up",
     "/ u128::from(self.fee_duration);",
     ".div_ceil(u128::from(self.fee_duration));"),
    ("trading start exclusive", "if timestamp < self.launch.fee.trading_start {", "if timestamp <= self.launch.fee.trading_start {"),
    ("installed supply rounded down", "amount1_delta(lower, upper, liquidity, true)", "amount1_delta(lower, upper, liquidity, false)"),
    ("token0 max liquidity rounded up", "muldiv(U256::from(amount), numerator, upper - lower, false)", "muldiv(U256::from(amount), numerator, upper - lower, true)"),
    ("skipAhead 1", "const SKIP_AHEAD: u32 = 0;", "const SKIP_AHEAD: u32 = 1;"),
    ("no bitmap word stop", "let word_end = (raw >> 8 << 8) + 255;", "let word_end = (raw >> 9 << 9) + 511;"),
    ("tick cap off by one", "u128::MAX / ticks", "u128::MAX / ticks + 1"),
    ("no supported quote check", "|| !supported_quote_tokens.contains(&parameters.quote_token)", ""),
    ("zero output accepted", "if requested > 0 && quote.calculated_amount == 0 {", "if false {"),
    ("fee cap off by one", "if fee.initial_fee > ZERO_SEED_LAUNCH_MAX_CREATOR_FEE {", "if fee.initial_fee >= ZERO_SEED_LAUNCH_MAX_CREATOR_FEE {"),
    ("binding not checked", "if installation.installed_supply != parameters.supply {", "if false {"),
]

original = open(PATH).read()
killed = 0
try:
    for name, old, new in MUTANTS:
        assert original.count(old) == 1, name
        open(PATH, "w").write(original.replace(old, new))
        r = subprocess.run(
            ["cargo", "test", "--features", "evm,starknet,serde", "--test", "zero_seed_launch_vectors", "-q"],
            capture_output=True,
        )
        status = "KILLED" if r.returncode != 0 else "SURVIVED"
        killed += r.returncode != 0
        print(f"{status}\t{name}", flush=True)
finally:
    open(PATH, "w").write(original)
print(f"{killed}/{len(MUTANTS)} killed")
sys.exit(0 if killed == len(MUTANTS) else 1)
