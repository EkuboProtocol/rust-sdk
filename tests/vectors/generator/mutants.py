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
    ("no constructor quote check", "if parameters.quote_token != self.instance.constructor_quote {", "if false {"),
    ("zero output accepted", "if requested > 0 && quote.calculated_amount == 0 {", "if false {"),
    ("fee cap off by one", "if fee.initial_fee > ZERO_SEED_LAUNCH_MAX_CREATOR_FEE {", "if fee.initial_fee >= ZERO_SEED_LAUNCH_MAX_CREATOR_FEE {"),
    ("binding not checked", "if installation.installed_supply != parameters.supply {", "if false {"),
    ("live network accepted", "self.chain_id != 31337", "false"),
    ("extension identity ignored", '|| self.extension != addr("0x5100000000000000000000000000000000000000")', ""),
    ("Core identity ignored", '|| self.core != addr("0x00000000000014aa86c5d3c41765bb24e11bd701")', ""),
    ("getter ignored", "|| self.quote_token_getter != self.constructor_quote", ""),
    ("executed runtime ignored", "|| self.extension_runtime != runtime", ""),
    ("Core runtime ignored", '|| self.core_runtime\n                != hash("0xc5f90c9d0dbc5037f8f9e248f4bb292e7c1824f584eb6550cb4cad525b38c71a")', ""),
    ("quote runtime ignored", '|| self.quote_runtime\n                != hash("0x8a3a1f6a9f9dce633117adee5b458245835a8645a8c8726a26382a4622508b1c")', ""),
    ("32-byte metadata accepted", "self.name.len() > 31", "self.name.len() > 32"),
    ("metadata character count", "self.name.len() > 31", "self.name.chars().count() > 31"),
    ("collision ignored", "if self.predicted_token_has_code {", "if false {"),
    ("margin off by one", "checked_add(300)", "checked_add(299)"),
    ("start cap removed", "|| start > max_start", ""),
    ("expiry at start rejected", "self.execution_expiry > start", "self.execution_expiry >= start"),
    ("expired plan accepted", "|| now >= self.execution_expiry", ""),
    ("fresh start margin removed", "|| start < fresh_min", ""),
    ("Core sink accepted", "|| recipient == instance.core", ""),
    ("extension sink accepted", "|| recipient == instance.extension", ""),
    ("token0 sink accepted", "|| recipient == key.token0", ""),
    ("token1 sink accepted", "|| recipient == key.token1", ""),
]

original = open(PATH).read()
killed = 0
try:
    for name, old, new in MUTANTS:
        assert original.count(old) >= 1, name
        open(PATH, "w").write(original.replace(old, new))
        r = subprocess.run(
            ["cargo", "test", "--offline", "--features", "evm,serde", "--test", "zero_seed_launch_vectors", "-q"],
            capture_output=True,
        )
        if r.returncode != 0 and b"test result: FAILED" not in r.stdout:
            print(r.stderr.decode(), flush=True)
            raise RuntimeError("control must compile and fail an assertion: " + name)
        status = "KILLED" if r.returncode != 0 else "SURVIVED"
        killed += r.returncode != 0
        print(f"{status}\t{name}", flush=True)
finally:
    open(PATH, "w").write(original)
print(f"{killed}/{len(MUTANTS)} killed")
sys.exit(0 if killed == len(MUTANTS) else 1)
