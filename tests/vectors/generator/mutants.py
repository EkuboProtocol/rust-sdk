#!/usr/bin/env python3
"""Negative controls: applies one mutation at a time to src/quoting/pools/zero_seed_launch.rs and
expects the zero-seed unit tests or `tests/zero_seed_launch_vectors.rs` to fail. Restores the file afterwards."""
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
    ("decay rounds up", "result = (result * U256::from(*constant)) >> 128;",
     "result = (result * U256::from(*constant)).div_ceil(TWO_POW_128);"),
    ("decay bits applied in descending order", ".iter().enumerate() {", ".iter().enumerate().rev() {"),
    ("one table constant off", "448_060,", "448_061,"),
    ("bit 0 constant off", "339_889_484_297_159_900_493_648_602_831_395_569_057,",
     "339_889_484_297_159_900_493_648_602_831_395_569_056,"),
    ("no zero cutoff", "if elapsed >= ZERO_SEED_LAUNCH_DECAY_ZERO_FROM {", "if elapsed >= 1 << 18 {"),
    ("endpoint normalization dropped",
     "(decay_q128(elapsed) - endpoint)\n        / (TWO_POW_128 - endpoint)",
     "decay_q128(elapsed)\n        / TWO_POW_128"),
    ("normalized excess rounds up", "/ (TWO_POW_128 - endpoint);", ".div_ceil(TWO_POW_128 - endpoint);"),
    ("linear schedule kept",
     "let endpoint = decay_q128(u64::from(duration));",
     "return initial_fee - (u128::from(initial_fee - final_fee) * u128::from(elapsed) / u128::from(duration)) as u64;\n    let endpoint = decay_q128(u64::from(duration));"),
    ("zero duration accepted", "if fee.final_fee > fee.initial_fee || fee.fee_duration == 0 {",
     "if fee.final_fee > fee.initial_fee {"),
    ("old 10% cap", "pub const ZERO_SEED_LAUNCH_MAX_CREATOR_FEE: u64 = 18_262_276_632_972_456_099;",
     "pub const ZERO_SEED_LAUNCH_MAX_CREATOR_FEE: u64 = 1_844_674_407_370_955_161;"),
    ("trading start exclusive", "if timestamp < self.launch.fee.trading_start {", "if timestamp <= self.launch.fee.trading_start {"),
    ("installed supply rounded down", "amount1_delta(lower, upper, liquidity, true)", "amount1_delta(lower, upper, liquidity, false)"),
    ("token0 max liquidity rounded up", "muldiv(U256::from(amount), numerator, upper - lower, false)", "muldiv(U256::from(amount), numerator, upper - lower, true)"),
    ("skipAhead 1", "const SKIP_AHEAD: u32 = 0;", "const SKIP_AHEAD: u32 = 1;"),
    ("no bitmap word stop", "let word_end = (raw >> 8 << 8) + 255;", "let word_end = (raw >> 9 << 9) + 511;"),
    ("tick cap off by one", "u128::MAX / ticks", "u128::MAX / ticks + 1"),
    ("zero output accepted", "if requested > 0 && quote.calculated_amount == 0 {", "if false {"),
    ("fee cap off by one", "if fee.initial_fee > ZERO_SEED_LAUNCH_MAX_CREATOR_FEE {", "if fee.initial_fee >= ZERO_SEED_LAUNCH_MAX_CREATOR_FEE {"),
    ("binding not checked", "if installation.installed_supply != parameters.supply {", "if false {"),
    ("native launch token accepted as token0", "if launch_token.is_zero() {", "if false {"),
    ("live network accepted", "if self.chain_id != LOCAL_CHAIN_ID", "if false"),
    ("extension identity ignored", "|| self.extension != addr(pin.extension)", ""),
    ("extension runtime ignored", "|| self.extension_runtime != hash(pin.extension_runtime)", ""),
    ("periphery identity ignored", "|| self.periphery != addr(pin.periphery)", ""),
    ("periphery runtime ignored", "|| self.periphery_runtime != hash(pin.periphery_runtime)", ""),
    ("Core identity ignored", "|| self.core != addr(LOCAL_CORE)", ""),
    ("Core runtime ignored", "|| self.core_runtime != hash(LOCAL_CORE_RUNTIME)", ""),
    ("getter ignored", "|| self.quote_token_getter != self.constructor_quote", ""),
    ("quote kind ignored", "|| !quote_kind_matches", ""),
    ("quote runtime ignored", "!self.constructor_quote.is_zero() && quote_runtime == hash(pinned)",
     "!self.constructor_quote.is_zero()"),
    ("32-byte metadata accepted", "self.name.len() > 31", "self.name.len() > 32"),
    ("metadata character count", "self.name.len() > 31", "self.name.chars().count() > 31"),
    ("collision ignored", "if self.predicted_token_has_code {", "if false {"),
    ("token order unchecked", "return Err(E::TokenOrderMismatch);", "return Ok(());"),
    ("margin off by one", "checked_add(300)", "checked_add(299)"),
    ("start cap removed", "|| start > max_start", ""),
    ("expiry at start rejected", "self.execution_expiry > start", "self.execution_expiry >= start"),
    ("expired plan accepted", "|| now >= self.execution_expiry", ""),
    ("fresh start margin removed", "|| start < fresh_min", ""),
    ("Core sink accepted", "|| recipient == instance.core", ""),
    ("extension sink accepted", "|| recipient == instance.extension", ""),
    ("periphery sink accepted", "|| recipient == instance.periphery", ""),
    ("token0 sink accepted", "|| recipient == key.token0", ""),
    ("token1 sink accepted", "|| recipient == key.token1", ""),
    ("owner salt not namespaced", "        periphery_launch_salt(owner, user_salt),", "        user_salt,"),
    ("token salt without controller", "    keccak_address_salt(controller, salt)", "    salt"),
    ("init code ignores decimals", "decimals_word[31] = decimals;", "decimals_word[31] = 18;"),
    ("symbol offset unpadded", "hasher.update(usize_word(4 * 32 + 32 + padded(name.len())));",
     "hasher.update(usize_word(4 * 32 + 32 + name.len()));"),
]

original = open(PATH).read()
killed = 0
try:
    for name, old, new in MUTANTS:
        assert original.count(old) >= 1, name
        open(PATH, "w").write(original.replace(old, new))
        r = subprocess.run(
            ["cargo", "test", "--offline", "--features", "evm,starknet,serde", "--lib", "--test", "zero_seed_launch_vectors",
             "-q"],
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
