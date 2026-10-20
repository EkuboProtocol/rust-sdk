#!/usr/bin/env python3
"""Converts the `VEC|` lines of the contract's fee-curve study into zero-seed-launch-fee-curve-rows.json.

Usage, in a checkout of the target evm-contracts commit:
  forge test --offline --match-path test/extensions/ZeroSeedLaunchFeeCurve.t.sol -vv \
    | python3 fee_curve_rows_to_json.py <commit> > tests/vectors/zero-seed-launch-fee-curve-rows.json
Each row keeps the raw line and its `key=value` fields, copied as printed."""
import json
import sys

out = {"source": f"EkuboProtocol/evm-contracts@{sys.argv[1]} test/extensions/ZeroSeedLaunchFeeCurve.t.sol"}
for raw in sys.stdin:
    line = raw.strip()
    if not line.startswith("VEC|"):
        continue
    parts = line.split("|")
    row = {"raw": line}
    for part in parts[2:]:
        key, sep, value = part.partition("=")
        if sep:
            row[key] = value
    out.setdefault(parts[1], []).append(row)
json.dump(out, sys.stdout, indent=1)
sys.stdout.write("\n")
