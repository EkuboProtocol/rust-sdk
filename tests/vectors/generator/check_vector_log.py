#!/usr/bin/env python3
"""Bind delivered JSON vectors to actual verbose Solidity test output.
Usage: python3 check-vector-log.py <zero-seed-launch.json> <forge-test-restored.out>
"""
import json
from pathlib import Path
import sys

# The contract's v5 vectors keep the creation gas measured before `_validate` lost its ceiling
# comparison; the executed creation is 34 gas cheaper. Only these exact pairs are tolerated.
STALE = {("gas", "t0", "create"): ("1367815", "1367781"), ("gas", "t1", "create"): ("1327004", "1326970")}

v = json.loads(Path(sys.argv[1]).read_text())
stale = 0
rows = [l.strip().split("|") for l in Path(sys.argv[2]).read_text().splitlines()
        if l.strip().startswith("VEC|")]
count = 0
for row in rows:
    kind = row[1]
    d = dict(field.split("=", 1) for field in row[2:] if "=" in field)
    if kind == "create":
        expected = next(x for x in v[kind] if x["order"] == d["order"] and x["dec"] == d["dec"])
    elif kind == "trade":
        if row[4] == "upperResidue":
            expected = next(x for x in v["residue_metrics"]["scenarios"] if
                            x["order"] == d["order"] and x["decimals"] == d["dec"])
            assert expected["position_token_before_exhaust"] == d["positionTokenBefore"]
            assert expected["delivered_raw_token"] == d["delivered"]
            assert expected["upper_residue_raw_token"] == d["residueToken"]
            count += 1
            continue
        expected = next(x for x in v[kind] if x["order"] == d["order"] and
                        x["decimals"] == d["dec"] and x["step"] == row[4])
        d = {k: val for k, val in d.items() if k != "dec"}
    elif kind == "fee":
        t = int(d["t"].removeprefix("start+"))
        expected = next(x for x in v[kind] if int(x["duration"]) == int(d["duration"]) and x["t_minus_start"] == t)
        d = {"duration": d["duration"], "fee_q64": d["feeQ64"]}
    elif kind in ("gas", "router"):
        expected = next(x for x in v[kind] if x["order"] == d["order"])
    else:
        continue
    for k, val in d.items():
        if (kind, d.get("order"), k) in STALE:
            assert (str(expected[k]), val) == STALE[kind, d["order"], k], (kind, k, val, expected[k])
            stale += 1
            continue
        assert str(expected[k]) == val, (kind, k, val, expected[k])
    count += 1
assert count == 4 + sum(len(v[k]) for k in ("create", "trade", "fee", "gas", "router")), count
assert stale == len(STALE), stale
print(f"PASS: {count} complete emitted vector rows match delivery JSON "
      f"({stale} stale creation gas values, exactly as pinned)")
