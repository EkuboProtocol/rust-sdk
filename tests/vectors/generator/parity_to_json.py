#!/usr/bin/env python3
"""Converts the PARITY| lines of ZeroSeedLaunchSdkParity.t.sol into zero-seed-launch-parity.json.

Usage: forge test --offline --match-contract ZeroSeedLaunchSdkParity -vv | python3 parity_to_json.py > out.json
Values are copied as decimal strings exactly as the contracts printed them."""
import json
import sys


def state(v):
    sqrt_ratio, tick, liquidity = v.split(",")
    return {"sqrt_ratio": sqrt_ratio, "tick": int(tick), "liquidity": liquidity}


def fields(line):
    out = {}
    for part in line.split("|")[2:]:
        k, _, v = part.partition("=")
        out[k] = v
    return out


scenarios, previews, creations = {}, [], []
for raw in sys.stdin:
    line = raw.strip()
    if not line.startswith("PARITY|"):
        continue
    kind = line.split("|")[1]
    f = fields(line)
    if kind == "create":
        name = f.pop("scenario")
        f["state"] = state(f["state"])
        scenarios[name] = {"name": name, "create": f, "steps": [], "claim": None}
    elif kind == "step":
        name = f.pop("scenario")
        step = {
            "i": int(f["i"]),
            "label": f["label"],
            "ts": f["ts"],
            "specified_is_token1": f["specifiedIs1"] == "1",
            "amount": f["amount"],
            "limit": f["limit"],
            "held_token": f["heldToken"],
            "token_allowance": f["tokenAllowance"],
            "held_quote": f["heldQuote"],
            "core_quote": f["coreQuote"],
            "pre": state(f["pre"]),
            "ok": f["ok"] == "1",
            "post": state(f["post"]),
            "pre_balances": f["preBalances"].split(","),
            "post_balances": f["postBalances"].split(","),
            "via_router": f["viaRouter"] == "1",
        }
        if step["ok"]:
            d0, d1, rate, fee, fee1 = f["event"].split(",")
            l0, l1 = f["ledger"].split(",")
            step.update(
                delta0=f["d0"],
                delta1=f["d1"],
                fee_at=f["feeAt"],
                ledger_delta0=l0,
                ledger_delta1=l1,
                event={"delta0": d0, "delta1": d1, "fee_rate": rate, "fee_amount": fee, "fee_is_token1": fee1 == "1"},
                gas=f["gas"],
            )
        else:
            step["error"] = f["err"]
        scenarios[name]["steps"].append(step)
    elif kind == "claim":
        name = f.pop("scenario")
        f["post"] = state(f["post"])
        scenarios[name]["claim"] = f
    elif kind == "preview":
        f["ok"] = f["ok"] == "1"
        previews.append(f)
    elif kind == "creation":
        f["ok"] = f["ok"] == "1"
        creations.append(f)

json.dump(
    {
        "version": 3,
        "label": "LOCAL FIXTURE PARITY VECTORS - not live evidence",
        "source": {
            "contracts": "EkuboProtocol/evm-contracts@550afc40280423128c02eb5ffd213aa959b34e2a (tree dbbfe6a5eb5ddefe04974338b2b57bdf675c431e)",
            "core": "local Core built at that commit, runtime keccak 0xc5f90c9d0dbc5037f8f9e248f4bb292e7c1824f584eb6550cb4cad525b38c71a (asserted in every scenario)",
            "flow": "one extension (constructor (core)) and one periphery per test serve native and ERC-20 quotes; launches created through ZeroSeedLaunchPeriphery with the requested supply unchanged; swaps are Core.forward(extension, abi.encode(PoolKey, SwapParameters)) from the test locker or test/LaunchTestRouter.sol; native ETH settled by value",
            "generator": "tests/vectors/generator/ZeroSeedLaunchSdkParity.t.sol",
        },
        "scenarios": list(scenarios.values()),
        "previews": previews,
        "creations": creations,
    },
    sys.stdout,
    indent=1,
)
sys.stdout.write("\n")
