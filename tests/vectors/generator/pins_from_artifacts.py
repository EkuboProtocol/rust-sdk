#!/usr/bin/env python3
"""Regenerates tests/vectors/pins/ from an evm-contracts checkout built with `forge build --offline`.

Usage (from the SDK root): python3 tests/vectors/generator/pins_from_artifacts.py <evm-contracts-root>
Keccak comes from the pinned Foundry `cast`; no provider access. The previous pins become `baseline`.
"""
import json
import subprocess
import sys
from pathlib import Path

root = Path(sys.argv[1])
pins_dir = Path("tests/vectors/pins")
head = subprocess.check_output(["git", "-C", str(root), "rev-parse", "HEAD"], text=True).strip()


def keccak(data):
    if isinstance(data, str):
        return subprocess.check_output(["cast", "keccak", data], text=True).strip()
    return subprocess.check_output(["cast", "keccak", "0x" + data.hex()], text=True).strip()


def artifact(name):
    return json.loads((root / f"out/{name}.sol/{name}.json").read_text())


def write_abi(name, abi):
    raw = json.dumps(abi, sort_keys=True, separators=(",", ":")).encode() + b"\n"
    (pins_dir / f"{name}.abi.json").write_bytes(raw)
    return __import__("hashlib").sha256(raw).hexdigest()


def signature(item):
    def kind(p):
        if p["type"].startswith("tuple"):
            return "(" + ",".join(kind(c) for c in p["components"]) + ")" + p["type"][len("tuple"):]
        return p["type"]

    return f"{item['name']}(" + ",".join(kind(p) for p in item["inputs"]) + ")"


def ast_names(ids):
    names = {}
    for info in (root / "out/build-info").glob("*.json"):
        text = info.read_text()
        if not any(f'"id":{i},' in text for i in ids if i not in names):
            continue
        stack = [json.loads(text)]
        while stack:
            node = stack.pop()
            if isinstance(node, dict):
                if node.get("id") in ids and "name" in node and node.get("nodeType") == "VariableDeclaration":
                    names[node["id"]] = node["name"]
                stack.extend(node.values())
            elif isinstance(node, list):
                stack.extend(node)
        if len(names) == len(ids):
            break
    return names


old = json.loads((pins_dir / "pins.json").read_text())
launch = artifact("ZeroSeedLaunch")
runtime = bytes.fromhex(launch["deployedBytecode"]["object"][2:])
creation = bytes.fromhex(launch["bytecode"]["object"][2:])
refs = launch["deployedBytecode"]["immutableReferences"]
names = ast_names({int(k) for k in refs})
if len(names) != len(refs):
    # Build-info without ASTs: AST ids are renumbered between revisions, so carry the previous names over in id
    # order and require the same reference count per immutable.
    previous = sorted(old["ZeroSeedLaunch"]["immutableReferences"].items(), key=lambda kv: int(kv[0]))
    current = sorted(refs.items(), key=lambda kv: int(kv[0]))
    assert [len(v["locations"]) for _, v in previous] == [len(v) for _, v in current]
    names = {int(k): v["name"] for (k, _), (_, v) in zip(current, previous)}

abis = {n: artifact(n)["abi"] for n in ("ZeroSeedLaunch", "IZeroSeedLaunch", "MintableERC20")}
hashes = {n: write_abi(n, a) for n, a in abis.items()}

prev = old["ZeroSeedLaunch"]
prev_sigs = {("function", s) for s in prev["functions"]} | {("event", s) for s in prev["events"]} | {
    ("error", s) for s in prev["errors"]}
cur = abis["ZeroSeedLaunch"]
cur_sigs = {(e["type"], signature(e)) for e in cur if e["type"] in ("function", "event", "error")}

pins = {
    "ZeroSeedLaunch": {
        "abiSha256": hashes["ZeroSeedLaunch"],
        "constructor": next(e for e in cur if e["type"] == "constructor"),
        "functions": {s: "0x" + launch["methodIdentifiers"][s] for s in sorted(launch["methodIdentifiers"])},
        "events": {signature(e): keccak(signature(e)) for e in sorted(
            (e for e in cur if e["type"] == "event"), key=signature)},
        "errors": {},
        "templateRuntime": {"bytes": len(runtime), "zeroFilledKeccak": keccak(runtime)},
        "creation": {"bytes": len(creation), "keccak": keccak(creation)},
        "immutableReferences": {k: {"name": names[int(k)], "locations": v} for k, v in sorted(refs.items())},
        "localFixtures": {},
        "abiCompatibility": {
            "source": f"EkuboProtocol/evm-contracts@{head}",
            "removedEntries": sorted([list(x) for x in prev_sigs - cur_sigs]),
            "addedEntries": sorted([list(x) for x in cur_sigs - prev_sigs]),
            "note": "LaunchParameters gains uint64 decayFactor after finalFee; Launch appends uint64 decayFactor. "
                    "create/previewInstallation/LaunchCreated change signature; getLaunch/feeAt keep selectors.",
        },
        "baseline": {
            "revision": "d6aeb58d845aa29454f3ed8df15e84a306a6f26d",
            "abiSha256": prev["abiSha256"],
            "runtimeBytes": prev["templateRuntime"]["bytes"],
            "creationBytes": prev["creation"]["bytes"],
            "zeroFilledRuntimeKeccak": prev["templateRuntime"]["zeroFilledKeccak"],
            "runtimeBytesDelta": len(runtime) - prev["templateRuntime"]["bytes"],
            "creationBytesDelta": len(creation) - prev["creation"]["bytes"],
        },
    },
    "IZeroSeedLaunch": {"abiSha256": hashes["IZeroSeedLaunch"]},
    "MintableERC20": {
        "abiSha256": hashes["MintableERC20"],
        "creation": {
            "bytes": len(bytes.fromhex(artifact("MintableERC20")["bytecode"]["object"][2:])),
            "keccak": keccak(bytes.fromhex(artifact("MintableERC20")["bytecode"]["object"][2:])),
        },
    },
}
for e in sorted((e for e in cur if e["type"] == "error"), key=signature):
    k = keccak(signature(e))
    pins["ZeroSeedLaunch"]["errors"][signature(e)] = {"selector": k[:10], "signatureKeccak": k}

core = "0x00000000000014aa86c5d3c41765bb24e11bd701"
parity = json.loads(Path("tests/vectors/zero-seed-launch-parity.json").read_text())
for label, quote in (("quoteHigh", "0xffffffffffffffffffffffffffffffffffffffff"),
                     ("quoteLow", "0x0000000000000000000000000000000000010000")):
    created = next(s["create"] for s in parity["scenarios"] if s["create"]["constructorQuote"].lower() == quote)
    args = "0x" + core[2:].rjust(64, "0") + quote[2:].rjust(64, "0")
    pins["ZeroSeedLaunch"]["localFixtures"][label] = {
        "extension": created["extension"].lower(),
        "core": core,
        "quote": quote,
        "constructorArguments": args,
        "initCodeKeccak": keccak(creation + bytes.fromhex(args[2:])),
        "runtimeKeccak": created["extensionCodehash"],
        "scope": "constructor-executed synthetic LOCAL fixture, not deployed network pin",
    }
(pins_dir / "pins.json").write_text(json.dumps(pins, indent=1) + "\n")
print(json.dumps({n: h for n, h in hashes.items()}), "pins.json written for", head)
