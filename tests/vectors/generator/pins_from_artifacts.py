#!/usr/bin/env python3
"""Regenerates tests/vectors/pins/ from an evm-contracts checkout built with `forge build --offline`.

Usage (from the SDK root):
  python3 tests/vectors/generator/pins_from_artifacts.py <evm-contracts-root> <consumer-manifest.json>

Keccak comes from the pinned Foundry `cast`; no provider access. ABI files are canonical JSON, exactly
`jq -cS .abi` of the artifact WITHOUT a trailing newline, so each file's SHA-256 is the consumer manifest's
`abi_sha256_canonical_json`. The manifest's selector, topic and error tables and artifact hashes are copied into
`pins.json` under `consumerManifest`; `tests/zero_seed_launch_vectors.rs` recomputes all of them from the ABI files.
Local fixture pins come from the indexer receipt `tests/vectors/zero-seed-launch-indexer.json`.
"""
import hashlib
import json
import subprocess
import sys
from pathlib import Path

root = Path(sys.argv[1])
manifest = json.loads(Path(sys.argv[2]).read_text())
pins_dir = Path("tests/vectors/pins")
head = subprocess.check_output(["git", "-C", str(root), "rev-parse", "HEAD"], text=True).strip()
assert head == manifest["frozen_commit"], (head, manifest["frozen_commit"])
CONTRACTS = ("ZeroSeedLaunch", "ZeroSeedLaunchPeriphery", "MintableERC20")


def keccak(data):
    if isinstance(data, str):
        return subprocess.check_output(["cast", "keccak", data], text=True).strip()
    return subprocess.check_output(["cast", "keccak", "0x" + data.hex()], text=True).strip()


def artifact(name):
    return json.loads((root / f"out/{name}.sol/{name}.json").read_text())


def canonical(abi):
    return json.dumps(abi, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode()


def signature(item):
    def kind(p):
        if p["type"].startswith("tuple"):
            return "(" + ",".join(kind(c) for c in p["components"]) + ")" + p["type"][len("tuple"):]
        return p["type"]

    return f"{item['name']}(" + ",".join(kind(p) for p in item["inputs"]) + ")"


def ast_names(ids):
    names = {}
    for info in (root / "out/build-info").glob("*.json"):
        stack = [json.loads(info.read_text())]
        while stack:
            node = stack.pop()
            if isinstance(node, dict):
                if node.get("id") in ids and node.get("nodeType") == "VariableDeclaration":
                    names[node["id"]] = node["name"]
                stack.extend(node.values())
            elif isinstance(node, list):
                stack.extend(node)
    return names


def word(value):
    return int(value, 16).to_bytes(32, "big")


pins = {"source": f"EkuboProtocol/evm-contracts@{head}"}
for name in CONTRACTS:
    art = artifact(name)
    abi_bytes = canonical(art["abi"])
    (pins_dir / f"{name}.abi.json").write_bytes(abi_bytes)
    runtime = bytes.fromhex(art["deployedBytecode"]["object"][2:])
    creation = bytes.fromhex(art["bytecode"]["object"][2:])
    refs = art["deployedBytecode"]["immutableReferences"]
    names = ast_names({int(k) for k in refs})
    entry = {
        "abiSha256": hashlib.sha256(abi_bytes).hexdigest(),
        "functions": {s: "0x" + art["methodIdentifiers"][s] for s in sorted(art["methodIdentifiers"])},
        "events": {signature(e): keccak(signature(e)) for e in sorted(
            (e for e in art["abi"] if e["type"] == "event"), key=signature)},
        "errors": {signature(e): keccak(signature(e))[:10] for e in sorted(
            (e for e in art["abi"] if e["type"] == "error"), key=signature)},
        "templateRuntime": {"bytes": len(runtime), "zeroFilledKeccak": keccak(runtime)},
        "creation": {"bytes": len(creation), "keccak": keccak(creation)},
        # AST ids are renumbered between builds; names are present only when the build-info carries ASTs.
        "immutableReferences": {k: ({"name": names[int(k)], "locations": v} if int(k) in names else {"locations": v})
                                for k, v in sorted(refs.items(), key=lambda kv: int(kv[0]))},
    }
    expected = manifest["artifacts"][name]
    assert entry["abiSha256"] == expected["abi_sha256_canonical_json"], name
    assert entry["templateRuntime"]["zeroFilledKeccak"] == expected["runtime_template_keccak256_immutables_zero"], name
    assert entry["creation"]["keccak"] == expected["creation_code_keccak256_no_constructor_args"], name
    assert len(runtime) == expected["runtime_length"] and len(creation) == expected["creation_code_length"], name
    pins[name] = entry

indexer = json.loads(Path("tests/vectors/zero-seed-launch-indexer.json").read_text())
core = indexer["addresses"]["core"].lower()
launch_creation = bytes.fromhex(artifact("ZeroSeedLaunch")["bytecode"]["object"][2:])
periphery_creation = bytes.fromhex(artifact("ZeroSeedLaunchPeriphery")["bytecode"]["object"][2:])
pins["localFixtures"] = {}
for instance in indexer["instances"]:
    extension = instance["extension"].lower()
    launch_args = word(core) + word(instance["quote"])
    periphery_args = word(core) + word(extension)
    pins["localFixtures"][instance["label"]] = {
        "chainId": indexer["chainId"],
        "core": core,
        "coreRuntimeKeccak": indexer["provenance"]["coreRuntimeKeccak"],
        "quote": instance["quote"].lower(),
        "quoteKind": instance["quoteKind"],
        "quoteRuntimeKeccak": instance["quoteRuntimeKeccak"],
        "extension": extension,
        "extensionConstructorArguments": "0x" + launch_args.hex(),
        "extensionInitCodeKeccak": keccak(launch_creation + launch_args),
        "extensionRuntimeKeccak": instance["extensionRuntimeKeccak"],
        "periphery": instance["periphery"].lower(),
        "peripheryConstructorArguments": "0x" + periphery_args.hex(),
        "peripheryInitCodeKeccak": keccak(periphery_creation + periphery_args),
        "peripheryRuntimeKeccak": instance["peripheryRuntimeKeccak"],
        "scope": "constructor-executed LOCAL anvil fixture (chain 31337, no fork), not a deployed network pin",
    }


def fill(name, values, expected):
    """The template runtime with each immutable set to one of `values`: exactly one assignment must reproduce the
    executed runtime keccak of the fixture, which binds the pin to this commit's code and constructor arguments."""
    art = artifact(name)
    runtime = bytes.fromhex(art["deployedBytecode"]["object"][2:])
    refs = sorted(art["deployedBytecode"]["immutableReferences"].items(), key=lambda kv: int(kv[0]))
    found = []
    for combo in __import__("itertools").product(sorted(values), repeat=len(refs)):
        code = bytearray(runtime)
        for (_, locations), label in zip(refs, combo):
            for location in locations:
                code[location["start"]:location["start"] + 32] = word(values[label])
        if keccak(bytes(code)) == expected:
            found.append({ref: label for (ref, _), label in zip(refs, combo)})
    assert len(found) == 1, (name, expected, found)
    return found[0]


for instance in indexer["instances"]:
    fixture = pins["localFixtures"][instance["label"]]
    fixture["extensionImmutables"] = fill(
        "ZeroSeedLaunch", {"core": core, "quote": instance["quote"]}, fixture["extensionRuntimeKeccak"])
    fixture["peripheryImmutables"] = fill(
        "ZeroSeedLaunchPeriphery", {"core": core, "extension": fixture["extension"]}, fixture["peripheryRuntimeKeccak"])
pins["consumerManifest"] = {
    "frozenCommit": manifest["frozen_commit"],
    "abiSha256Convention": "sha256 of `jq -cS .abi` of the Foundry artifact, no trailing newline",
    "abiSha256": {n: manifest["artifacts"][n]["abi_sha256_canonical_json"] for n in CONTRACTS},
    "abi": manifest["abi"],
    "structs": manifest["structs"],
    "forwardSchema": manifest["forward_schema"],
}
(pins_dir / "pins.json").write_text(json.dumps(pins, indent=1) + "\n")
print(json.dumps({n: pins[n]["abiSha256"] for n in CONTRACTS}), "pins.json written for", head)
