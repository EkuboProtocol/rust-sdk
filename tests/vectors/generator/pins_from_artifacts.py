#!/usr/bin/env python3
"""Regenerates tests/vectors/pins/ from an evm-contracts checkout built with `forge build --offline`.

Usage (from the SDK root):
  python3 tests/vectors/generator/pins_from_artifacts.py <evm-contracts-root> <consumer-manifest.json> <pin-log>

`<pin-log>` is the `-vv` output of `ZeroSeedLaunchLocalFixturePins.t.sol` run in a scratch copy of the same checkout.
Keccak comes from the pinned Foundry `cast`; no provider access. ABI files are canonical JSON, exactly `jq -cS .abi` of
the artifact WITHOUT a trailing newline, so each file's SHA-256 is the consumer manifest's `abi_sha256_canonical_json`.
The manifest's selector, topic and error tables and artifact hashes are copied into `pins.json` under
`consumerManifest`; `tests/zero_seed_launch_vectors.rs` recomputes all of them from the ABI files.

The local fixture is ONE extension and ONE periphery with no quote: every launch selects its own quote. Its addresses
are recomputed here from the artifacts (the first CREATE2 salt of the deterministic deployer whose address carries the
call-point byte, the periphery at salt 0), and each executed runtime must equal the template runtime with exactly one
assignment of its immutables. The local ERC-20 quote is the plain test ERC-20 (`test/TestToken.sol`, no immutables) at
the top of the address space. When `tests/vectors/zero-seed-launch-indexer.json` is a receipt of the same commit, its
single instance and its ERC-20 quotes are checked against these pins as well.
"""
import hashlib
import itertools
import json
import subprocess
import sys
from pathlib import Path

root = Path(sys.argv[1])
manifest = json.loads(Path(sys.argv[2]).read_text())
pin_log = Path(sys.argv[3]).read_text()
pins_dir = Path("tests/vectors/pins")
head = subprocess.check_output(["git", "-C", str(root), "rev-parse", "HEAD"], text=True).strip()
assert head == manifest["frozen_commit"], (head, manifest["frozen_commit"])
CONTRACTS = ("ZeroSeedLaunch", "ZeroSeedLaunchPeriphery", "MintableERC20")
CALL_POINTS_BYTE = 0x51
LOCAL_CHAIN_ID = 31337


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


def word(value):
    return int(value, 16).to_bytes(32, "big")


def create2(deployer, salt, init_code_hash):
    digest = keccak(b"\xff" + bytes.fromhex(deployer[2:]) + salt + bytes.fromhex(init_code_hash[2:]))
    return "0x" + digest[-40:]


pins = {"source": f"EkuboProtocol/evm-contracts@{head}"}
for name in CONTRACTS:
    art = artifact(name)
    abi_bytes = canonical(art["abi"])
    (pins_dir / f"{name}.abi.json").write_bytes(abi_bytes)
    runtime = bytes.fromhex(art["deployedBytecode"]["object"][2:])
    creation = bytes.fromhex(art["bytecode"]["object"][2:])
    refs = art["deployedBytecode"].get("immutableReferences", {})
    entry = {
        "abiSha256": hashlib.sha256(abi_bytes).hexdigest(),
        "functions": {s: "0x" + art["methodIdentifiers"][s] for s in sorted(art["methodIdentifiers"])},
        "events": {signature(e): keccak(signature(e)) for e in sorted(
            (e for e in art["abi"] if e["type"] == "event"), key=signature)},
        "errors": {signature(e): keccak(signature(e))[:10] for e in sorted(
            (e for e in art["abi"] if e["type"] == "error"), key=signature)},
        "templateRuntime": {"bytes": len(runtime), "zeroFilledKeccak": keccak(runtime)},
        "creation": {"bytes": len(creation), "keccak": keccak(creation)},
        # AST ids are renumbered between builds.
        "immutableReferences": {k: {"locations": v} for k, v in sorted(refs.items(), key=lambda kv: int(kv[0]))},
    }
    expected = manifest["artifacts"][name]
    assert entry["abiSha256"] == expected["abi_sha256_canonical_json"], name
    assert entry["templateRuntime"]["zeroFilledKeccak"] == expected["runtime_template_keccak256_immutables_zero"], name
    assert entry["creation"]["keccak"] == expected["creation_code_keccak256_no_constructor_args"], name
    assert len(runtime) == expected["runtime_length"] and len(creation) == expected["creation_code_length"], name
    pins[name] = entry


def fill(name, values, expected):
    """The template runtime with each immutable set to one of `values`: exactly one assignment must reproduce the
    executed runtime keccak, which binds the pin to this commit's code and constructor arguments."""
    art = artifact(name)
    runtime = bytes.fromhex(art["deployedBytecode"]["object"][2:])
    refs = sorted(art["deployedBytecode"]["immutableReferences"].items(), key=lambda kv: int(kv[0]))
    found = []
    for combo in itertools.product(sorted(values), repeat=len(refs)):
        code = bytearray(runtime)
        for (_, locations), label in zip(refs, combo):
            for location in locations:
                code[location["start"]:location["start"] + 32] = word(values[label])
        if keccak(bytes(code)) == expected:
            found.append({ref: label for (ref, _), label in zip(refs, combo)})
    assert len(found) == 1, (name, expected, found)
    return found[0]


executed = next(line.strip() for line in pin_log.splitlines() if line.strip().startswith("PIN|"))
executed = dict(part.split("=", 1) for part in executed.split("|")[1:])
core = executed["core"].lower()
deployer = executed["deployer"].lower()
launch_creation = bytes.fromhex(artifact("ZeroSeedLaunch")["bytecode"]["object"][2:])
periphery_creation = bytes.fromhex(artifact("ZeroSeedLaunchPeriphery")["bytecode"]["object"][2:])

launch_args = word(core)
launch_init_hash = keccak(launch_creation + launch_args)
assert launch_init_hash == executed["extensionInitCodeKeccak"]
for i in itertools.count():
    salt = i.to_bytes(32, "big")
    extension = create2(deployer, salt, launch_init_hash)
    if int(extension[2:4], 16) == CALL_POINTS_BYTE:
        break
assert extension == executed["extension"].lower() and "0x" + salt.hex() == executed["extensionSalt"], extension
periphery_args = word(core) + word(extension)
periphery_init_hash = keccak(periphery_creation + periphery_args)
assert periphery_init_hash == executed["peripheryInitCodeKeccak"]
periphery = create2(deployer, bytes(32), periphery_init_hash)
assert periphery == executed["periphery"].lower(), periphery
quote_runtime = bytes.fromhex(artifact("TestToken")["deployedBytecode"]["object"][2:])
assert keccak(quote_runtime) == executed["quoteRuntimeKeccak"]
assert executed["coreRuntimeKeccak"] == "0xc5f90c9d0dbc5037f8f9e248f4bb292e7c1824f584eb6550cb4cad525b38c71a"

pins["localFixture"] = {
    "chainId": LOCAL_CHAIN_ID,
    "core": core,
    "coreRuntimeKeccak": executed["coreRuntimeKeccak"],
    "deployer": deployer,
    "extension": extension,
    "extensionSalt": "0x" + salt.hex(),
    "extensionConstructorArguments": "0x" + launch_args.hex(),
    "extensionInitCodeKeccak": launch_init_hash,
    "extensionRuntimeKeccak": executed["extensionRuntimeKeccak"],
    "extensionImmutables": fill("ZeroSeedLaunch", {"core": core}, executed["extensionRuntimeKeccak"]),
    "periphery": periphery,
    "peripherySalt": "0x" + bytes(32).hex(),
    "peripheryConstructorArguments": "0x" + periphery_args.hex(),
    "peripheryInitCodeKeccak": periphery_init_hash,
    "peripheryRuntimeKeccak": executed["peripheryRuntimeKeccak"],
    "peripheryImmutables": fill(
        "ZeroSeedLaunchPeriphery", {"core": core, "extension": extension}, executed["peripheryRuntimeKeccak"]),
    "scope": "constructor-executed LOCAL anvil fixture (chain 31337, no fork), not a deployed network pin; "
             "one extension and one periphery serve every quote",
}
pins["localQuotes"] = [{
    "chainId": LOCAL_CHAIN_ID,
    "quote": executed["quote"].lower(),
    "runtimeKeccak": executed["quoteRuntimeKeccak"],
    "source": "test/TestToken.sol:TestToken (plain 18-decimal ERC-20, no immutables), relocated",
    "scope": "LOCAL fixture ERC-20 quote only; no live quote is reviewed",
}]
pins["consumerManifest"] = {
    "frozenCommit": manifest["frozen_commit"],
    "frozenTree": manifest["frozen_tree"],
    "manifestSha256": hashlib.sha256(Path(sys.argv[2]).read_bytes()).hexdigest(),
    "abiSha256Convention": "sha256 of `jq -cS .abi` of the Foundry artifact, no trailing newline",
    "abiSha256": {n: manifest["artifacts"][n]["abi_sha256_canonical_json"] for n in CONTRACTS},
    "abi": manifest["abi"],
    "structs": manifest["structs"],
    "forwardSchema": manifest["forward_schema"],
}
(pins_dir / "pins.json").write_text(json.dumps(pins, indent=1) + "\n")

receipt = json.loads(Path("tests/vectors/zero-seed-launch-indexer.json").read_text())
if receipt["provenance"]["evmContractsHead"] == head:
    (instance,) = receipt["instances"]
    fixture = pins["localFixture"]
    for field in ("extension", "periphery"):
        assert instance[field].lower() == fixture[field], field
    for field in ("extensionRuntimeKeccak", "peripheryRuntimeKeccak"):
        assert instance[field] == fixture[field], field
    for launch in receipt["launches"].values():
        if launch["quoteKind"] == "erc20":
            assert {"quote": launch["quote"].lower(), "runtimeKeccak": launch["quoteRuntimeKeccak"]} in [
                {"quote": q["quote"], "runtimeKeccak": q["runtimeKeccak"]} for q in pins["localQuotes"]]
    print("indexer receipt instance and quotes match the local fixture pins")
else:
    print("indexer receipt is for", receipt["provenance"]["evmContractsHead"], "- local fixture not cross-checked")
print(json.dumps({n: pins[n]["abiSha256"] for n in CONTRACTS}), "pins.json written for", head)
