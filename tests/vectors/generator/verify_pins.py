#!/usr/bin/env python3
"""Offline, exact source-pin receipts; run from the SDK root. No provider access."""
import hashlib
import json
from pathlib import Path

root = Path("tests/vectors")
expected = {
    "zero-seed-launch.json": "0a136d132d37de2d775e7f50b6bba413d2fda1cfd5c63e294d6bd060e28e8127",
    "pins/pins.json": "f78c349e1403ecf89d2bc1b7be208752ec4e8692729d8bc727227b93525ab881",
    "pins/ZeroSeedLaunch.abi.json": "189ff93c0f6fb64f6e7dd0675872bf6686692f8303e6218b8c2521bfa5ced215",
    "pins/IZeroSeedLaunch.abi.json": "4c519694df0d35d77e382a35a4423367e0b8b8f3548294856240e2f83eec20bf",
    "pins/MintableERC20.abi.json": "0f0d0950f409dfb10d8985ba15e203f3d028d127d674a7b89dff9a0bfc66b348",
}
for name, digest in expected.items():
    actual = hashlib.sha256((root / name).read_bytes()).hexdigest()
    assert actual == digest, (name, actual, digest)
    print(actual, name)
pins = json.loads((root / "pins/pins.json").read_text())["ZeroSeedLaunch"]
parity = json.loads((root / "zero-seed-launch-parity.json").read_text())
assert parity["source"]["contracts"] == "EkuboProtocol/evm-contracts@d6aeb58d845aa29454f3ed8df15e84a306a6f26d (tree 28946ed5a980df9cd030931e365741fe6b971b50)"
assert sum(len(s["steps"]) for s in parity["scenarios"]) == 307
for scenario in parity["scenarios"]:
    c = scenario["create"]
    fixture = next(f for f in pins["localFixtures"].values() if f["quote"].lower() == c["constructorQuote"].lower())
    assert c["extension"].lower() == fixture["extension"]
    assert c["extensionCodehash"] == fixture["runtimeKeccak"]
    args = fixture["constructorArguments"][2:]
    assert int(args[:64], 16) == int(fixture["core"], 16)
    assert int(args[64:], 16) == int(c["constructorQuote"], 16)
    assert c["coreCodehash"] == "0xc5f90c9d0dbc5037f8f9e248f4bb292e7c1824f584eb6550cb4cad525b38c71a"
    assert c["extensionCodehash"] != pins["templateRuntime"]["zeroFilledKeccak"]
    if c["quoteDecimals"] == "18":
        assert c["quoteCodehash"] == "0x8a3a1f6a9f9dce633117adee5b458245835a8645a8c8726a26382a4622508b1c"
    else:
        assert c["quoteCodehash"] != "0x8a3a1f6a9f9dce633117adee5b458245835a8645a8c8726a26382a4622508b1c"
assert pins["functions"]["quoteToken()"] == "0x217a4b70"
assert pins["errors"]["MetadataTooLong()"]["selector"] == "0x85b8e2f4"
assert pins["errors"]["LaunchTokenExists(address)"]["selector"] == "0xf68475cd"
print("PASS: 5 exact SHA256 receipts, 7 constructor-executed fixtures, 307 step slots; live manifest EMPTY")
