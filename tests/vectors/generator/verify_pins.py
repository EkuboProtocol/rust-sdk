#!/usr/bin/env python3
"""Offline, exact source-pin receipts; run from the SDK root. No provider access."""
import hashlib
import json
from pathlib import Path

root = Path("tests/vectors")
expected = {
    "zero-seed-launch-indexer.json": "b4026beee434641d3420de7db672d9424d79bad3a3ed86f44f50cf2bd5ca16fd",
    "zero-seed-launch.json": "303055e5fe7bcb67755e2723036e408048c8761d9b7e118185a7c118da6e1723",
    "zero-seed-launch-fee-curve-rows.json": "bf3d3098c9b77befd35166c974793ec1ecdeccaa03adf5cf0b9888c67cac6320",
    "pins/pins.json": "449da40cf91ac0d4ea24faa78ce6399545bc576d3dea99c40d257dc2041ceb35",
    "pins/ZeroSeedLaunch.abi.json": "bc51b39284a5a2a0970d3a804420762ce291dc01f9c21ddf31840e354a3792bb",
    "pins/IZeroSeedLaunch.abi.json": "60eaec35405f1a750acc93794cd724d744ffa2be9abc87cc41145fb3ea915f40",
    "pins/MintableERC20.abi.json": "0f0d0950f409dfb10d8985ba15e203f3d028d127d674a7b89dff9a0bfc66b348",
}
for name, digest in expected.items():
    actual = hashlib.sha256((root / name).read_bytes()).hexdigest()
    assert actual == digest, (name, actual, digest)
    print(actual, name)
pins = json.loads((root / "pins/pins.json").read_text())["ZeroSeedLaunch"]
parity = json.loads((root / "zero-seed-launch-parity.json").read_text())
assert parity["source"]["contracts"] == "EkuboProtocol/evm-contracts@b1cbb1c1a9a00de62072a63a8f4aab4d97065573 (tree 3f9196ebe47ebbff04459d08d645f8ca3168244a)"
assert sum(len(s["steps"]) for s in parity["scenarios"]) == 407
assert len(parity["scenarios"]) == 9
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
create = "create((address,string,string,uint8,uint128,uint128,int32,int32,uint32,uint64,uint32,uint64,uint64,uint64,bytes32))"
assert pins["functions"][create] == "0xd5f50468"
assert pins["functions"]["feeAt(bytes32,uint256)"] == "0xe81084ec"
assert pins["functions"]["getLaunch(bytes32)"] == "0x7d1d589c"
changed = pins["abiCompatibility"]["removedEntries"] + pins["abiCompatibility"]["addedEntries"]
assert all(e[0] != "error" for e in changed), "errors and their selectors are unchanged"
indexer = json.loads((root / "zero-seed-launch-indexer.json").read_text())
assert indexer["chainId"] == 31337
assert indexer["provenance"]["evmContractsHead"] == "b1cbb1c1a9a00de62072a63a8f4aab4d97065573"
source = Path("src/quoting/pools/zero_seed_launch.rs").read_text()
for entry in indexer["instances"][:2]:
    assert entry["address"].lower() in source
    assert entry["runtimeKeccak"] in source
    args = entry["constructorArguments"][2:]
    assert int(args[:64], 16) == int(indexer["addresses"]["core"], 16)
    assert int(args[64:], 16) == int(entry["quote"], 16)
assert "0x5100000000000000000000000000000000000000" not in source
print("PASS: 7 exact SHA256 receipts, 9 arithmetic parity fixtures, 407 step slots, 2 actual supported indexer tuples; live manifest EMPTY")
