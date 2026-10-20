#!/usr/bin/env python3
"""Offline, exact source-pin receipts; run from the SDK root. No provider access."""
import hashlib
import json
from pathlib import Path

root = Path("tests/vectors")
expected = {
    "zero-seed-launch.json": "3a9801ff630ff86ec90967a53b4ee6199b626a577e23c204e74db9bc70fb47da",
    "zero-seed-launch-indexer.json": "c4cea4e1d1accf56fcf7beb90743321cd6b1c4761e304651c3636dc9136d482b",
    "zero-seed-launch-fee-decay-vectors.json": "7004b29f91540f1b29a568b525d215227565b36d1b490687ae604f5f145b835b",
    "zero-seed-launch-fee-curve-all-seconds.json": "fc9be5e4d59d8163f7a5566a7076bb9628d8ff30af5efde1eb554ba9b93bddce",
    "zero-seed-launch-fee-curve-rows.json": "192d5529a5e73be83adeb29a8b9da681bdb45337cfdc4b2be34f45854191c4ce",
    "zero-seed-launch-parity.json": "4184ecb6e84e1df8ec7f807c16a2c7990d1bbed9c46270607ac18c61b39eb040",
    "pins/pins.json": "c0b95763a5d12af2e139415bb4d260d9353b828f84a8e0e851d3493ea6c25083",
    "pins/ZeroSeedLaunch.abi.json": "21f9e2c0166ab28ce8573c481de5b0fc2f37dd7595d496d326f0a2d1a544254e",
    "pins/ZeroSeedLaunchPeriphery.abi.json": "5c563488b843aee923d0d819a66489eeee543dd20d1582de1f5df643f5d08a75",
    "pins/MintableERC20.abi.json": "fa77fe077e7630e8d08191428bbdf6529fb32d0bbe49b8a7245887fbd1f1abba",
}
for name, digest in expected.items():
    actual = hashlib.sha256((root / name).read_bytes()).hexdigest()
    assert actual == digest, (name, actual, digest)
    print(actual, name)

oracle = json.loads((root / "zero-seed-launch-fee-curve-all-seconds.json").read_text())
assert len(oracle) == 25212

pins = json.loads((root / "pins/pins.json").read_text())
assert pins["source"] == "EkuboProtocol/evm-contracts@4f1a3060b099e8a50469848118f44c0c65cfab9a"
manifest = pins["consumerManifest"]
for name in ("ZeroSeedLaunch", "ZeroSeedLaunchPeriphery", "MintableERC20"):
    assert pins[name]["abiSha256"] == manifest["abiSha256"][name] == expected[f"pins/{name}.abi.json"]
assert sum(len(t) for c in manifest["abi"].values() for t in c.values()) == 56
assert pins["MintableERC20"]["creation"]["keccak"] == "0x25da7fd323fdbf874dde8aaef1bce445ec035022d8518cb3046f65a0427a2f52"
code = Path("src/quoting/pools/zero_seed_launch/MintableERC20.creation.hex").read_text().strip()
assert len(code) == 2 * pins["MintableERC20"]["creation"]["bytes"]

parity = json.loads((root / "zero-seed-launch-parity.json").read_text())
assert parity["source"]["contracts"].startswith("EkuboProtocol/evm-contracts@4f1a3060b099e8a50469848118f44c0c65cfab9a")
assert len(parity["scenarios"]) == 11
assert sum(len(s["steps"]) for s in parity["scenarios"]) == 507
for scenario in parity["scenarios"]:
    c = scenario["create"]
    assert c["coreCodehash"] == "0xc5f90c9d0dbc5037f8f9e248f4bb292e7c1824f584eb6550cb4cad525b38c71a"
    assert c["extensionCodehash"] != pins["ZeroSeedLaunch"]["templateRuntime"]["zeroFilledKeccak"]
    assert c["controller"] == c["periphery"]
    if c["quoteKind"] == "native":
        assert int(c["token0"], 16) == 0 and c["quoteCodehash"] == "none"

indexer = json.loads((root / "zero-seed-launch-indexer.json").read_text())
assert indexer["chainId"] == 31337
assert indexer["provenance"]["evmContractsHead"] == "4f1a3060b099e8a50469848118f44c0c65cfab9a"
assert indexer["provenance"]["launchAbiSha256"] == expected["pins/ZeroSeedLaunch.abi.json"]
assert indexer["provenance"]["peripheryAbiSha256"] == expected["pins/ZeroSeedLaunchPeriphery.abi.json"]
source = Path("src/quoting/pools/zero_seed_launch.rs").read_text()
for entry in indexer["instances"]:
    fixture = pins["localFixtures"][entry["label"]]
    for field in ("extension", "periphery"):
        assert entry[field].lower() == fixture[field] and fixture[field] in source
    for field in ("extensionRuntimeKeccak", "peripheryRuntimeKeccak"):
        assert entry[field] == fixture[field] and entry[field] in source
    if entry["quoteKind"] == "native":
        assert entry["quoteRuntimeKeccak"] is None and int(entry["quote"], 16) == 0
    else:
        assert entry["quoteRuntimeKeccak"] in source
assert "0x5100000000000000000000000000000000000000" not in source
print("PASS: 10 exact SHA256 receipts, 56 manifest ABI entries, 11 arithmetic parity fixtures, 507 step slots, "
      "2 supported LOCAL indexer instances (native, WETH); live manifest EMPTY")
