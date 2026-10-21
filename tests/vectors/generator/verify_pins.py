#!/usr/bin/env python3
"""Offline, exact source-pin receipts; run from the SDK root. No provider access."""
import hashlib
import json
from pathlib import Path

TARGET = "40af6cb359b0de2f61f15e47b6622a00c48b5b08"
root = Path("tests/vectors")
expected = {
    "zero-seed-launch.json": "869408e73a94f74c3cbd9d92a1f41b24ef7593a16759759fd89abc6a3b6a4776",
    "zero-seed-launch-fee-decay-vectors.json": "7004b29f91540f1b29a568b525d215227565b36d1b490687ae604f5f145b835b",
    "zero-seed-launch-fee-curve-all-seconds.json": "fc9be5e4d59d8163f7a5566a7076bb9628d8ff30af5efde1eb554ba9b93bddce",
    "zero-seed-launch-fee-curve-rows.json": "96a8dbdee103f3da920fd2744e823e9469e118d20c478553e30cb029980988f2",
    "zero-seed-launch-parity.json": "198f8cfe38ecdd2e94804b4c06e2bf6bda499a47bb8b1523865f5d09c55be491",
    "pins/pins.json": "36f4467d21c662a06ebdaf1864057c085bd7b57cbe5e41229f21589499a16884",
    "pins/ZeroSeedLaunch.abi.json": "999068f8e41867e972f4485c0105f584a2c10d7537615e6b4517807548fcd4bf",
    "pins/ZeroSeedLaunchPeriphery.abi.json": "df24d9f07d45323da7e46c0f6e64ce24f8f522442d60cb07880ddf742ebe7305",
    "pins/MintableERC20.abi.json": "fa77fe077e7630e8d08191428bbdf6529fb32d0bbe49b8a7245887fbd1f1abba",
}
# The indexer receipt of the previous target, kept until the receipt of TARGET replaces it.
PREVIOUS_INDEXER_RECEIPT = "c4cea4e1d1accf56fcf7beb90743321cd6b1c4761e304651c3636dc9136d482b"
for name, digest in expected.items():
    actual = hashlib.sha256((root / name).read_bytes()).hexdigest()
    assert actual == digest, (name, actual, digest)
    print(actual, name)

oracle = json.loads((root / "zero-seed-launch-fee-curve-all-seconds.json").read_text())
assert len(oracle) == 25212

pins = json.loads((root / "pins/pins.json").read_text())
assert pins["source"] == f"EkuboProtocol/evm-contracts@{TARGET}"
manifest = pins["consumerManifest"]
assert manifest["frozenCommit"] == TARGET
for name in ("ZeroSeedLaunch", "ZeroSeedLaunchPeriphery", "MintableERC20"):
    assert pins[name]["abiSha256"] == manifest["abiSha256"][name] == expected[f"pins/{name}.abi.json"]
assert sum(len(t) for c in manifest["abi"].values() for t in c.values()) == 92
assert "quoteToken()" not in manifest["abi"]["ZeroSeedLaunch"]["functions"]
assert pins["MintableERC20"]["creation"]["keccak"] == "0x25da7fd323fdbf874dde8aaef1bce445ec035022d8518cb3046f65a0427a2f52"
code = Path("src/quoting/pools/zero_seed_launch/MintableERC20.creation.hex").read_text().strip()
assert len(code) == 2 * pins["MintableERC20"]["creation"]["bytes"]

source = Path("src/quoting/pools/zero_seed_launch.rs").read_text()
fixture = pins["localFixture"]
assert "quote" not in fixture
for field in ("extension", "periphery", "extensionRuntimeKeccak", "peripheryRuntimeKeccak", "coreRuntimeKeccak"):
    assert fixture[field] in source, field
(local_quote,) = pins["localQuotes"]
assert local_quote["chainId"] == 31337 and local_quote["runtimeKeccak"] in source
assert "LIVE_REVIEWED_QUOTES: [ReviewedQuote; 0] = []" in source
assert "0x5100000000000000000000000000000000000000" not in source.split("#[cfg(test)]")[0]

parity = json.loads((root / "zero-seed-launch-parity.json").read_text())
assert parity["source"]["contracts"].startswith(f"EkuboProtocol/evm-contracts@{TARGET}")
assert len(parity["scenarios"]) == 13
assert sum(len(s["steps"]) for s in parity["scenarios"]) == 522
assert len(parity["previews"]) == len(parity["creations"]) == 129
extensions = set()
for scenario in parity["scenarios"]:
    c = scenario["create"]
    assert c["coreCodehash"] == fixture["coreRuntimeKeccak"]
    assert c["extensionCodehash"] == fixture["extensionRuntimeKeccak"]
    assert c["controller"] == c["periphery"]
    assert int(c["supply"]) == int(c["requestedSupply"]) == int(c["totalSupply"])
    assert int(c["installedSupply"]) + int(c["sinkSupply"]) == int(c["requestedSupply"])
    assert int(c["balanceOfZero"]) == int(c["sinkSupply"])
    assert int(c["positionTokenDelta"]) == int(c["installedSupply"])
    if c["quoteKind"] == "native":
        assert int(c["token0"], 16) == 0 and int(c["quote"], 16) == 0 and c["quoteCodehash"] == "none"
    if scenario["name"].startswith("shared_"):
        extensions.add((c["extension"], c["periphery"], c["quoteKind"]))
assert len({(e, p) for e, p, _ in extensions}) == 1 and {k for _, _, k in extensions} == {"native", "erc20"}
for creation in parity["creations"]:
    if creation["ok"]:
        assert int(creation["totalSupply"]) == int(creation["requestedSupply"])
        assert int(creation["balanceOfZero"]) == int(creation["sinkSupply"])
        assert int(creation["installedSupply"]) + int(creation["sinkSupply"]) == int(creation["requestedSupply"])

receipt_path = root / "zero-seed-launch-indexer.json"
indexer = json.loads(receipt_path.read_text())
if indexer["provenance"]["evmContractsHead"] == TARGET:
    assert indexer["chainId"] == 31337
    assert indexer["provenance"]["launchAbiSha256"] == expected["pins/ZeroSeedLaunch.abi.json"]
    assert indexer["provenance"]["peripheryAbiSha256"] == expected["pins/ZeroSeedLaunchPeriphery.abi.json"]
    (instance,) = indexer["instances"]
    assert "quote" not in instance
    for field in ("extension", "periphery"):
        assert instance[field].lower() == fixture[field]
    for field in ("extensionRuntimeKeccak", "peripheryRuntimeKeccak"):
        assert instance[field] == fixture[field]
    kinds = set()
    for launch in indexer["launches"].values():
        kinds.add(launch["quoteKind"])
        if launch["quoteKind"] == "native":
            assert launch["quoteRuntimeKeccak"] is None and int(launch["quote"], 16) == 0
        else:
            assert launch["quote"].lower() == local_quote["quote"]
            assert launch["quoteRuntimeKeccak"] == local_quote["runtimeKeccak"]
    assert kinds == {"native", "erc20"}
    receipt = "indexer receipt of the target checked against the local fixture"
else:
    assert hashlib.sha256(receipt_path.read_bytes()).hexdigest() == PREVIOUS_INDEXER_RECEIPT
    receipt = "indexer receipt PENDING (previous target's receipt still in place)"
print(f"PASS: {len(expected)} exact SHA256 receipts, 92 manifest ABI entries, 13 parity scenarios, 522 step slots, "
      f"129 previews and creations, 1 supported LOCAL instance serving native and ERC-20 quotes, "
      f"1 reviewed LOCAL ERC-20 quote; live lists EMPTY; {receipt}")
