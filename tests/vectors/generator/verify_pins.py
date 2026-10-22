#!/usr/bin/env python3
"""Offline, exact source-pin receipts; run from the SDK root. No provider access."""
import hashlib
import json
from pathlib import Path

TARGET = "43d6628841b3ce91dafa048b7ceef64bed55fc8e"
root = Path("tests/vectors")
expected = {
    "zero-seed-launch.json": "8398d4189a6b1a434e17376276a7e218c9597408754a9920ce34a4872809a879",
    "zero-seed-launch-fee-decay-vectors.json": "7004b29f91540f1b29a568b525d215227565b36d1b490687ae604f5f145b835b",
    "zero-seed-launch-fee-curve-all-seconds.json": "fc9be5e4d59d8163f7a5566a7076bb9628d8ff30af5efde1eb554ba9b93bddce",
    "zero-seed-launch-fee-curve-rows.json": "7a86930ae16e5f8cc6730f33bc6f71915f5d3c1375fd7788593153de03b16d81",
    "zero-seed-launch-parity.json": "e799f4de8bbaf8653cc938b7d8f6b3552b5f0b3fcfdc2623b38996787a479cb0",
    "zero-seed-launch-indexer.json": "ec308953b8412e3ad76e7b6bf74b1e3ae56f6cbe0798032dbc6673bfedfae7d9",
    "pins/pins.json": "a2de05ae1bc5fc640fda4cf2930c8ba1e85c7cab5023db67dc6351408d97ec14",
    "zero-seed-launch-installation.json": "b06f6576e2280fa9851835655e899d3a21506bec317fa51af2d5a2efadbf330d",
    "pins/ZeroSeedLaunch.abi.json": "efae9388aa6b1342479204ddf436fd2a310df16bf06c80c990b2d22c90d1e41e",
    "pins/ZeroSeedLaunchPeriphery.abi.json": "df24d9f07d45323da7e46c0f6e64ce24f8f522442d60cb07880ddf742ebe7305",
    "pins/MintableERC20.abi.json": "fa77fe077e7630e8d08191428bbdf6529fb32d0bbe49b8a7245887fbd1f1abba",
}
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
assert sum(len(t) for c in manifest["abi"].values() for t in c.values()) == 91
assert "quoteToken()" not in manifest["abi"]["ZeroSeedLaunch"]["functions"]
assert manifest["removedFromAbi"] == {"FeeTooHigh()": "0xcd4e6167"}
assert all("0xcd4e6167" not in pins[n]["errors"].values() for n in ("ZeroSeedLaunch", "ZeroSeedLaunchPeriphery", "MintableERC20"))
assert manifest["maxCreatorFeeQ64"] == str(2**64 - 1)
vectors = json.loads((root / "zero-seed-launch.json").read_text())
assert vectors["version"] == 6 and vectors["fixture"]["max_creator_fee_q64"] == str(2**64 - 1)
assert vectors["creator_fee_range"] == manifest["creatorFeeRange"]
assert len(vectors["creator_fee_range"]["vectors"]) == 12 and len(vectors["max_rate"]["trades"]) == 16
assert "pub const ZERO_SEED_LAUNCH_MAX_CREATOR_FEE: u64 = u64::MAX;" in Path("src/quoting/pools/zero_seed_launch.rs").read_text()
assert "FeeTooHigh" not in Path("src/quoting/pools/zero_seed_launch.rs").read_text()
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
assert len(parity["previews"]) == len(parity["creations"]) == 145
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

indexer = json.loads((root / "zero-seed-launch-indexer.json").read_text())
assert indexer["chainId"] == 31337
assert indexer["provenance"]["evmContractsHead"] == TARGET
assert indexer["provenance"]["launchAbiSha256"] == expected["pins/ZeroSeedLaunch.abi.json"]
assert indexer["provenance"]["peripheryAbiSha256"] == expected["pins/ZeroSeedLaunchPeriphery.abi.json"]
assert indexer["provenance"]["coreRuntimeKeccak"] == fixture["coreRuntimeKeccak"]
(instance,) = indexer["instances"]
assert "quote" not in instance
for field in ("extension", "periphery"):
    assert instance[field].lower() == fixture[field]
for field in ("extensionRuntimeKeccak", "peripheryRuntimeKeccak", "extensionSalt", "peripherySalt"):
    assert instance[field] == fixture[field]
assert indexer["addresses"]["erc20Quote"].lower() == local_quote["quote"]
assert indexer["provenance"]["erc20QuoteRuntimeKeccak"] == local_quote["runtimeKeccak"]
kinds = []
for label, launch in indexer["launches"].items():
    kinds.append(launch["quoteKind"])
    assert launch["instance"] == instance["label"]
    if launch["quoteKind"] == "native":
        assert int(launch["quote"], 16) == 0 and launch["tokenIsToken1"]
    else:
        assert launch["quote"].lower() == local_quote["quote"]
    installation = indexer["installations"][label]
    assert int(installation["installedSupply"]) + int(installation["sinkSupply"]) == int(installation["requestedSupply"])
    assert installation["totalSupply"] == installation["requestedSupply"]
    assert installation["sinkBalance"] == installation["sinkSupply"]
    assert installation["coreInstalledDelta"] == installation["installedSupply"]
assert sorted(kinds) == ["erc20"] * 5 + ["native"] * 3
installation_vectors = json.loads((root / "zero-seed-launch-installation.json").read_text())
assert installation_vectors["pins"]["runtime"]["ZeroSeedLaunch"]["keccak256"] == fixture["extensionRuntimeKeccak"]
for label in ("l7", "l8"):
    installation = indexer["installations"][label]
    assert installation["liquidity"] != "0" and not indexer["launches"][label]["tokenIsToken1"]
assert indexer["installations"]["l8"]["sinkSupply"] == "0"
for label in ("l5", "l6"):
    (log,) = [l for b in indexer["branches"].values() for l in b["logs"]
              if l["topics"][:1] == ["0x3a4e811187f4a8c0b72396e9d7ca13aeed62eb97a599a24af1ed99066041098f"]
              and l["topics"][1] == indexer["launches"][label]["poolId"]]
    data = bytes.fromhex(log["data"][2:])
    p = int.from_bytes(data[160:192], "big") // 32
    assert int.from_bytes(data[32 * (p + 10):32 * (p + 11)], "big") == 2**64 - 1, label
print(f"PASS: {len(expected)} exact SHA256 receipts, 91 manifest ABI entries (FeeTooHigh removed), 13 parity scenarios, 522 step slots, "
      f"145 previews and creations, 1 supported LOCAL instance serving native and ERC-20 quotes, "
      f"1 reviewed LOCAL ERC-20 quote; live lists EMPTY; indexer receipt of the target: 1 instance, "
      f"{len(kinds)} launches (native and ERC-20)")
