// SPDX-License-Identifier: ekubo-license-v1.eth
pragma solidity =0.8.33;

// Local fixture pin generator. Not part of evm-contracts: copied into a scratch copy of
// EkuboProtocol/evm-contracts@40af6cb359b0de2f61f15e47b6622a00c48b5b08 as test/extensions/ and run with
// `forge test --offline --match-contract ZeroSeedLaunchLocalFixturePins -vv`. It executes the deployment of the local
// anvil fixture (chain 31337, no fork): Core at its canonical address, ONE ZeroSeedLaunch `(core)` through the
// deterministic CREATE2 deployer at the first salt (counting up from 0) whose address carries the call-point byte, its
// ZeroSeedLaunchPeriphery `(core, extension)` at salt 0, and the plain 18-decimal test ERC-20 relocated to the top of
// the address space as the local ERC-20 quote. `pins_from_artifacts.py` reads the `PIN|` line.

import {Test} from "forge-std/Test.sol";
import {console2} from "forge-std/console2.sol";
import {zeroSeedLaunchCallPoints} from "../../src/extensions/ZeroSeedLaunch.sol";

contract ZeroSeedLaunchLocalFixturePinsTest is Test {
    address payable constant CORE = payable(0x00000000000014aA86C5d3c41765bb24e11bd701);
    address constant DETERMINISTIC_DEPLOYER = 0x4e59b44847b379578588920cA78FbF26c0B4956C;
    address constant LOCAL_QUOTE = address(type(uint160).max);

    function _deploy(bytes32 salt, bytes memory initCode) private returns (address deployed) {
        (bool ok, bytes memory out) = DETERMINISTIC_DEPLOYER.call(bytes.concat(salt, initCode));
        assertTrue(ok && out.length == 20, "CREATE2 deployment");
        deployed = address(bytes20(out));
    }

    function test_localFixturePins() public {
        assertGt(DETERMINISTIC_DEPLOYER.code.length, 0, "deterministic deployer");
        deployCodeTo("Core.sol:Core", CORE);
        uint8 callPoints = zeroSeedLaunchCallPoints().toUint8();

        bytes memory launchInit = bytes.concat(vm.getCode("ZeroSeedLaunch.sol:ZeroSeedLaunch"), abi.encode(CORE));
        bytes32 launchInitHash = keccak256(launchInit);
        uint256 i;
        address predicted;
        for (;; i++) {
            predicted = vm.computeCreate2Address(bytes32(i), launchInitHash, DETERMINISTIC_DEPLOYER);
            if (uint8(uint160(predicted) >> 152) == callPoints) break;
        }
        address extension = _deploy(bytes32(i), launchInit);
        assertEq(extension, predicted, "extension address");

        bytes memory peripheryInit = bytes.concat(
            vm.getCode("ZeroSeedLaunchPeriphery.sol:ZeroSeedLaunchPeriphery"), abi.encode(CORE, extension)
        );
        address periphery = _deploy(bytes32(0), peripheryInit);

        deployCodeTo("TestToken.sol:TestToken", abi.encode(address(this)), LOCAL_QUOTE);

        console2.log(
            string.concat(
                string.concat(
                    "PIN|core=",
                    vm.toString(CORE),
                    "|coreRuntimeKeccak=",
                    vm.toString(CORE.codehash),
                    "|deployer=",
                    vm.toString(DETERMINISTIC_DEPLOYER),
                    "|extension=",
                    vm.toString(extension),
                    "|extensionSalt=",
                    vm.toString(bytes32(i))
                ),
                string.concat(
                    "|extensionInitCodeKeccak=",
                    vm.toString(launchInitHash),
                    "|extensionRuntimeKeccak=",
                    vm.toString(extension.codehash),
                    "|periphery=",
                    vm.toString(periphery),
                    "|peripheryInitCodeKeccak=",
                    vm.toString(keccak256(peripheryInit)),
                    "|peripheryRuntimeKeccak=",
                    vm.toString(periphery.codehash)
                ),
                string.concat(
                    "|quote=", vm.toString(LOCAL_QUOTE), "|quoteRuntimeKeccak=", vm.toString(LOCAL_QUOTE.codehash)
                )
            )
        );
    }
}
