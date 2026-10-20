// SPDX-License-Identifier: ekubo-license-v1.eth
pragma solidity =0.8.33;

// SDK parity generator. Not part of evm-contracts: it is copied into a scratch copy of
// EkuboProtocol/evm-contracts@4f1a3060b099e8a50469848118f44c0c65cfab9a as test/extensions/, run with
// `forge test --offline --match-contract ZeroSeedLaunchSdkParity -vv`, and its `PARITY|` log lines are converted to
// JSON by `parity_to_json.py`. Launches are created through ZeroSeedLaunchPeriphery and every swap is a
// `Core.forward(extension, abi.encode(PoolKey, SwapParameters))` from the test locker of ZeroSeedLaunch.t.sol, which
// settles native ETH by value and ERC-20s by payFrom/withdraw. Every value it prints is read from the local Core,
// extension and periphery state or from their emitted events, never recomputed. Local fixture only.

import {Vm} from "forge-std/Vm.sol";
import {console2} from "forge-std/console2.sol";
import {ERC20} from "solady/tokens/ERC20.sol";
import {ICore} from "../../src/interfaces/ICore.sol";
import {IZeroSeedLaunch} from "../../src/interfaces/extensions/IZeroSeedLaunch.sol";
import {CoreLib} from "../../src/libraries/CoreLib.sol";
import {PoolKey} from "../../src/types/poolKey.sol";
import {PoolState} from "../../src/types/poolState.sol";
import {PositionId} from "../../src/types/positionId.sol";
import {PoolBalanceUpdate} from "../../src/types/poolBalanceUpdate.sol";
import {createSwapParameters} from "../../src/types/swapParameters.sol";
import {SqrtRatio, toSqrtRatio} from "../../src/types/sqrtRatio.sol";
import {tickToSqrtRatio} from "../../src/math/ticks.sol";
import {MIN_SQRT_RATIO, MAX_SQRT_RATIO} from "../../src/types/sqrtRatio.sol";
import {NATIVE_TOKEN_ADDRESS} from "../../src/math/constants.sol";
import {MAX_CREATOR_FEE} from "../../src/extensions/ZeroSeedLaunch.sol";
import {MintableERC20} from "../../src/MintableERC20.sol";
import {ZeroSeedLaunchBase} from "./ZeroSeedLaunch.t.sol";

contract ZeroSeedLaunchSdkParityTest is ZeroSeedLaunchBase {
    using CoreLib for ICore;

    bytes32 constant CORE_CODEHASH = 0xc5f90c9d0dbc5037f8f9e248f4bb292e7c1824f584eb6550cb4cad525b38c71a;
    bytes32 constant LAUNCH_CREATED = keccak256(
        "LaunchCreated(bytes32,address,address,(address,address,bytes32),bytes32,uint128,(string,string,uint8,uint128,uint128,int32,int32,uint32,uint64,uint32,uint64,uint64,bytes32))"
    );
    bytes32 constant LAUNCH_SWAPPED = keccak256("LaunchSwapped(bytes32,address,int128,int128,uint64,uint128,bool)");
    bytes32 constant CREATOR_FEES_CLAIMED = keccak256("CreatorFeesClaimed(bytes32,address,uint128,uint128)");
    bytes32 constant LAUNCH_OWNER_CHANGED = keccak256("LaunchOwnerChanged(bytes32,address,address)");
    bytes32 constant LAUNCH_FEES_CLAIMED = keccak256("LaunchFeesClaimed(bytes32,address,address,uint128,uint128)");

    struct Ctx {
        string tag;
        PoolKey key;
        address token;
        address quote;
        bool tokenIs1;
        uint256 i;
        uint256 unit;
    }

    function _s(uint256 v) private pure returns (string memory) {
        return vm.toString(v);
    }

    function _i(int256 v) private pure returns (string memory) {
        return vm.toString(v);
    }

    function _state(PoolKey memory key) private view returns (string memory) {
        PoolState st = ICore(CORE).poolState(key.toPoolId());
        return string.concat(_s(st.sqrtRatio().toFixed()), ",", _i(st.tick()), ",", _s(st.liquidity()));
    }

    function _fees(PoolKey memory key) private view returns (uint128 a, uint128 b) {
        (a, b) = launch.creatorFees(key);
    }

    /// @dev Core's and the test account's balances of token0 and token1. For native ETH the test account is this
    /// contract plus the swapper that pays its ETH debts (`_balance`).
    function _balances(Ctx memory c) private view returns (string memory) {
        return string.concat(
            _s(_balance(c.key.token0, CORE)),
            ",",
            _s(_balance(c.key.token1, CORE)),
            ",",
            _s(_balance(c.key.token0, address(this))),
            ",",
            _s(_balance(c.key.token1, address(this)))
        );
    }

    /// @dev One forwarded swap at `ts`. `specifiedIs1` and `amount` are Core's SwapParameters; `limit` is fixed point,
    /// 0 for the default.
    function _step(Ctx memory c, string memory label, uint256 ts, bool specifiedIs1, int128 amount, uint256 limit)
        private
        returns (bool ok, PoolBalanceUpdate u)
    {
        vm.warp(ts);
        string memory pre = _state(c.key);
        (uint128 f0, uint128 f1) = _fees(c.key);
        SqrtRatio lim = limit == 0 ? SqrtRatio.wrap(0) : toSqrtRatio(limit, false);
        vm.recordLogs();
        string memory head = string.concat(
            "PARITY|step|",
            c.tag,
            "|i=",
            _s(c.i++),
            "|label=",
            label,
            "|ts=",
            _s(ts),
            "|specifiedIs1=",
            specifiedIs1 ? "1" : "0",
            "|amount=",
            _i(amount),
            "|limit=",
            _s(limit == 0 ? 0 : lim.toFixed()),
            "|heldToken=",
            _s(_held(c)),
            "|tokenAllowance=",
            _s(ERC20(c.token).allowance(address(this), address(swapper))),
            "|heldQuote=",
            _s(_balance(c.quote, address(this))),
            "|coreQuote=",
            _s(_balance(c.quote, CORE)),
            "|pre=",
            pre,
            "|preBalances=",
            _balances(c)
        );
        uint256 gas = gasleft();
        try swapper.forwardSwap(c.key, createSwapParameters(lim, amount, specifiedIs1, 0)) returns (
            PoolBalanceUpdate r
        ) {
            gas -= gasleft();
            ok = true;
            u = r;
        } catch (bytes memory err) {
            vm.getRecordedLogs();
            console2.log(
                string.concat(
                    head, "|ok=0|err=", vm.toString(err), "|post=", _state(c.key), "|postBalances=", _balances(c)
                )
            );
            return (false, u);
        }
        console2.log(string.concat(head, _tail(c, ts, u, f0, f1), "|gas=", _s(gas)));
    }

    function _event() private returns (string memory ev) {
        Vm.Log[] memory logs = vm.getRecordedLogs();
        ev = "none";
        for (uint256 k; k < logs.length; k++) {
            if (logs[k].emitter == address(launch) && logs[k].topics.length > 0 && logs[k].topics[0] == LAUNCH_SWAPPED)
            {
                (int128 d0, int128 d1, uint64 rate, uint128 feeAmount, bool feeIs1) =
                    abi.decode(logs[k].data, (int128, int128, uint64, uint128, bool));
                ev = string.concat(_i(d0), ",", _i(d1), ",", _s(rate), ",", _s(feeAmount), ",", feeIs1 ? "1" : "0");
            }
        }
    }

    function _tail(Ctx memory c, uint256 ts, PoolBalanceUpdate u, uint128 f0, uint128 f1)
        private
        returns (string memory)
    {
        string memory ev = _event();
        (uint128 g0, uint128 g1) = _fees(c.key);
        return string.concat(
            "|ok=1|d0=",
            _i(u.delta0()),
            "|d1=",
            _i(u.delta1()),
            "|ledger=",
            _s(g0 - f0),
            ",",
            _s(g1 - f1),
            "|feeAt=",
            _s(launch.feeAt(c.key.toPoolId(), ts)),
            "|event=",
            ev,
            "|post=",
            _state(c.key),
            "|postBalances=",
            _balances(c)
        );
    }

    function _buy(Ctx memory c, string memory label, uint256 ts, int128 amount, bool exactOut, uint256 limit)
        private
        returns (bool, PoolBalanceUpdate)
    {
        return _step(c, label, ts, exactOut ? c.tokenIs1 : !c.tokenIs1, exactOut ? -amount : amount, limit);
    }

    function _sell(Ctx memory c, string memory label, uint256 ts, int128 amount, bool exactOut, uint256 limit)
        private
        returns (bool, PoolBalanceUpdate)
    {
        return _step(c, label, ts, exactOut ? !c.tokenIs1 : c.tokenIs1, exactOut ? -amount : amount, limit);
    }

    function _held(Ctx memory c) private view returns (uint256) {
        return ERC20(c.token).balanceOf(address(this));
    }

    function _scenario(bool tokenIs0, uint8 quoteDecimals, uint32 duration) private {
        vm.recordLogs();
        (IZeroSeedLaunch.Installation memory inst, IZeroSeedLaunch.LaunchParameters memory p) =
            _create(tokenIs0, quoteDecimals, duration);
        Ctx memory c = _logCreate(
            string.concat("scenario=", tokenIs0 ? "t0" : "t1", "_18_", _s(quoteDecimals), "_", _s(duration)),
            inst,
            p,
            quoteDecimals
        );
        _program(c, inst, duration);
    }

    /// @dev The same program from a high initial rate (study values, not selected parameters).
    function _highRateScenario(
        bool tokenIs0,
        uint8 quoteDecimals,
        uint32 duration,
        uint64 initialFee,
        string memory name
    ) private {
        _quote(tokenIs0, quoteDecimals);
        IZeroSeedLaunch.LaunchParameters memory p =
            _parameters(quoteDecimals == 18 ? ASK_18_18 : ASK_18_6, REQUESTED_SUPPLY, duration);
        p.initialFee = initialFee;
        _bind(p, creator);
        vm.recordLogs();
        vm.prank(creator);
        IZeroSeedLaunch.Installation memory inst = periphery.create(p);
        MintableERC20(inst.token).approve(address(swapper), type(uint256).max);
        Ctx memory c = _logCreate(
            string.concat("scenario=", tokenIs0 ? "t0" : "t1", "_18_", _s(quoteDecimals), "_", _s(duration), "_", name),
            inst,
            p,
            quoteDecimals
        );
        _program(c, inst, duration);
    }

    function _owner(Vm.Log[] memory logs) private view returns (address owner) {
        for (uint256 k; k < logs.length; k++) {
            if (
                logs[k].emitter == address(periphery) && logs[k].topics.length == 4
                    && logs[k].topics[0] == LAUNCH_OWNER_CHANGED
            ) {
                assertEq(logs[k].topics[2], bytes32(0), "created from the zero owner");
                owner = address(uint160(uint256(logs[k].topics[3])));
            }
        }
        assertEq(owner, creator, "owner of record");
    }

    function _logCreate(
        string memory tag,
        IZeroSeedLaunch.Installation memory inst,
        IZeroSeedLaunch.LaunchParameters memory p,
        uint8 quoteDecimals
    ) private returns (Ctx memory c) {
        assertEq(CORE.codehash, CORE_CODEHASH, "local Core == Base Core runtime");
        Vm.Log[] memory logs = vm.getRecordedLogs();
        bool tokenIs0 = inst.poolKey.token0 == inst.token;
        c.tag = tag;
        c.key = inst.poolKey;
        c.token = inst.token;
        c.quote = activeQuote;
        c.tokenIs1 = !tokenIs0;
        c.unit = 10 ** quoteDecimals;
        address owner = _owner(logs);

        // Pool construction inputs, from the emitted LaunchCreated event and Core state only.
        bool found;
        for (uint256 k; k < logs.length; k++) {
            if (logs[k].emitter == address(launch) && logs[k].topics.length > 0 && logs[k].topics[0] == LAUNCH_CREATED)
            {
                (PoolKey memory key, PositionId pos, uint128 liquidity, IZeroSeedLaunch.LaunchParameters memory ep) =
                    abi.decode(logs[k].data, (PoolKey, PositionId, uint128, IZeroSeedLaunch.LaunchParameters));
                found = true;
                console2.log(
                    string.concat(
                        "PARITY|create|",
                        c.tag,
                        "|token0=",
                        vm.toString(key.token0),
                        "|token1=",
                        vm.toString(key.token1),
                        "|extension=",
                        vm.toString(key.config.extension()),
                        "|fee=",
                        _s(key.config.fee()),
                        "|tickSpacing=",
                        _s(key.config.concentratedTickSpacing()),
                        "|token=",
                        vm.toString(address(uint160(uint256(logs[k].topics[2])))),
                        "|controller=",
                        vm.toString(address(uint160(uint256(logs[k].topics[3])))),
                        string.concat(
                            "|owner=",
                            vm.toString(owner),
                            "|periphery=",
                            vm.toString(address(periphery)),
                            "|name=",
                            ep.name,
                            "|symbol=",
                            ep.symbol,
                            "|decimals=",
                            _s(ep.decimals),
                            "|userSalt=",
                            vm.toString(p.salt),
                            "|extensionSalt=",
                            vm.toString(ep.salt),
                            "|tickLower=",
                            _i(pos.tickLower()),
                            "|tickUpper=",
                            _i(pos.tickUpper())
                        ),
                        string.concat(
                            "|liquidity=",
                            _s(liquidity),
                            "|supply=",
                            _s(ep.supply),
                            "|askTick=",
                            _i(ep.askTick),
                            "|upperTick=",
                            _i(ep.upperTick),
                            "|tradingStart=",
                            _s(ep.tradingStart),
                            "|feeDuration=",
                            _s(ep.feeDuration),
                            "|initialFee=",
                            _s(ep.initialFee),
                            "|finalFee=",
                            _s(ep.finalFee),
                            "|quoteDecimals=",
                            _s(quoteDecimals),
                            "|state=",
                            _state(key)
                        ),
                        string.concat(
                            "|coreCodehash=",
                            vm.toString(CORE.codehash),
                            "|extensionCodehash=",
                            vm.toString(address(launch).codehash),
                            "|peripheryCodehash=",
                            vm.toString(address(periphery).codehash),
                            "|constructorQuote=",
                            vm.toString(launch.quoteToken()),
                            "|quoteKind=",
                            activeQuote == NATIVE_TOKEN_ADDRESS ? "native" : "erc20",
                            "|quoteCodehash=",
                            activeQuote == NATIVE_TOKEN_ADDRESS ? "none" : vm.toString(activeQuote.codehash),
                            "|createTs=",
                            _s(block.timestamp)
                        )
                    )
                );
            }
        }
        assertTrue(found, "LaunchCreated");
    }

    /// @dev The owner claims through the periphery to this contract. Logs the ledger read before, the periphery's
    /// return values and both claim events of the same transaction.
    function _claim(Ctx memory c) private {
        (uint128 l0, uint128 l1) = _fees(c.key);
        vm.recordLogs();
        vm.prank(creator);
        (uint128 r0, uint128 r1) = periphery.claimFees(c.key, address(this));
        Vm.Log[] memory logs = vm.getRecordedLogs();
        string memory extensionEvent = "none";
        string memory peripheryEvent = "none";
        for (uint256 k; k < logs.length; k++) {
            if (logs[k].topics.length == 0) continue;
            if (logs[k].emitter == address(launch) && logs[k].topics[0] == CREATOR_FEES_CLAIMED) {
                assertEq(address(uint160(uint256(logs[k].topics[2]))), address(periphery), "controller");
                (uint128 a0, uint128 a1) = abi.decode(logs[k].data, (uint128, uint128));
                extensionEvent = string.concat(_s(a0), ",", _s(a1));
            }
            if (logs[k].emitter == address(periphery) && logs[k].topics[0] == LAUNCH_FEES_CLAIMED) {
                assertEq(address(uint160(uint256(logs[k].topics[2]))), creator, "owner");
                assertEq(address(uint160(uint256(logs[k].topics[3]))), address(this), "recipient");
                (uint128 a0, uint128 a1) = abi.decode(logs[k].data, (uint128, uint128));
                peripheryEvent = string.concat(_s(a0), ",", _s(a1));
            }
        }
        (uint128 a0, uint128 a1) = _fees(c.key);
        console2.log(
            string.concat(
                string.concat("PARITY|claim|", c.tag, "|amount0=", _s(l0), "|amount1=", _s(l1)),
                string.concat("|returned=", _s(r0), ",", _s(r1), "|ledgerAfter=", _s(a0), ",", _s(a1)),
                string.concat("|extensionEvent=", extensionEvent, "|peripheryEvent=", peripheryEvent),
                string.concat("|post=", _state(c.key))
            )
        );
    }

    function _program(Ctx memory c, IZeroSeedLaunch.Installation memory inst, uint32 duration) private {
        bool tokenIs0 = !c.tokenIs1;

        // Before the start: TradingNotStarted.
        _buy(c, "beforeStart", START - 1, int128(uint128(c.unit)), false, 0);
        // At the start with no buyer: no bid.
        _sell(c, "noBidSellExactIn", START, 1e18, false, 0);
        _sell(c, "noBidSellExactOut", START, 1, true, 0);
        _buy(c, "zeroAmount", START, 0, false, 0);
        (, PoolBalanceUpdate u) = _buy(c, "buyExactIn", START, int128(uint128(c.unit)), false, 0);
        int128 net = c.tokenIs1 ? -u.delta1() : -u.delta0();
        _buy(c, "buyExactOut", START, net, true, 0);
        _buy(c, "dustBuyExactIn", START + 1, 1, false, 0);
        _buy(c, "dustBuyExactOut", START + 1, 1, true, 0);
        _sell(c, "dustSellExactIn", START + 1, 1, false, 0);
        _sell(c, "dustSellExactOut", START + 1, 1, true, 0);

        // Explicit limits: inside the range, beyond the bounds (clamped) and in the wrong direction.
        int32 mid = (inst.positionId.tickLower() + inst.positionId.tickUpper()) / 2;
        mid -= mid % int32(SPACING);
        uint256 midRatio = tickToSqrtRatio(mid).toFixed();
        _buy(c, "buyToMidLimit", START + duration / 2, int128(uint128(c.unit)) * 1_000_000, false, midRatio);
        _buy(
            c,
            "buyWrongDirection",
            START + duration / 2,
            int128(uint128(c.unit)),
            false,
            tokenIs0 ? MIN_SQRT_RATIO.toFixed() : MAX_SQRT_RATIO.toFixed()
        );
        _sell(c, "sellHalfExactIn", START + duration - 1, int128(uint128(_held(c) / 2)), false, 0);
        _sell(c, "sellExactOutQuote", START + duration, int128(uint128(c.unit / 10)), true, 0);
        _buy(c, "buyExactInEndPlus1", START + duration + 1, int128(uint128(c.unit)), false, 0);

        // Pseudo-random sequence across the schedule.
        uint256 seed = uint256(keccak256(abi.encode(c.tag)));
        uint256 ts = START + duration + 1;
        for (uint256 k; k < 24; k++) {
            seed = uint256(keccak256(abi.encode(seed, k)));
            ts += seed % 400;
            uint256 op = (seed >> 16) % 4;
            uint256 size = (seed >> 32) % (c.unit * 1000) + 1;
            if (op == 0) {
                _buy(c, "randBuyExactIn", ts, int128(uint128(size)), false, 0);
            } else if (op == 1) {
                _buy(c, "randBuyExactOut", ts, int128(uint128(((seed >> 96) % 1e26) + 1)), true, 0);
            } else {
                uint256 held = _held(c);
                if (held == 0) continue;
                if (op == 2) {
                    _sell(c, "randSellExactIn", ts, int128(uint128((seed >> 96) % held + 1)), false, 0);
                } else {
                    _sell(c, "randSellExactOut", ts, int128(uint128(size / 7 + 1)), true, 0);
                }
            }
        }

        // Upper bound: an exact-input buy beyond inventory fills partially, then an exact-output one fills nothing.
        _buy(c, "exhaustExactIn", ts, int128(uint128(c.unit)) * 1e9, false, 0);
        _buy(c, "afterUpperExactOut", ts, 1e18, true, 0);
        _buy(c, "afterUpperExactIn", ts, int128(uint128(c.unit)), false, 0);
        // Leave the upper bound, re-enter it with an exact-output buy beyond inventory, then return to the ask.
        _sell(c, "sellFromUpper", ts + 1, int128(uint128(_held(c) / 3)), false, 0);
        _buy(c, "exhaustExactOut", ts + 2, int128(uint128(REQUESTED_SUPPLY)), true, 0);
        _sell(
            c,
            "sellBeyondLowerLimit",
            ts + 3,
            int128(uint128(_held(c) / 2)),
            false,
            tokenIs0 ? MIN_SQRT_RATIO.toFixed() : MAX_SQRT_RATIO.toFixed()
        );
        _sell(c, "sellAllExactIn", ts + 3, int128(uint128(_held(c))), false, 0);
        // The owner claims the fee ledger through the periphery and sells the token side too: the price returns to
        // the ask.
        _claim(c);
        _sell(c, "sellClaimedExactIn", ts + 4, int128(uint128(_held(c))), false, 0);
        _sell(c, "sellAtAskExactIn", ts + 4, 1e18, false, 0);
        _sell(c, "sellAtAskExactOut", ts + 4, 1, true, 0);
        _buy(c, "farFutureBuy", START + 10 * 365 days, int128(uint128(c.unit)), false, 0);
    }

    function test_parity_t0_18_18() public {
        _scenario(true, 18, DURATION);
    }

    function test_parity_t1_18_18_native() public {
        _scenario(false, 18, DURATION);
    }

    function test_parity_t0_18_6() public {
        _scenario(true, 6, DURATION);
    }

    function test_parity_t1_18_6() public {
        _scenario(false, 6, DURATION);
    }

    function test_parity_t0_18_18_600() public {
        _scenario(true, 18, DURATION_SHORT);
    }

    function test_parity_t1_18_18_600_native() public {
        _scenario(false, 18, DURATION_SHORT);
    }

    function test_parity_t1_18_6_600() public {
        _scenario(false, 6, DURATION_SHORT);
    }

    function test_parity_t0_18_18_3600_rate50() public {
        _highRateScenario(true, 18, DURATION, 9223372036854775808, "rate50");
    }

    function test_parity_t1_18_18_3600_rate50_native() public {
        _highRateScenario(false, 18, DURATION, 9223372036854775808, "rate50");
    }

    function test_parity_t1_18_6_600_rate99() public {
        _highRateScenario(false, 6, DURATION_SHORT, MAX_CREATOR_FEE, "rate99");
    }

    /// @dev A launch near the top of the price range, where one raw token costs about int128.max raw quote.
    function test_parity_overflow() public {
        _quote(true, 18);
        IZeroSeedLaunch.LaunchParameters memory p = _parameters(88_000_000, 1_000_000, DURATION);
        p.upperTick = 88_722_800;
        _bind(p, creator);
        vm.recordLogs();
        vm.prank(creator);
        IZeroSeedLaunch.Installation memory inst = periphery.create(p);
        Ctx memory c = _logCreate("scenario=overflow_t0_18_18_3600", inst, p, 18);
        _buy(c, "buyOneTokenExactOut", START, 1, true, 0);
        _buy(c, "buyTwoTokensExactOut", START, 2, true, 0);
        _buy(c, "buyMaxExactIn", START, type(int128).max, false, 0);
        _buy(c, "buyHalfMaxExactIn", START, type(int128).max / 2, false, 0);
        _buy(c, "buyOneTokenExactOutFinalFee", START + DURATION, 1, true, 0);
        _sell(c, "sellOneTokenExactIn", START + DURATION, 1, false, 0);
        _sell(c, "sellExactOutMax", START + DURATION, type(int128).max, true, 0);
    }

    // ---- Installation preview and binding, read from the periphery's previewInstallation and create reverts. ----

    function _logPreview(string memory label, IZeroSeedLaunch.LaunchParameters memory p) private {
        string memory head = string.concat(
            "PARITY|preview|label=",
            label,
            "|quote=",
            vm.toString(activeQuote),
            "|supply=",
            _s(p.supply),
            "|askTick=",
            _i(p.askTick),
            "|upperTick=",
            _i(p.upperTick),
            "|tickSpacing=",
            _s(p.tickSpacing),
            string.concat(
                "|tradingStart=",
                _s(p.tradingStart),
                "|feeDuration=",
                _s(p.feeDuration),
                "|initialFee=",
                _s(p.initialFee),
                "|finalFee=",
                _s(p.finalFee),
                "|now=",
                _s(block.timestamp)
            )
        );
        try periphery.previewInstallation(creator, p) returns (IZeroSeedLaunch.Installation memory inst) {
            console2.log(
                string.concat(
                    head,
                    "|ok=1|token=",
                    vm.toString(inst.token),
                    "|token0=",
                    vm.toString(inst.poolKey.token0),
                    "|tickLower=",
                    _i(inst.positionId.tickLower()),
                    "|tickUpper=",
                    _i(inst.positionId.tickUpper()),
                    "|initialTick=",
                    _i(inst.initialTick),
                    "|liquidity=",
                    _s(inst.liquidity),
                    "|installedSupply=",
                    _s(inst.installedSupply)
                )
            );
            _logBinding(label, p, inst);
        } catch (bytes memory err) {
            console2.log(string.concat(head, "|ok=0|err=", vm.toString(err)));
        }
    }

    /// @dev create with the preview's supply and liquidity L-1, L+1, and with supply+1: the revert data carries the
    /// installable amount for that liquidity.
    function _logBinding(
        string memory label,
        IZeroSeedLaunch.LaunchParameters memory p,
        IZeroSeedLaunch.Installation memory inst
    ) private {
        int256[3] memory dl = [int256(-1), int256(1), int256(0)];
        for (uint256 k; k < 3; k++) {
            IZeroSeedLaunch.LaunchParameters memory q = _clone(p);
            q.supply = inst.installedSupply + (k == 2 ? 1 : 0);
            q.liquidity = uint128(uint256(int256(uint256(inst.liquidity)) + dl[k]));
            uint256 snap = vm.snapshotState();
            vm.prank(creator);
            string memory out;
            try periphery.create(q) returns (IZeroSeedLaunch.Installation memory) {
                out = "ok=1";
            } catch (bytes memory err) {
                out = string.concat("ok=0|err=", vm.toString(err));
            }
            vm.revertToState(snap);
            console2.log(
                string.concat(
                    "PARITY|binding|label=", label, "|supply=", _s(q.supply), "|liquidity=", _s(q.liquidity), "|", out
                )
            );
        }
        // The exact pair succeeds.
        IZeroSeedLaunch.LaunchParameters memory e = _clone(p);
        e.supply = inst.installedSupply;
        e.liquidity = inst.liquidity;
        uint256 snap2 = vm.snapshotState();
        vm.prank(creator);
        IZeroSeedLaunch.Installation memory made = periphery.create(e);
        assertEq(made.liquidity, inst.liquidity);
        assertEq(made.installedSupply, inst.installedSupply);
        assertEq(made.token, inst.token);
        vm.revertToState(snap2);
        console2.log(
            string.concat(
                "PARITY|binding|label=", label, "|supply=", _s(e.supply), "|liquidity=", _s(e.liquidity), "|ok=1"
            )
        );
    }

    function _clone(IZeroSeedLaunch.LaunchParameters memory p)
        private
        pure
        returns (IZeroSeedLaunch.LaunchParameters memory q)
    {
        q = abi.decode(abi.encode(p), (IZeroSeedLaunch.LaunchParameters));
    }

    function test_parity_preview() public {
        for (uint256 order; order < 2; order++) {
            uint256 snap = vm.snapshotState();
            bool tokenIs0 = order == 0;
            string memory o = tokenIs0 ? "t0" : "t1";
            for (uint256 d; d < 2; d++) {
                uint8 dec = d == 0 ? 18 : 6;
                _quote(tokenIs0, dec);
                string memory g = string.concat(o, "_18_", _s(dec));
                int32 ask = dec == 18 ? ASK_18_18 : ASK_18_6;
                IZeroSeedLaunch.LaunchParameters memory p = _parameters(ask, REQUESTED_SUPPLY, DURATION);
                _logPreview(string.concat(g, "_frozen"), p);
                uint128[6] memory supplies = [
                    uint128(1),
                    uint128(1000),
                    uint128(1e18),
                    uint128(123_456_789_012_345_678_901_234_567),
                    uint128(REQUESTED_SUPPLY - 1),
                    uint128(type(int128).max)
                ];
                for (uint256 k; k < supplies.length; k++) {
                    IZeroSeedLaunch.LaunchParameters memory q = _clone(p);
                    q.supply = supplies[k];
                    _logPreview(string.concat(g, "_supply", _s(k)), q);
                }
                // Narrow range, spacing 1; widest spacing; a range ending at the tick bounds.
                IZeroSeedLaunch.LaunchParameters memory r = _clone(p);
                r.tickSpacing = 1;
                r.upperTick = ask + 600;
                _logPreview(string.concat(g, "_narrow1"), r);
                r = _clone(p);
                r.tickSpacing = 698605;
                r.askTick = -698605 * 60;
                r.upperTick = -698605 * 50;
                _logPreview(string.concat(g, "_maxSpacing"), r);
                r = _clone(p);
                r.askTick = -88722800;
                r.upperTick = -88722800 + WIDTH;
                _logPreview(string.concat(g, "_nearMinTick"), r);
                r = _clone(p);
                r.askTick = 88722800 - WIDTH;
                r.upperTick = 88722800;
                _logPreview(string.concat(g, "_nearMaxTick"), r);
                // Refusals.
                r = _clone(p);
                r.supply = 0;
                _logPreview(string.concat(g, "_zeroSupply"), r);
                r = _clone(p);
                r.supply = uint128(type(int128).max) + 1;
                _logPreview(string.concat(g, "_supplyAboveInt128"), r);
                r = _clone(p);
                r.tickSpacing = 0;
                _logPreview(string.concat(g, "_spacing0"), r);
                r = _clone(p);
                r.tickSpacing = 698606;
                _logPreview(string.concat(g, "_spacingTooHigh"), r);
                r = _clone(p);
                r.upperTick = r.askTick;
                _logPreview(string.concat(g, "_emptyRange"), r);
                r = _clone(p);
                r.askTick = -88722836;
                _logPreview(string.concat(g, "_askBelowMin"), r);
                r = _clone(p);
                r.upperTick = 88722836;
                _logPreview(string.concat(g, "_upperAboveMax"), r);
                r = _clone(p);
                r.askTick += 1;
                _logPreview(string.concat(g, "_misaligned"), r);
                r = _clone(p);
                r.initialFee = MAX_CREATOR_FEE + 1;
                r.finalFee = 0;
                _logPreview(string.concat(g, "_feeTooHigh"), r);
                r = _clone(p);
                r.initialFee = MAX_CREATOR_FEE;
                r.finalFee = MAX_CREATOR_FEE;
                _logPreview(string.concat(g, "_feeAtCap"), r);
                r = _clone(p);
                r.finalFee = r.initialFee + 1;
                _logPreview(string.concat(g, "_finalAboveInitial"), r);
                r = _clone(p);
                r.feeDuration = 0;
                _logPreview(string.concat(g, "_duration0"), r);
                r = _clone(p);
                r.feeDuration = type(uint32).max;
                _logPreview(string.concat(g, "_durationMax"), r);
                r = _clone(p);
                r.initialFee = type(uint64).max;
                _logPreview(string.concat(g, "_feeMaxEncodable"), r);
                r = _clone(p);
                r.tradingStart = uint64(block.timestamp - 1);
                _logPreview(string.concat(g, "_startInPast"), r);
                r = _clone(p);
                r.tradingStart = uint64(block.timestamp);
                _logPreview(string.concat(g, "_startNow"), r);
            }
            vm.revertToState(snap);
        }
    }
}
