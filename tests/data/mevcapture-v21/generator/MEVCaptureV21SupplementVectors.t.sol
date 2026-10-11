// SPDX-License-Identifier: ekubo-license-v1.eth
pragma solidity =0.8.33;

import {MEVCaptureV21SwapVectorsTest} from "./MEVCaptureV21SwapVectors.t.sol";
import {V21Ref} from "./MEVCaptureV21Helpers.sol";
import {SqrtRatio} from "../../src/types/sqrtRatio.sol";

/// @notice EKU-1577 supplementary SDK parity vectors, generated from the unmodified merged contract
///   da368348238a46857d39b6db57bdb2b432c979df. Every swap is still checked against the reference twin.
///   Covers what swaps.json does not: Core word-boundary step splits with liquidity, user minFee on away
///   segments, the post-swap refresh raise and its same-timestamp position suppression, and a nondefault
///   getConfig tuple.
contract MEVCaptureV21SupplementVectorsTest is MEVCaptureV21SwapVectorsTest {
    function _header(string memory config) internal {
        out = string.concat(
            '{"spec":"EKU-1577 supplement; src/extensions/MEVCaptureV21.sol at da368348238a46857d39b6db57bdb2b432c979df",',
            '"config":',
            config,
            ",",
            '"note":"same format as swaps.json",',
            '"scenarios":[\n'
        );
    }

    function _buildDefault() internal returns (string memory) {
        _header(
            '{"halfLife":"120","slopeK":"4","segmentExp":"0","jLin":"16","maxFee":"32768","clampTicks":"2500","mGate":"3","maxSegments":"40"}'
        );
        uint256 t0 = vm.getBlockTimestamp();

        _begin("word_boundary_splits_spacing1", 196, 0, 0);
        _pos(bytes24(uint192(1)), -100_000, 100_000, L66);
        _swap(true, BIG, _at(3000), 0); // capped call crosses ~12 words of 256 ticks with liquidity
        _swap(true, -1e19, _at(-3000), 0); // exact out, decreasing across words
        _swap(false, 5e18, SqrtRatio.wrap(0), 0); // exact in, decreasing
        _end(false);

        vm.warp(t0 + 1000);
        _begin("user_min_fee_on_away_segments", 196, 12, 0);
        _pos(bytes24(uint192(1)), -40 * S, 40 * S, L66);
        _swap(true, BIG, _at(3 * S), 1000); // away fees 392, 784, 1176 -> 1000, 1000, 1176
        _swap(false, BIG, _at(-2 * S), 2000); // toward at the user minFee, then away
        _end(false);

        vm.warp(t0 + 2000);
        _begin("refresh_raise_and_position_suppression", 196, 12, 0);
        _pos(bytes24(uint192(1)), -40 * S, 2 * S, 1);
        _pos(bytes24(uint192(2)), 2 * S, 40 * S, L66);
        vm.warp(t0 + 2200);
        _swap(false, 1, SqrtRatio.wrap(0), 0); // first touch raises the reference to 1 bit
        vm.warp(t0 + 2400);
        _swap(true, BIG, _at(3 * S), 0); // no raise at first touch; refresh raises from the liquidity after
        vm.warp(t0 + 2600);
        _pos(bytes24(uint192(3)), -S, S, 1);
        _swap(false, BIG, _at(S), 0); // a position in this timestamp suppresses the refresh
        _swap(true, BIG, _at(5 * S), 0);
        _end(true);

        return string.concat(out, "\n]}\n");
    }

    function _buildNondefault() internal returns (string memory) {
        V21Ref.Cfg memory c = V21Ref.Cfg({tau: 7, slopeK: 16, segExp: 2, jLin: 3, maxFee: 2000, clamp: 100, mGate: 0});
        useExtension(deployV21(c, 1), c);
        _header(
            '{"halfLife":"7","slopeK":"16","segmentExp":"2","jLin":"3","maxFee":"2000","clampTicks":"100","mGate":"0","maxSegments":"27"}'
        );
        uint256 t0 = vm.getBlockTimestamp();

        _begin("nondefault_config_segments_decay_cap", 100, 4, 0);
        _pos(bytes24(uint192(1)), -16_000, 16_000, L66);
        _pos(bytes24(uint192(2)), 320, 960, 1e18);
        _swap(true, BIG, _at(700), 0);
        _swap(false, BIG, _at(-500), 0);
        vm.warp(t0 + 10);
        _swap(true, 1e15, SqrtRatio.wrap(0), 0); // decay over more than one half-life, clamped
        _swap(true, 1e18, SqrtRatio.wrap(0), 0);
        vm.warp(t0 + 11);
        _swap(false, -1e17, SqrtRatio.wrap(0), 0);
        _swap(true, -1e17, SqrtRatio.wrap(0), 150);
        _end(true);

        return string.concat(out, "\n]}\n");
    }

    function test_supplement_vectors() public {
        vm.writeFile("test/data/mevcapture-v21/swapsSupplement.json", _buildDefault());
    }

    function test_supplement_nondefault_vectors() public {
        vm.writeFile("test/data/mevcapture-v21/swapsNondefault.json", _buildNondefault());
    }
}
