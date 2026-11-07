# Zero-seed launch vectors (LOCAL evidence only)

Source: `EkuboProtocol/evm-contracts@853b608ec26d4c80bdad6e394cb8ba686e1ae615`
(tree `7185f89095c2235db68cb51bfc8c4eac4515f42c`), the final `ZeroSeedLaunch`,
`ZeroSeedLaunchPeriphery` and `LaunchToken`. Every file here is copied verbatim from that
commit's `test/vectors/`; nothing is regenerated or edited. These are local Forge fixtures
against a locally compiled `Core`: not deployment, audit or live-chain evidence. No deployment
of this contract exists.

| file | sha256 | source |
|---|---|---|
| `zero-seed-launch.json` | `e5444bf6b1f7e422238331b50b64cf0400597bd13421e281615735511274190b` | `test/vectors/zero-seed-launch.json` (version 8): fee rows and curves, creations, trades, maximum-rate trades and exact-output bounds, start, metadata, spacing and supply rules, code pins |
| `zero-seed-launch-installation.json` | `5cf44854cbf00abb700936b2e22782c27dac5e68cf892edc8f5aa7090067a555` | `test/vectors/zero-seed-launch-installation.json` (version 2): 64 spacing/installation rows from the independent integer oracle, refusals included |
| `zero-seed-launch-events.json` | `24dd5883ce242ec523517c9f38cfd5e8ca29740974aeded5740ac3608e1e7066` | `test/vectors/zero-seed-launch-events.json`: raw `LaunchCreated` with an empty and a nonempty logo, and the raw receipt of a periphery creation, buy, claim and owner transfer |

`src/quoting/pools/zero_seed_launch/LaunchToken.creation.hex` is `LaunchToken`'s creation code
compiled at that commit with its pinned `foundry.toml` (solc 0.8.33, via-IR, 9,999,999 runs,
osaka). Its keccak is `0xb92240f5b935a76e949aab04e7e9e4a0a28adc3ff1a89a349c67dcaab13ea432`,
`pins.creationCode.LaunchToken` of `zero-seed-launch.json`; the tests check both.

`tests/zero_seed_launch.rs` checks the file hashes above and then:

- the fee schedule: the 40 `fee` rows (tick magnitude included), the five `fee_curve.tables`,
  the five SHA-256 digest chains, the `tick_steps` rows, the saturation seconds, the default and
  600-second rates and the consumer default after one day;
- the creator fee range verdicts, `uint64` values that are not encodable failing to parse;
- all 64 installation rows: derived spacing, aligned bounds, steps, bitmap words, pool ticks,
  fixed sqrt ratios, tick cap, supply envelope, liquidity, installed supply, sink, the debit one
  liquidity unit above, and every refusal; plus the spacing table of the specification;
- the four creations, then each creation's trade program replayed swap by swap from the
  installed state (no-bid sell, exact-input and exact-output buys, sells to the ask, upper
  exhaustion and the zero fill after it), with the principal and Core dust after each stage;
- the maximum-rate trades and both exact-output bounds (`SafeCastLib.Overflow`, then
  `AmountBeforeFeeOverflow`), the router buys and the one-unit dust buy;
- the start rule, metadata examples and claim recipient refusals;
- the raw receipt: the predicted token, pool key, position, liquidity, installed and sink
  supply of `LaunchCreated` and its mint `Transfer`s, the `LaunchSwapped` deltas, rate and fee,
  and the claimed amount.
