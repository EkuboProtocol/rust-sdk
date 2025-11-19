use crate::{
    chain::Chain,
    math::{
        sqrt_ratio::SQRT_RATIO_ONE,
        uint::{u256_to_float_base_x128, U256},
    },
};

const MASKS: [U256; 27] = [
    U256::from_limbs([8987818235631183931, 18446734850344432284, 0, 0]),
    U256::from_limbs([1390292817054524432, 18446725626983924632, 0, 0]),
    U256::from_limbs([6106104599673403081, 18446707180276744355, 0, 0]),
    U256::from_limbs([11001558419889720088, 18446670286917723849, 0, 0]),
    U256::from_limbs([11758220747761187196, 18446596500421042512, 0, 0]),
    U256::from_limbs([13410380190397192564, 18446448928313114404, 0, 0]),
    U256::from_limbs([16901990496071521224, 18446153787638963396, 0, 0]),
    U256::from_limbs([2628633744169581664, 18445563520457217769, 0, 0]),
    U256::from_limbs([16741406942698519205, 18444383042757836574, 0, 0]),
    U256::from_limbs([8444515413536692068, 18442022313998591526, 0, 0]),
    U256::from_limbs([9306074004969915320, 18437301762902803792, 0, 0]),
    U256::from_limbs([1215727185815661655, 18427864285319361663, 0, 0]),
    U256::from_limbs([4836152305972799785, 18409003819927758022, 0, 0]),
    U256::from_limbs([465769373252535706, 18371340779054097314, 0, 0]),
    U256::from_limbs([11626538800767970419, 18296245704473805246, 0, 0]),
    U256::from_limbs([13511344043162985703, 18146975181141493926, 0, 0]),
    U256::from_limbs([17542275577360126846, 17852077684229624197, 0, 0]),
    U256::from_limbs([9306072323298629247, 17276581513264360642, 0, 0]),
    U256::from_limbs([8354374849381600509, 16180647793008867682, 0, 0]),
    U256::from_limbs([1840363272369915117, 14192930847592841948, 0, 0]),
    U256::from_limbs([16571633202497044730, 10920045577671636999, 0, 0]),
    U256::from_limbs([7981864148337927882, 6464414258794766152, 0, 0]),
    U256::from_limbs([4190795360855086819, 2265367348423649960, 0, 0]),
    U256::from_limbs([14440677137918516476, 278200272243057167, 0, 0]),
    U256::from_limbs([11954280435123913168, 4195612578938288, 0, 0]),
    U256::from_limbs([1943989925737446246, 954269482040, 0, 0]),
    U256::from_limbs([6723154418996326713, 49365, 0, 0]),
];

pub fn to_sqrt_ratio<C: Chain>(tick: i32) -> Option<U256> {
    if tick < C::min_tick() || tick > C::max_tick() {
        return None;
    }

    let mut ratio = SQRT_RATIO_ONE;

    let tick_abs = tick.abs();

    for (i, mask) in MASKS.iter().enumerate() {
        if (tick_abs & (1 << i)) != 0 {
            ratio = (ratio * mask) >> 128;
        }
    }

    if tick > 0 {
        ratio = U256::MAX / ratio;
    }

    Some(C::adjust_sqrt_ratio_precision(ratio))
}

const SQRT_TICK_SIZE: f64 =
    1.00000049999987500006249996093752734372949220361326815796989439990616646_f64;

pub fn approximate_sqrt_ratio_to_tick(sqrt_ratio: U256) -> i32 {
    u256_to_float_base_x128(sqrt_ratio)
        .log(SQRT_TICK_SIZE)
        .round() as i32
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::chain::{
        evm::Evm,
        starknet::Starknet,
        tests::{ChainEnum, CHAINS},
    };

    mod to_sqrt_ratio {
        use ruint::uint;

        use super::*;

        #[test]
        fn tick_examples() {
            for chain in CHAINS {
                match chain {
                    ChainEnum::Starknet => {
                        assert_eq!(
                            to_sqrt_ratio::<Starknet>(1_000_000).unwrap(),
                            uint!(561030636129153856592777659729523183729_U256)
                        );
                        assert_eq!(
                            to_sqrt_ratio::<Starknet>(10_000_000).unwrap(),
                            uint!(50502254805927926084427918474025309948677_U256)
                        );
                        assert_eq!(
                            to_sqrt_ratio::<Starknet>(-1_000_000).unwrap(),
                            uint!(206391740095027370700312310531588921767_U256)
                        );
                        assert_eq!(
                            to_sqrt_ratio::<Starknet>(-10_000_000).unwrap(),
                            uint!(2292810285051363400276741638672651165_U256)
                        );
                    }
                    ChainEnum::Evm => {
                        assert_eq!(
                            to_sqrt_ratio::<Evm>(1_000_000).unwrap(),
                            uint!(561030636129153856579134353873645338624_U256)
                        );
                        assert_eq!(
                            to_sqrt_ratio::<Evm>(10_000_000).unwrap(),
                            uint!(50502254805927926084423855178401471004672_U256)
                        );
                        assert_eq!(
                            to_sqrt_ratio::<Evm>(-1_000_000).unwrap(),
                            uint!(206391740095027370700312310528859963392_U256)
                        );
                        assert_eq!(
                            to_sqrt_ratio::<Evm>(-10_000_000).unwrap(),
                            uint!(2292810285051363400276741630355046400_U256)
                        );
                    }
                }
            }
        }

        #[test]
        fn tick_too_small() {
            for chain in CHAINS {
                match chain {
                    ChainEnum::Starknet => {
                        assert!(to_sqrt_ratio::<Starknet>(Starknet::MIN_TICK - 1).is_none());
                        assert!(to_sqrt_ratio::<Starknet>(i32::MIN).is_none());
                    }
                    ChainEnum::Evm => {
                        assert!(to_sqrt_ratio::<Evm>(Evm::MIN_TICK - 1).is_none());
                        assert!(to_sqrt_ratio::<Evm>(i32::MIN).is_none());
                    }
                }
            }
        }

        #[test]
        fn min_tick() {
            for chain in CHAINS {
                match chain {
                    ChainEnum::Starknet => {
                        assert_eq!(
                            to_sqrt_ratio::<Starknet>(Starknet::MIN_TICK).unwrap(),
                            Starknet::MIN_SQRT_RATIO
                        );
                    }
                    ChainEnum::Evm => {
                        assert_eq!(
                            to_sqrt_ratio::<Evm>(Evm::MIN_TICK).unwrap(),
                            Evm::MIN_SQRT_RATIO
                        );
                    }
                }
            }
        }

        #[test]
        fn max_tick() {
            for chain in CHAINS {
                match chain {
                    ChainEnum::Starknet => {
                        assert_eq!(
                            to_sqrt_ratio::<Starknet>(Starknet::MAX_TICK).unwrap(),
                            Starknet::MAX_SQRT_RATIO
                        );
                    }
                    ChainEnum::Evm => {
                        assert_eq!(
                            to_sqrt_ratio::<Evm>(Evm::MAX_TICK).unwrap(),
                            Evm::MAX_SQRT_RATIO
                        );
                    }
                }
            }
        }

        #[test]
        fn tick_too_large() {
            for chain in CHAINS {
                match chain {
                    ChainEnum::Starknet => {
                        assert!(to_sqrt_ratio::<Starknet>(Starknet::MAX_TICK + 1).is_none());
                        assert!(to_sqrt_ratio::<Starknet>(i32::MAX).is_none());
                    }
                    ChainEnum::Evm => {
                        assert!(to_sqrt_ratio::<Evm>(Evm::MAX_TICK + 1).is_none());
                        assert!(to_sqrt_ratio::<Evm>(i32::MAX).is_none());
                    }
                }
            }
        }
    }

    mod approximate_sqrt_ratio_to_tick {
        use super::*;

        #[test]
        fn tick_examples() {
            for chain in CHAINS {
                match chain {
                    ChainEnum::Starknet => {
                        assert_eq!(
                            approximate_sqrt_ratio_to_tick(to_sqrt_ratio::<Starknet>(0).unwrap()),
                            0
                        );
                        assert_eq!(
                            approximate_sqrt_ratio_to_tick(
                                to_sqrt_ratio::<Starknet>(1_000_000).unwrap()
                            ),
                            1_000_000
                        );
                        assert_eq!(
                            approximate_sqrt_ratio_to_tick(
                                to_sqrt_ratio::<Starknet>(10_000_000).unwrap()
                            ),
                            10_000_000
                        );
                        assert_eq!(
                            approximate_sqrt_ratio_to_tick(
                                to_sqrt_ratio::<Starknet>(-1_000_000).unwrap()
                            ),
                            -1_000_000
                        );
                        assert_eq!(
                            approximate_sqrt_ratio_to_tick(
                                to_sqrt_ratio::<Starknet>(-10_000_000).unwrap()
                            ),
                            -10_000_000
                        );
                    }
                    ChainEnum::Evm => {
                        assert_eq!(
                            approximate_sqrt_ratio_to_tick(to_sqrt_ratio::<Evm>(0).unwrap()),
                            0
                        );
                        assert_eq!(
                            approximate_sqrt_ratio_to_tick(
                                to_sqrt_ratio::<Evm>(1_000_000).unwrap()
                            ),
                            1_000_000
                        );
                        assert_eq!(
                            approximate_sqrt_ratio_to_tick(
                                to_sqrt_ratio::<Evm>(10_000_000).unwrap()
                            ),
                            10_000_000
                        );
                        assert_eq!(
                            approximate_sqrt_ratio_to_tick(
                                to_sqrt_ratio::<Evm>(-1_000_000).unwrap()
                            ),
                            -1_000_000
                        );
                        assert_eq!(
                            approximate_sqrt_ratio_to_tick(
                                to_sqrt_ratio::<Evm>(-10_000_000).unwrap()
                            ),
                            -10_000_000
                        );
                    }
                }
            }
        }

        #[test]
        fn min_tick() {
            for chain in CHAINS {
                match chain {
                    ChainEnum::Starknet => assert_eq!(
                        approximate_sqrt_ratio_to_tick(
                            to_sqrt_ratio::<Starknet>(Starknet::MIN_TICK).unwrap()
                        ),
                        Starknet::MIN_TICK
                    ),
                    ChainEnum::Evm => assert_eq!(
                        approximate_sqrt_ratio_to_tick(
                            to_sqrt_ratio::<Evm>(Evm::MIN_TICK).unwrap()
                        ),
                        Evm::MIN_TICK
                    ),
                }
            }
        }

        #[test]
        fn max_tick() {
            for chain in CHAINS {
                match chain {
                    ChainEnum::Starknet => assert_eq!(
                        approximate_sqrt_ratio_to_tick(
                            to_sqrt_ratio::<Starknet>(Starknet::MAX_TICK).unwrap()
                        ),
                        Starknet::MAX_TICK
                    ),
                    ChainEnum::Evm => assert_eq!(
                        approximate_sqrt_ratio_to_tick(
                            to_sqrt_ratio::<Evm>(Evm::MAX_TICK).unwrap()
                        ),
                        Evm::MAX_TICK
                    ),
                }
            }
        }
    }
}
