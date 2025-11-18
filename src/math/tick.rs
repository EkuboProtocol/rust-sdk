use crate::{
    chain::Chain,
    math::uint::{u256_to_float_base_x128, U256},
};

const ONE_X128: U256 = U256([0, 0, 1, 0]);

const MASKS: [U256; 27] = [
    U256([8987818235631183931, 18446734850344432284, 0, 0]),
    U256([1390292817054524432, 18446725626983924632, 0, 0]),
    U256([6106104599673403081, 18446707180276744355, 0, 0]),
    U256([11001558419889720088, 18446670286917723849, 0, 0]),
    U256([11758220747761187196, 18446596500421042512, 0, 0]),
    U256([13410380190397192564, 18446448928313114404, 0, 0]),
    U256([16901990496071521224, 18446153787638963396, 0, 0]),
    U256([2628633744169581664, 18445563520457217769, 0, 0]),
    U256([16741406942698519205, 18444383042757836574, 0, 0]),
    U256([8444515413536692068, 18442022313998591526, 0, 0]),
    U256([9306074004969915320, 18437301762902803792, 0, 0]),
    U256([1215727185815661655, 18427864285319361663, 0, 0]),
    U256([4836152305972799785, 18409003819927758022, 0, 0]),
    U256([465769373252535706, 18371340779054097314, 0, 0]),
    U256([11626538800767970419, 18296245704473805246, 0, 0]),
    U256([13511344043162985703, 18146975181141493926, 0, 0]),
    U256([17542275577360126846, 17852077684229624197, 0, 0]),
    U256([9306072323298629247, 17276581513264360642, 0, 0]),
    U256([8354374849381600509, 16180647793008867682, 0, 0]),
    U256([1840363272369915117, 14192930847592841948, 0, 0]),
    U256([16571633202497044730, 10920045577671636999, 0, 0]),
    U256([7981864148337927882, 6464414258794766152, 0, 0]),
    U256([4190795360855086819, 2265367348423649960, 0, 0]),
    U256([14440677137918516476, 278200272243057167, 0, 0]),
    U256([11954280435123913168, 4195612578938288, 0, 0]),
    U256([1943989925737446246, 954269482040, 0, 0]),
    U256([6723154418996326713, 49365, 0, 0]),
];

pub fn to_sqrt_ratio<C: Chain>(tick: i32) -> Option<U256> {
    if tick < C::min_tick() || tick > C::max_tick() {
        return None;
    }

    let mut ratio = ONE_X128.clone();

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
    mod to_sqrt_ratio {
        use super::super::{to_sqrt_ratio, MAX_SQRT_RATIO, MAX_TICK, MIN_SQRT_RATIO, MIN_TICK};
        use crate::math::uint::U256;

        #[test]
        fn test_tick_examples() {
            assert_eq!(
                to_sqrt_ratio(1000000).unwrap(),
                U256::from_str_radix("561030636129153856579134353873645338624", 10).unwrap(),
            );
            assert_eq!(
                to_sqrt_ratio(10000000).unwrap(),
                U256::from_str_radix("50502254805927926084423855178401471004672", 10).unwrap(),
            );
            assert_eq!(
                to_sqrt_ratio(-1000000).unwrap(),
                U256::from_str_radix("206391740095027370700312310528859963392", 10).unwrap(),
            );
            assert_eq!(
                to_sqrt_ratio(-10000000).unwrap(),
                U256::from_str_radix("2292810285051363400276741630355046400", 10).unwrap(),
            );
        }

        #[test]
        fn test_tick_too_small() {
            assert!(to_sqrt_ratio(MIN_TICK - 1).is_none());
            assert!(to_sqrt_ratio(i32::MIN).is_none());
        }

        #[test]
        fn test_min_tick() {
            assert_eq!(to_sqrt_ratio(MIN_TICK).unwrap(), MIN_SQRT_RATIO,);
        }

        #[test]
        fn test_max_tick() {
            assert_eq!(to_sqrt_ratio(MAX_TICK).unwrap(), MAX_SQRT_RATIO,);
        }

        #[test]
        fn test_tick_too_large() {
            assert!(to_sqrt_ratio(MAX_TICK + 1).is_none());
            assert!(to_sqrt_ratio(i32::MAX).is_none());
        }
    }

    mod approximate_sqrt_ratio_to_tick {
        use crate::math::tick::{MAX_TICK, MIN_TICK};

        use super::super::{approximate_sqrt_ratio_to_tick, to_sqrt_ratio};

        #[test]
        fn test_tick_examples() {
            assert_eq!(approximate_sqrt_ratio_to_tick(to_sqrt_ratio(0).unwrap()), 0,);
            assert_eq!(
                approximate_sqrt_ratio_to_tick(to_sqrt_ratio(1000000).unwrap()),
                1000000,
            );
            assert_eq!(
                approximate_sqrt_ratio_to_tick(to_sqrt_ratio(10000000).unwrap()),
                10000000
            );
            assert_eq!(
                approximate_sqrt_ratio_to_tick(to_sqrt_ratio(-1000000).unwrap()),
                -1000000,
            );
            assert_eq!(
                approximate_sqrt_ratio_to_tick(to_sqrt_ratio(-10000000).unwrap()),
                -10000000,
            );
        }

        #[test]
        fn test_min_tick() {
            assert_eq!(
                approximate_sqrt_ratio_to_tick(to_sqrt_ratio(MIN_TICK).unwrap()),
                MIN_TICK,
            );
        }

        #[test]
        fn test_max_tick() {
            assert_eq!(
                approximate_sqrt_ratio_to_tick(to_sqrt_ratio(MAX_TICK).unwrap()),
                MAX_TICK,
            );
        }
    }
}
