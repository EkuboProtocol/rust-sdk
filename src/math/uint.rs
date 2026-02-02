use ruint::aliases::U256;

#[must_use]
pub fn u256_to_float_base_x128(x128: U256) -> f64 {
    let [l0, l1, l2, l3] = x128.into_limbs();
    l0 as f64 / 340282366920938463463374607431768211456f64
        + (l1 as f64 / 18446744073709551616f64)
        + l2 as f64
        + (l3 as f64 * 18446744073709551616f64)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn u256_to_fraction() {
        assert_eq!(
            u256_to_float_base_x128(U256::from_limbs([
                16403144882676588163,
                1525053501570699700,
                35,
                0
            ])),
            35.08267331597798
        );
        assert_eq!(
            u256_to_float_base_x128(U256::from_limbs([123456, 0, 0, 0])),
            3.628045764377908e-34
        );
        assert_eq!(
            u256_to_float_base_x128(U256::from_limbs([0, 123456, 0, 0])),
            6.692563170318522e-15
        );
        assert_eq!(
            u256_to_float_base_x128(U256::from_limbs([0, 0, 123456, 0])),
            123456.0
        );
        assert_eq!(
            u256_to_float_base_x128(U256::from_limbs([0, 0, 0, 123456])),
            2.2773612363638864e24
        );
    }
}
