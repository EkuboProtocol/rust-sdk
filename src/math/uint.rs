use ruint::aliases::U256;

#[must_use]
pub fn u256_to_float_base_x128(x128: U256) -> f64 {
    let [l0, l1, l2, l3] = x128.into_limbs();
    l0 as f64 / 340282366920938463463374607431768211456f64
        + (l1 as f64 / 18446744073709551616f64)
        + l2 as f64
        + (l3 as f64 * 18446744073709551616f64)
}
