use lazy_static::lazy_static;
use num_bigint::BigUint;
use num_traits::One;

lazy_static! {
    // Public constants using lazy_static
    pub static ref MAX_U128: BigUint = (BigUint::one() << 128) - BigUint::one();
    pub static ref MAX_U256: BigUint = (BigUint::one() << 256) - BigUint::one();
}
