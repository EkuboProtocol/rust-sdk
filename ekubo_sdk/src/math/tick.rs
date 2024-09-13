use num_traits::Num;
use super::constants::{MAX_U256};

use num_bigint::BigUint;
use std::error::Error;
use std::fmt;
use std::str::FromStr;

lazy_static::lazy_static! {
    pub static ref MIN_SQRT_RATIO: BigUint = BigUint::from_str("18446748437148339061").unwrap();
    pub static ref MASKS: [BigUint;27] =  [
        <BigUint as Num>::from_str_radix("fffff79c8499329c7cbb2510d893283b", 16).unwrap(),
        <BigUint as Num>::from_str_radix("ffffef390978c398134b4ff3764fe410", 16).unwrap(),
        <BigUint as Num>::from_str_radix("ffffde72140b00a354bd3dc828e976c9",16).unwrap(),
        <BigUint as Num>::from_str_radix("ffffbce42c7be6c998ad6318193c0b18",16).unwrap(),
        <BigUint as Num>::from_str_radix("ffff79c86a8f6150a32d9778eceef97c",16).unwrap(),
        <BigUint as Num>::from_str_radix("fffef3911b7cff24ba1b3dbb5f8f5974",16).unwrap(),
        <BigUint as Num>::from_str_radix("fffde72350725cc4ea8feece3b5f13c8",16).unwrap(),
        <BigUint as Num>::from_str_radix("fffbce4b06c196e9247ac87695d53c60",16).unwrap(),
        <BigUint as Num>::from_str_radix("fff79ca7a4d1bf1ee8556cea23cdbaa5",16).unwrap(),
        <BigUint as Num>::from_str_radix("ffef3995a5b6a6267530f207142a5764",16).unwrap(),
        <BigUint as Num>::from_str_radix("ffde7444b28145508125d10077ba83b8",16).unwrap(),
        <BigUint as Num>::from_str_radix("ffbceceeb791747f10df216f2e53ec57",16).unwrap(),
        <BigUint as Num>::from_str_radix("ff79eb706b9a64c6431d76e63531e929",16).unwrap(),
        <BigUint as Num>::from_str_radix("fef41d1a5f2ae3a20676bec6f7f9459a",16).unwrap(),
        <BigUint as Num>::from_str_radix("fde95287d26d81bea159c37073122c73",16).unwrap(),
        <BigUint as Num>::from_str_radix("fbd701c7cbc4c8a6bb81efd232d1e4e7",16).unwrap(),
        <BigUint as Num>::from_str_radix("f7bf5211c72f5185f372aeb1d48f937e",16).unwrap(),
        <BigUint as Num>::from_str_radix("efc2bf59df33ecc28125cf78ec4f167f",16).unwrap(),
        <BigUint as Num>::from_str_radix("e08d35706200796273f0b3a981d90cfd",16).unwrap(),
        <BigUint as Num>::from_str_radix("c4f76b68947482dc198a48a54348c4ed",16).unwrap(),
        <BigUint as Num>::from_str_radix("978bcb9894317807e5fa4498eee7c0fa",16).unwrap(),
        <BigUint as Num>::from_str_radix("59b63684b86e9f486ec54727371ba6ca",16).unwrap(),
        <BigUint as Num>::from_str_radix("1f703399d88f6aa83a28b22d4a1f56e3",16).unwrap(),
        <BigUint as Num>::from_str_radix("3dc5dac7376e20fc8679758d1bcdcfc",16).unwrap(),
        <BigUint as Num>::from_str_radix("ee7e32d61fdb0a5e622b820f681d0",16).unwrap(),
        <BigUint as Num>::from_str_radix("de2ee4bc381afa7089aa84bb66",16).unwrap(),
        <BigUint as Num>::from_str_radix("c0d55d4d7152c25fb139",16).unwrap(),
    ];
    pub static ref ONE_X128: BigUint = <BigUint as Num>::from_str_radix("100000000000000000000000000000000", 16).unwrap();
}

pub const MIN_TICK: i32 = -88722883;
pub const MAX_TICK: i32 = 88722883;
pub const MAX_TICK_SPACING: i32 = 354892;

// Define a custom error type for more contextual errors
#[derive(Debug)]
struct InvalidTickError(i32);

impl fmt::Display for InvalidTickError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Invalid tick: {}", self.0)
    }
}

impl Error for InvalidTickError {}

pub fn to_sqrt_ratio(tick: i32) -> Result<BigUint, InvalidTickError> {
    if tick < MIN_TICK || tick > MAX_TICK {
        return Err(InvalidTickError(tick));
    }

    let mut ratio = ONE_X128.clone();

    let tick_abs = tick.abs();

    for (i, mask) in MASKS.iter().enumerate() {
        if (tick_abs & (1 << i)) != 0 {
            ratio = (ratio * mask) >> 128;
        }
    }

    if tick > 0 {
        ratio = MAX_U256.clone() / ratio;
    }

    Ok(ratio)
}

#[cfg(test)]
mod tests {
    use num_bigint::{BigUint};
    use super::{to_sqrt_ratio, Num};

    #[test]
    fn test_tick_examples() {
        assert_eq!(
            to_sqrt_ratio(1000000).unwrap(),
            <BigUint as Num>::from_str_radix("561030636129153856592777659729523183729", 10).unwrap(),
        );
        assert_eq!(
            to_sqrt_ratio(10000000).unwrap(),
            <BigUint as Num>::from_str_radix("50502254805927926084427918474025309948677", 10).unwrap(),
        );
        assert_eq!(
            to_sqrt_ratio(-1000000).unwrap(),
            <BigUint as Num>::from_str_radix("206391740095027370700312310531588921767", 10).unwrap(),
        );
        assert_eq!(
            to_sqrt_ratio(-10000000).unwrap(),
            <BigUint as Num>::from_str_radix("2292810285051363400276741638672651165", 10).unwrap(),
        );
    }
}

