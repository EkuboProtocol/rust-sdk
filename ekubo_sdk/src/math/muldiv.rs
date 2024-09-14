use crate::math::uint::{U256, U512};

#[derive(Debug)]
pub enum MuldivError {
    Overflow,
    DenominatorZero,
}

pub(crate) fn muldiv(x: U256, y: U256, d: U256, round_up: bool) -> Result<U256, MuldivError> {
    if d.is_zero() {
        Err(MuldivError::DenominatorZero)
    } else {
        let intermediate: U512 = <U256 as Into<U512>>::into(x) * <U256 as Into<U512>>::into(y);
        let (result, denominator) = intermediate.div_mod(d.into());

        let rounded = if round_up && !denominator.is_zero() {
            result + 1
        } else {
            result
        };

        rounded.try_into().map_err(|_| MuldivError::Overflow)
    }
}