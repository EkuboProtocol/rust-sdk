use num_traits::Zero;

uint::construct_uint! {
    pub struct U256(4);
}

uint::construct_uint! {
    pub(crate) struct U512(8);
}

impl From<U256> for U512 {
    fn from(value: U256) -> Self {
        let mut result = U512::default();
        for (i, &limb) in value.0.iter().enumerate() {
            result.0[i] = limb;
        }
        result
    }
}

impl TryFrom<U512> for U256 {
    type Error = ();

    fn try_from(value: U512) -> Result<Self, Self::Error> {
        let mut result = U256::default();
        for (i, &limb) in value.0.iter().enumerate() {
            if i >= 4 && !limb.is_zero() {
                return Err(());
            }
            if i < 4 {
                result.0[i] = limb;
            }
        }
        Ok(result)
    }
}