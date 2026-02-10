//! Thin facades over std/libm so float operations work in `no_std` mode.
use ruint::aliases::U256;

#[inline]
pub fn log_base(value: f64, base: f64) -> f64 {
    #[cfg(feature = "std")]
    {
        value.log(base)
    }
    #[cfg(feature = "no_std")]
    {
        libm::log(value) / libm::log(base)
    }
}

#[inline]
pub fn round_f64(value: f64) -> f64 {
    #[cfg(feature = "std")]
    {
        value.round()
    }
    #[cfg(feature = "no_std")]
    {
        libm::round(value)
    }
}

/// Integer square root specialized for U256 (floor of sqrt).
#[inline]
pub fn integer_sqrt_u256(value: U256) -> U256 {
    #[cfg(feature = "std")]
    {
        value.root(2)
    }
    #[cfg(feature = "no_std")]
    {
        if value <= U256::ONE {
            return value;
        }

        // Newton's method for integer square root.
        let mut x0 = value;
        let mut x1 = (x0 + value / x0) >> 1;

        while x1 < x0 {
            x0 = x1;
            x1 = (x0 + value / x0) >> 1;
        }

        x0
    }
}
