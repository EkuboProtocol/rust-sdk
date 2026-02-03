#![no_std]

// Enforce that exactly one of "std" or "no_std" is selected.
#[cfg(all(feature = "std", feature = "no_std"))]
compile_error!(r#"Features "std" and "no_std" are mutually exclusive."#);
#[cfg(not(any(feature = "std", feature = "no_std")))]
compile_error!(r#"Either feature "std" or "no_std" must be enabled."#);

// Enforce that exactly one alloy version is selected when EVM support is enabled.
#[cfg(all(feature = "evm-alloy-0_6", feature = "evm-alloy-1"))]
compile_error!(r#"Features "evm-alloy-0_6" and "evm-alloy-1" are mutually exclusive."#);
#[cfg(all(feature = "evm", not(any(feature = "evm-alloy-0_6", feature = "evm-alloy-1"))))]
compile_error!(r#"Feature "evm" requires either "evm-alloy-0_6" or "evm-alloy-1"."#);

extern crate alloc;
#[cfg(any(test, feature = "std"))]
extern crate std;

pub use ruint::aliases::U256;

#[cfg(feature = "evm-alloy-0_6")]
pub use alloy_primitives_0_6 as alloy_primitives;
#[cfg(feature = "evm-alloy-1")]
pub use alloy_primitives_1 as alloy_primitives;

pub mod chain;
pub mod math;
pub mod quoting;

mod private {
    pub trait Sealed {}
}
