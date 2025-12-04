#![no_std]

// Enforce that exactly one of "std" or "no_std" is selected.
#[cfg(all(feature = "std", feature = "no_std"))]
compile_error!(r#"Features "std" and "no_std" are mutually exclusive."#);
#[cfg(not(any(feature = "std", feature = "no_std")))]
compile_error!(r#"Either feature "std" or "no_std" must be enabled."#);

extern crate alloc;
#[cfg(feature = "std")]
extern crate std;

pub use ruint::aliases::U256;

pub mod chain;
pub mod math;
pub mod quoting;

mod private {
    pub trait Sealed {}
}
