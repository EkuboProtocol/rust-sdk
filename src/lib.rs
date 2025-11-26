#![no_std]
extern crate alloc;

pub use ruint::aliases::U256;

pub mod chain;
pub mod math;
pub mod quoting;

mod private {
    pub trait Sealed {}
}
