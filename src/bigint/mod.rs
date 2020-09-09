
#[macro_use]
mod nat_macro;

mod nat;
mod nat_err;

// #[cfg(not(any(target_arch = "x86", target_arch = "x86_64")))]
mod nat_generic;

pub use nat::Nat;
pub use nat_err::NatError;
