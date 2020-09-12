
#[macro_use]
mod nat_macro;

mod nat;
mod nat_err;

#[cfg(rmath_avx2 = "support")]
mod nat_avx2;

#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
mod nat_amd64;

#[cfg(not(any(target_arch = "x86", target_arch = "x86_64", rmath_avx2 = "support")))]
mod nat_generic;

pub use nat::Nat;
pub use nat_err::NatError;
