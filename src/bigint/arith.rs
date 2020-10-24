#![allow(unused)]

#[cfg(not(any(rmath_sse2 = "support")))]
pub use crate::bigint::arith_generic::*;

#[cfg(rmath_sse2 = "support")]
pub use crate::bigint::arith_amd64::*;
