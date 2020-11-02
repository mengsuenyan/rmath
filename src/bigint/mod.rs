//! ECDSA椭圆曲线数字签名算法: https://www.cnblogs.com/mengsuenyan/p/13816789.html
//! 
//! 椭圆加密数学基础: https://www.cnblogs.com/mengsuenyan/p/13156265.html
//! 
//! 数论相关: https://www.cnblogs.com/mengsuenyan/p/12969712.html
//! 
//! 
//! # Note
//! 
//! **The implementation of the `Clone` trait just only provide a shadow clone of the data that purpose is to share the ownership of the data, and the `deep_clone` method provide a real clone of the data.**
//! 

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


#[macro_use]
mod bigint_macro;

mod bigint;
pub use bigint::BigInt;

#[cfg(not(any(rmath_sse2 = "support")))]
mod arith_generic;

#[cfg(rmath_sse2 = "support")]
mod arith_amd64;

mod arith;

mod util;

#[macro_use]
mod float_macro;

mod float_para;
mod decimal;
mod float_err;
mod float_fmt;
pub mod float;
pub use float::Float;

mod rat;
mod rat_err;
pub use rat_err::{RatError, RatErrKind};
pub use rat::Rat;