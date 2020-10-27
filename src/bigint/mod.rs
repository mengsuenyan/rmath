//! ECDSA椭圆曲线数字签名算法: https://www.cnblogs.com/mengsuenyan/p/13816789.html
//! 
//! 椭圆加密数学基础: https://www.cnblogs.com/mengsuenyan/p/13156265.html
//! 
//! 数论相关: https://www.cnblogs.com/mengsuenyan/p/12969712.html
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

mod float;