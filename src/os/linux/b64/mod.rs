
#[cfg(target_arch = "x86_64")]
    pub mod x86_64;
#[cfg(target_arch = "x86_64")]
    pub use x86_64::*;

#[cfg(target_arch = "powerpc64")]
    pub mod powerpc64;
#[cfg(target_arch = "powerpc64")]
    pub use powerpc64::*;

#[cfg(target_arch = "mips64")]
    pub mod mips64;
#[cfg(target_arch = "mips64")]
    pub use mips64::*;

#[cfg(target_arch = "aarch64")]
    pub mod aarch64;
#[cfg(target_arch = "aarch64")]
    pub use aarch64::*;