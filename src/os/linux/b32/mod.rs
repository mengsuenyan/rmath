
#[cfg(target_arch = "x86")]
    pub mod x86;
#[cfg(target_arch = "x86")]
    pub use x86::*;

#[cfg(target_arch = "arm")]
    pub mod arm;
#[cfg(target_arch = "arm")]
    pub use arm::*;

#[cfg(target_arch = "powerpc")]
    pub mod powerpc;
#[cfg(target_arch = "powerpc")]
    pub use powerpc::*;

#[cfg(target_arch = "mips")]
    pub mod mips;
#[cfg(target_arch = "mips")]
    pub use mips::*;

