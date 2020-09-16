#[cfg(target_pointer_width = "32")]
mod inner {
    use std::os::raw::c_long;
    
    const __X32_SYSCALL_BIT: c_long = 0x40000000;
    pub const SYS_getrandom: c_long = __X32_SYSCALL_BIT + 318;
}

#[cfg(target_pointer_width = "64")]
mod inner {
    use std::os::raw::c_long;


    pub const SYS_getrandom: c_long = 318;
}

pub use inner::*;