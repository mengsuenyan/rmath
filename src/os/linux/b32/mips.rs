use std::os::raw::c_long;

pub const SYS_syscall: c_long = 4000;
pub const SYS_getrandom: c_long = SYS_syscall + 353;
