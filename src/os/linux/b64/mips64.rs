
use std::os::raw::c_long;

const SYS_read: c_long = 5000;
pub const SYS_getrandom: c_long = SYS_read + 313;