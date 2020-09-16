use std::os::raw::{c_ulong, c_uchar};

pub type DWORD = c_ulong;
pub type ULONG = DWORD;
pub type UCHAR = c_uchar;
pub type PUCHAR = *mut UCHAR;