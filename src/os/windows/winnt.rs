use std::os::raw::{c_void, c_long};

pub type PVOID = *mut c_void;
pub type WCHAR = u16;
pub type LONG = c_long;


pub type LPCWSTR = *const WCHAR;
pub type PCWSTR = *const WCHAR;

