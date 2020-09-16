#![allow(non_camel_case_types, unused, non_upper_case_globals)]
use std::os::raw::{c_long, c_uint};
use std::collections::VecDeque;
use crate::os::linux::b64::SYS_getrandom;

#[cfg(any(target_arch = "arm",
    target_arch = "mips",
    target_arch = "powerpc",
    target_arch = "x86"))]
pub mod b32;

#[cfg(any(target_arch = "x86_64",
    target_arch = "mips64",
    target_arch = "powerpc64",
    target_arch = "aarch64"))]
pub mod b64;

const GRND_NONBLOCK: c_uint = 0x0001;

extern "C" {
    fn syscall(num: c_long, ...) -> c_long;
}

#[derive(Clone)]
pub struct BCrypt {
    buf: VecDeque<u8>,
}

impl BCrypt {
    pub fn new() -> Self {
        Self {
            buf: VecDeque::with_capacity(32),
        }
    }
    
    pub fn gen_random(&mut self, buf: &mut [u8]) -> std::result::Result<(), std::io::Error> {
        let len = unsafe {
            syscall(SYS_getrandom, buf.as_mut_ptr(), buf.len(), GRND_NONBLOCK)
        };
        
        if len >= 0 { 
            buf[0..(len as usize)].iter().for_each(|&x| {
                self.buf.push_front(x);
            });
        }
        
        if self.buf.len() < buf.len() {
            Err(std::io::Error::new(std::io::ErrorKind::Other, format!("only read {} bytes random bytes from the system", self.buf.len())))
        } else {
            self.buf.iter().rev().zip(buf.iter_mut()).for_each(|(&x, y)| {
                *y = x;
            });
            self.buf.truncate(self.buf.len() - buf.len());
            Ok(())
        }
    }
}