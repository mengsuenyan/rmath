use crate::rand::{Source, Seed};

#[cfg(target_arch = "x86_64")]
use std::arch::x86_64 as march;

#[cfg(target_arch = "x86")]
use std::arch::x86 as march;

pub struct DefaultRand {}

impl DefaultRand {
    pub fn new() -> Self {
        DefaultRand {}
    }
    
    #[target_feature(enable = "rdrand")]
    unsafe fn gen_u32(&mut self) -> Option<u32> {
        let mut out = 0;
        if march::_rdrand32_step(&mut out) > 0 {
            Some(out)
        } else {
            None
        }
    }

    #[cfg(target_arch = "x86")]
    #[target_feature(enable = "rdrand")]
    unsafe fn gen_u64(&mut self) -> Option<u64> {
        self.gen_u32().zip(self.gen_u32()).map(|(low, high)| {
            (low as u64) | ((high as u64) << 32)
        })
    }

    #[cfg(target_arch = "x86_64")]
    #[target_feature(enable = "rdrand")]
    unsafe fn gen_u64(&mut self) -> Option<u64> {
        let mut out = 0;
        if march::_rdrand64_step(&mut out) > 0 {
            Some(out)
        } else {
            None
        }
    }
}

impl Source for DefaultRand {
    fn set_seed<Sd: Seed>(&mut self, _sd: &Sd) {
    }

    fn reset(&mut self) {
    }

    fn gen_u32(&mut self) -> Option<u32> {
        unsafe {self.gen_u32()}
    }

    fn gen_u64(&mut self) -> Option<u64> {
        unsafe {self.gen_u64()}
    }
}