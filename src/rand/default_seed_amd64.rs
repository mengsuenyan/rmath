use crate::rand::Seed;

#[cfg(target_arch = "x86_64")]
use std::arch::x86_64 as march;

#[cfg(target_arch = "x86")]
use std::arch::x86 as march;

pub struct DefaultSeed {}

impl DefaultSeed {
    pub fn new() -> Self {
        DefaultSeed{}
    }
    
    #[target_feature(enable = "rdseed")]
    unsafe fn rdseed_u32(&self) -> Option<u32> {
        let mut out = 0;
        if march::_rdseed32_step(&mut out) > 0 {
            Some(out)
        } else {
            None
        }
    }
    
    #[cfg(target_arch = "x86")]
    #[target_feature(enable = "rdseed")]
    unsafe fn rdseed_u64(&self) -> Option<u64> {
        self.rdseed_u32().zip(self.rdseed_u32()).map(|(low, high)| {
            (low as u64) | ((high as u64) << 32)
        })
    }

    #[cfg(target_arch = "x86_64")]
    #[target_feature(enable = "rdseed")]
    unsafe fn rdseed_u64(&self) -> Option<u64> {
        let mut out = 0;
        if march::_rdseed64_step(&mut out) > 0 {
            Some(out)
        } else {
            None
        }
    }
}

impl Seed for DefaultSeed {
    fn seed_u32(&self) -> Option<u32> {
        unsafe {self.rdseed_u32()}
    }

    fn seed_u64(&self) -> Option<u64> {
        unsafe {self.rdseed_u64()}
    }
}