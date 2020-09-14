use crate::rand::{Seed, RandError, RandErrKind, Result};

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
    unsafe fn rdseed_u32(&self) -> Result<u32> {
        let mut out = 0;
        if march::_rdseed32_step(&mut out) > 0 {
            Ok(out)
        } else {
            Err(RandError::new(RandErrKind::NoNewRandSeedGen, ""))
        }
    }
    
    #[cfg(target_arch = "x86")]
    #[target_feature(enable = "rdseed")]
    unsafe fn rdseed_u64(&self) -> Result<u64> {
        match self.rdseed_u32() {
            Ok(low) => {
                self.rdseed_u32().map(|high| {
                    Ok((low as u64) | ((high as u64) << 32))
                })
            },
            Err(e) => Err(e),
        }
    }

    #[cfg(target_arch = "x86_64")]
    #[target_feature(enable = "rdseed")]
    unsafe fn rdseed_u64(&self) -> Result<u64> {
        let mut out = 0;
        if march::_rdseed64_step(&mut out) > 0 {
            Ok(out)
        } else {
            Err(RandError::new(RandErrKind::NoNewRandSeedGen, ""))
        }
    }
}

impl Seed for DefaultSeed {
    fn seed_u32(&self) -> Result<u32> {
        unsafe {self.rdseed_u32()}
    }

    fn seed_u64(&self) -> Result<u64> {
        unsafe {self.rdseed_u64()}
    }
}