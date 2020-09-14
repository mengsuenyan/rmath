use crate::rand::{Source, Seed, RandError, RandErrKind, Result};

#[cfg(target_arch = "x86_64")]
use std::arch::x86_64 as march;

#[cfg(target_arch = "x86")]
use std::arch::x86 as march;

pub struct DefaultRand {}

impl DefaultRand {
    pub fn new<Sd: Seed>(_sd: &Sd) -> Result<Self> {
        Ok(DefaultRand {})
    }
    
    #[target_feature(enable = "rdrand")]
    unsafe fn gen_u32(&mut self) -> Result<u32> {
        let mut out = 0;
        if march::_rdrand32_step(&mut out) > 0 {
            Ok(out)
        } else {
            Err(RandError::new(RandErrKind::NoNewRandNumberGen, ""))
        }
    }

    #[cfg(target_arch = "x86")]
    #[target_feature(enable = "rdrand")]
    unsafe fn gen_u64(&mut self) -> Result<u64> {
        match self.gen_u32() {
            Ok(low) => self.gen_u32().map(|high| {
                Ok((low as u64) | ((high as u64) << 32))
            }),
            Err(e) => Err(e),
        }
    }

    #[cfg(target_arch = "x86_64")]
    #[target_feature(enable = "rdrand")]
    unsafe fn gen_u64(&mut self) -> Result<u64> {
        let mut out = 0;
        if march::_rdrand64_step(&mut out) > 0 {
            Ok(out)
        } else {
            Err(RandError::new(RandErrKind::NoNewRandNumberGen, ""))
        }
    }
}

impl Source for DefaultRand {
    fn gen_u32(&mut self) -> Result<u32> {
        unsafe {self.gen_u32()}
    }

    fn reset<Sd: Seed>(&mut self, _sd: &Sd) -> Result<()> {
        Ok(())
    }

    fn gen_u64(&mut self) -> Result<u64> {
        unsafe {self.gen_u64()}
    }
}