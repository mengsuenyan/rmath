/// The DefaultSeed implement by the rdseed instruction in the x86/x86_64 platform

use crate::rand::{Seed, RandError, RandErrKind, Result, PrimitiveType};

#[cfg(target_arch = "x86_64")]
use std::arch::x86_64 as march;

#[cfg(target_arch = "x86")]
use std::arch::x86 as march;
use std::marker::PhantomData;

#[derive(Clone)]
pub struct DefaultSeed<T> {
    ph: PhantomData<T>,
}

impl<T: PrimitiveType> DefaultSeed<T> {
    pub fn new() -> Result<Self> {
        Ok(DefaultSeed {ph: PhantomData})
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
    
    fn rdseed_usize(&self) -> Result<usize> {
        #[cfg(target_pointer_width = "32")]
            unsafe {self.rdseed_u32().map(|x| {x as usize}) }

        #[cfg(target_pointer_width = "64")]
            unsafe {self.rdseed_u64().map(|x| {x as usize})}
    }
}

impl Seed<u32> for DefaultSeed<u32> {
    fn seed(&self) -> Result<u32> {
        unsafe {
            self.rdseed_u32()
        }
    }
}

impl Seed<u64> for DefaultSeed<u64> {
    fn seed(&self) -> Result<u64> {
        unsafe {
            self.rdseed_u64()
        }
    }
}

impl Seed<usize> for DefaultSeed<usize> {
    fn seed(&self) -> Result<usize> {
        self.rdseed_usize()
    }
}
