use crate::rand::{Source, Seed, RandError, RandErrKind, Result, PrimitiveType};

#[cfg(target_arch = "x86_64")]
use std::arch::x86_64 as march;

#[cfg(target_arch = "x86")]
use std::arch::x86 as march;
use std::marker::PhantomData;

pub struct DefaultRand<T> {
    ph: PhantomData<T>
}

impl<T: PrimitiveType> DefaultRand<T> {
    pub fn new<Sd: Seed<T>>(_sd: &Sd) -> Result<Self> {
        Ok(DefaultRand {ph: PhantomData})
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
    
    fn gen_usize(&mut self) -> Result<usize> {
        #[cfg(target_pointer_width = "32")]
            unsafe {self.gen_u32().map(|x| {x as usize}) }

        #[cfg(target_pointer_width = "64")]
            unsafe {self.gen_u64().map(|x| {x as usize})}
    }
}

impl Source<u32> for DefaultRand<u32> {
    fn gen(&mut self) -> Result<u32> {
        unsafe {
            self.gen_u32()
        }
    }

    fn reset<Sd: Seed<u32>>(&mut self, _sd: &Sd) -> Result<()> {
        Ok(())
    }
}

impl Source<u64> for DefaultRand<u64> {
    fn gen(&mut self) -> Result<u64> {
        unsafe {
            self.gen_u64()
        }
    }

    fn reset<Sd: Seed<u64>>(&mut self, _sd: &Sd) -> Result<()> {
        Ok(())
    }
}

impl Source<usize> for DefaultRand<usize> {
    fn gen(&mut self) -> Result<usize> {
        self.gen_usize()
    }

    fn reset<Sd: Seed<usize>>(&mut self, _sd: &Sd) -> Result<()> {
        Ok(())
    }
}