use std::marker::PhantomData;
use crate::rand::{PrimitiveType, Result, Seed};
use std::collections::hash_map::DefaultHasher;
use std::time::{SystemTime, UNIX_EPOCH, Instant};
use std::hash::{Hash, Hasher};

/// The DefaultSeed implement by the system time in the non-x86/x86_64 platform

#[derive(Clone)]
pub struct DefaultSeed<T> {
    ph: PhantomData<T>
}

impl<T: PrimitiveType> DefaultSeed<T> {
    pub fn new() -> Result<Self> {
        Ok(Self {ph: PhantomData})
    }
    
    fn time_hash(&self) -> u64 {
        let mut hasher = DefaultHasher::new();
        let time = SystemTime::now();
        time.hash(&mut hasher);
        
        let dur = match time.duration_since(UNIX_EPOCH) {
            Ok(x) => x, Err(e) => e.duration(),
        };
        let (x, y) = (std::cmp::max(1, (dur.as_micros() & 0xf) as usize),
                        std::cmp::max(1, (dur.as_micros() & 0xf0) as usize));
        let (x, y) = if x < y {(y, x)} else {(x, y)};
        (0..=x).for_each(|i| {
            if i == y {
                let time = Instant::now();
                time.hash(&mut hasher);
            }
            hasher.write_usize(i);
        });
        
        hasher.finish()
    }
}

impl Seed<u32> for DefaultSeed<u32> {
    fn seed(&self) -> Result<u32> {
        Ok((self.time_hash() & (u32::MAX as u64)) as u32)
    }
}

impl Seed<u64> for DefaultSeed<u64> {
    fn seed(&self) -> Result<u64> {
        Ok(self.time_hash())
    }
}

impl Seed<usize> for DefaultSeed<usize> {
    fn seed(&self) -> Result<usize> {
        #[cfg(target_pointer_width = "32")]
            {Ok((self.time_hash() & (u32::MAX as u64)) as usize)}
        
        #[cfg(target_pointer_width = "64")]
            {Ok(self.time_hash() as usize)}
    }
}