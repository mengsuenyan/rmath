
/// The trait for random seed generator
pub trait Seed {
    fn seed_u32(&self) -> Option<u32>;

    fn seed_u64(&self) -> Option<u64> {
        self.seed_u32().zip(self.seed_u32()).map(|(low, high)| {
            (low as u64) | ((high as u64) << 32)
        })
    }

    fn seed(&self) -> Option<usize> {
        #[cfg(target_pointer_width = "32")]
            {
                self.seed_u32().map(|x| {x as usize})
            }
        #[cfg(target_pointer_width = "64")]
            {
                self.seed_u64().map(|x| { x as usize })
            }
    }
}

/// The trait for random number
pub trait Source {
    fn set_seed<Sd: Seed>(&mut self, sd: &Sd);
    
    /// reset the internal state
    fn reset(&mut self);
    
    fn gen_u32(&mut self) -> Option<u32>;

    fn gen_u64(&mut self) -> Option<u64> {
        self.gen_u32().zip(self.gen_u32()).map(|(low, high)| {
            (low as u64) | ((high as u64) << 32)
        })
    }

    fn gen(&mut self) -> Option<usize> {
        #[cfg(target_pointer_width = "32")]
            {
                self.gen_u32().map(|x| {x as usize})
            }

        #[cfg(target_pointer_width = "64")]
            {
                self.gen_u64().map(|x| {x as usize})
            }
    }
}

mod default_seed;

mod default_seed_amd64;
pub use default_seed_amd64::DefaultSeed;


mod default_rand;

mod default_rand_amd64;
pub use default_rand_amd64::DefaultRand;

