
mod rand_error;
pub use rand_error::{RandError, RandErrKind};
pub type Result<T> = std::result::Result<T, RandError>;

/// The trait for random seed generator
pub trait Seed {
    fn seed_u32(&self) -> Result<u32>;

    fn seed_u64(&self) -> Result<u64> {
        match self.seed_u32() {
            Ok(low) => {
                self.seed_u32().map(|high| {
                    (low as u64) | ((high as u64) << 32)
                })
            },
            Err(e) => Err(e),
        }
    }

    fn seed(&self) -> Result<usize> {
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
    /// this will be reset the internal state of the Source Instance
    fn set_seed<Sd: Seed>(&mut self, sd: &Sd) -> Result<()>;
    
    /// reset the internal state
    fn reset(&mut self) -> Result<()>;
    
    fn gen_u32(&mut self) -> Result<u32>;

    fn gen_u64(&mut self) -> Result<u64> {
        match self.gen_u32() {
            Ok(low) => {
                self.gen_u32().map(|high| {
                    (low as u64) | ((high as u64) << 32)
                })
            },
            Err(e) => Err(e),
        }
    }

    fn gen(&mut self) -> Result<usize> {
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

mod linear_congruential_rand;

mod default_seed;

mod default_seed_amd64;
pub use default_seed_amd64::DefaultSeed;


mod default_rand;

mod default_rand_amd64;
pub use default_rand_amd64::DefaultRand;

