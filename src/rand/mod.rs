
mod rand_error;
pub use rand_error::{RandError, RandErrKind};
pub type Result<T> = std::result::Result<T, RandError>;

pub trait PrimitiveType {
    fn bits_len() -> Self;
    fn mask(&self) -> Self;
}

impl PrimitiveType for u32 {
    fn bits_len() -> Self {
        (std::mem::size_of::<u32>() << 3) as u32
    }

    fn mask(&self) -> Self {
        if self == &32 {core::u32::MAX} else {(1 << (self & 31)) - 1}
    }
}

impl PrimitiveType for usize {
    fn bits_len() -> Self {
        (std::mem::size_of::<usize>() << 3) as usize 
    }

    fn mask(&self) -> Self {
        if self == &Self::bits_len() {core::usize::MAX} else {(1 << (self & (Self::bits_len() - 1))) - 1}
    }
}
impl PrimitiveType for u64 {
    fn bits_len() -> Self {
        (std::mem::size_of::<u64>() << 3) as u64
    }

    fn mask(&self) -> Self {
        if self == &64 {core::u64::MAX} else {(1 << (self & 63)) - 1}
    }
}

pub trait Seed<T: PrimitiveType> {
    fn seed(&self) -> Result<T>;
}

pub trait Source<T: PrimitiveType> {
    fn gen(& mut self) -> Result<T>;
    
    fn reset<Sd: Seed<T>>(&mut self, sd: &Sd) -> Result<()>;
}

#[macro_use]
mod linear_congruential_rand;
pub use linear_congruential_rand::LinearCongruentialRand;

#[macro_use]
mod mersenne_twister_rand;
pub use mersenne_twister_rand::MersenneTwisterRand;

#[macro_use]
mod lagged_fibonacci_rand;
pub use lagged_fibonacci_rand::LaggedFibonacciRand;

#[cfg(not(any(target_arch = "x86", target_arch = "x86_64")))]
mod default_seed;
#[cfg(not(any(target_arch = "x86", target_arch = "x86_64")))]
pub use default_seed::DefaultSeed;

#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
mod default_seed_amd64;
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
pub use default_seed_amd64::DefaultSeed;


mod default_rand;

mod default_rand_amd64;
pub use default_rand_amd64::DefaultRand;

