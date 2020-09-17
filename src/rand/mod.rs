
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

pub trait IterSource<T: PrimitiveType>: Source<T> {
    fn iter_mut(&mut self) -> crate::rand::iter::Iter<'_, Self, T>
        where Self: std::marker::Sized;
}

#[macro_use]
mod iter;
pub use iter::Iter;

#[macro_use]
mod linear_congruential_rand;
pub use linear_congruential_rand::LinearCongruentialRand;
iter_impl!(LinearCongruentialRand, u32, usize, u64);

#[macro_use]
mod mersenne_twister_rand;
pub use mersenne_twister_rand::MersenneTwisterRand;
iter_impl!(MersenneTwisterRand, u32, usize, u64);

#[macro_use]
mod lagged_fibonacci_rand;
pub use lagged_fibonacci_rand::LaggedFibonacciRand;
iter_impl!(LaggedFibonacciRand, u32, usize, u64);

#[cfg(not(any(target_arch = "x86", target_arch = "x86_64")))]
mod default_seed;
#[cfg(not(any(target_arch = "x86", target_arch = "x86_64")))]
pub use default_seed::DefaultSeed;
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
mod default_seed_amd64;
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
pub use default_seed_amd64::DefaultSeed;


#[cfg(not(any(target_arch = "x86", target_arch = "x86_64")))]
mod default_rand;
#[cfg(not(any(target_arch = "x86", target_arch = "x86_64")))]
pub use default_rand::DefaultRand;
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
mod default_rand_amd64;
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
pub use default_rand_amd64::DefaultRand;
iter_impl!(DefaultRand, u32, usize, u64);


#[cfg(not(any(target_arch = "x86", target_arch = "x86_64")))]
mod crypto_rand;
#[cfg(not(any(target_arch = "x86", target_arch = "x86_64")))]
pub use crypto_rand::CryptoRand;

#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
mod crypto_rand_amd64;
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
pub use crypto_rand_amd64::CryptoRand;
iter_impl!(CryptoRand, u32, usize, u64);
