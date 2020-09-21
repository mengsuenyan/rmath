//! the rand mod provide the generation of random number and random seed 
//! 
//! # Examples
//! 
//! ```Rust
//! use rmath::rand::{DefaultSeed, DefaultRand, Seed, CryptoRand, IterSource};
//! let s = DefaultSeed::<u32>::new().unwrap();
//! let s64 = DefaultSeed::<u64>::new().unwrap();
//! println!("{:#x}", s.seed().unwrap());
//! println!("{:#x}", s64.seed().unwrap());
//! let mut rander = DefaultRand::new(&s).unwrap();
//! let mut rander_64 = DefaultRand::new(&s64).unwrap();
//! let mut lcr0 = rmath::minstd_rand0!(s).unwrap();
//! let mut lcr = rmath::minstd_rand!(s).unwrap();
//! let mut mtr= rmath::mt19937!(s).unwrap();
//! let mut mtr_64 = rmath::mt19937_64!(s64).unwrap();
//! let mut lfr = rmath::ranlux24_base!(s).unwrap();
//! let mut lfr_64 = rmath::ranlux48_base!(s64).unwrap();
//! let mut crypto_rand = CryptoRand::new(&s).unwrap();
//! let mut crypto_rand_64 = CryptoRand::new(&s64).unwrap();
//! println!("======================================================");
//! let dr_itr = rander.iter_mut();
//! dr_itr.take(10).for_each(|x| {
//!     println!("{:#x}", x);
//! });
//! println!("======================================================");
//! let dr_itr = rander_64.iter_mut();
//! dr_itr.take(10).for_each(|x| {
//!     println!("{:#x}", x);
//! });
//! println!("======================================================");
//! let dr_itr = lcr0.iter_mut();
//! dr_itr.take(10).for_each(|x| {
//!     println!("{:#x}", x);
//! });
//! println!("======================================================");
//! let dr_itr = lcr.iter_mut();
//! dr_itr.take(10).for_each(|x| {
//!     println!("{:#x}", x);
//! });
//! println!("======================================================");
//! let dr_itr = mtr.iter_mut();
//! dr_itr.take(10).for_each(|x| {
//!     println!("{:#x}", x);
//! });
//! println!("======================================================");
//! let dr_itr = mtr_64.iter_mut();
//! dr_itr.take(10).for_each(|x| {
//!     println!("{:#x}", x);
//! });
//! println!("======================================================");
//! let dr_itr = lfr_64.iter_mut();
//! dr_itr.take(10).for_each(|x| {
//!     println!("{:#x}", x);
//! });
//! println!("======================================================");
//! let dr_itr = lfr.iter_mut();
//! dr_itr.take(10).for_each(|x| {
//!     println!("{:#x}", x);
//! });
//! println!("======================================================");
//! let dr_itr = crypto_rand.iter_mut();
//! dr_itr.take(10).for_each(|x| {
//!     println!("{:#x}", x);
//! });
//! println!("======================================================");
//! let dr_itr = crypto_rand_64.iter_mut();
//! dr_itr.take(10).for_each(|x| {
//!     println!("{:#x}", x);
//! });
//! ```

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
