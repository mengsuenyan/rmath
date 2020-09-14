
mod rand_error;
pub use rand_error::{RandError, RandErrKind};
pub type Result<T> = std::result::Result<T, RandError>;

pub trait PrimitiveType {}

impl PrimitiveType for u32 {}
impl PrimitiveType for usize {}
impl PrimitiveType for u64 {}

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


mod default_seed;

mod default_seed_amd64;
pub use default_seed_amd64::DefaultSeed;


mod default_rand;

mod default_rand_amd64;
pub use default_rand_amd64::DefaultRand;

