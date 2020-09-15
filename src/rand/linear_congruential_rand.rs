/// random number generated by the Linear Congruential Algorithm
use crate::rand::{PrimitiveType, Seed, Result, RandError, RandErrKind, Source};

/// Linear Congruential Generator Algorithms
/// 
/// $$
/// x_{n+1} = (a * x_n + c) \mod m
/// $$
#[derive(Clone)]
pub struct LinearCongruentialRand<T> {
    a: T,
    c: T,
    m: T,
    x: T,
}

impl<T> LinearCongruentialRand<T> 
    where T: PrimitiveType + PartialEq + Default {
    /// $$
    /// x_{n+1} = (a * x_n + c) \mod m
    /// $$
    pub fn new<Sd: Seed<T>>(sd: &Sd, a: T, c: T, m: T) -> Result<Self> {
        if m == T::default() {
            Err(RandError::new(RandErrKind::DivisorIsZero, ""))
        } else {
            sd.seed().map(|x| {
                Self {a,c,m,x}
            })
        }
    }
}

macro_rules! lcr_calc {
    ($Type0: ty) => {
        impl Source<$Type0> for LinearCongruentialRand<$Type0> {
            fn gen(&mut self) -> Result<$Type0> {
                let tmp = (((self.a).overflowing_mul(self.x).0).overflowing_add(self.c)).0 % self.m;
                self.x = tmp;
                Ok(tmp)
            }

            fn reset<Sd: Seed<$Type0>>(&mut self, sd: &Sd) -> Result<()> {
                sd.seed().map(|x| {
                    self.x = x;
                })
            }
        }
    };
}

lcr_calc!(u32);
lcr_calc!(usize);
lcr_calc!(u64);

/// Discovered in 1969 by Lewis, Goodman and Miller, adopted as "Minimal standard" in 1988 by Park and Miller 
/// `$Sd` must be the instance of the `Seed`
#[macro_export]
macro_rules! minstd_rand0 {
    ($Sd: ident) => {
        rmath::rand::LinearCongruentialRand::new(&$Sd, 16807u32, 0u32, 2147483647)
    };
}


/// Newer "Minimum standard", recommended by Park, Miller, and Stockmeyer in 1993
/// `$Sd` must be the instance of the `Seed`
#[macro_export]
macro_rules! minstd_rand {
    ($Sd: ident) => {
        rmath::rand::LinearCongruentialRand::new(&$Sd, 48271u32, 0u32, 2147483647)
    };
}
