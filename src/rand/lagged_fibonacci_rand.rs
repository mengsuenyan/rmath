use crate::rand::{PrimitiveType, Seed, Result, RandError, RandErrKind, LinearCongruentialRand, Source};
use std::fmt::Debug;
use std::cell::Cell;

/// implements a subtract-with-carry(lagged Fibonacci) algorithm

/// lagged fibonacci algorithm
/// $$
/// x_{i} = (x_{i-s} - x_{i-r} - carry_{i-1}) \bmod m
/// $$
#[derive(Clone)]
pub struct LaggedFibonacciRand<T> {
    word_size: T,
    short_lag: T,
    long_lag: T,
    
    seed: std::result::Result<T, T>,
    carry: T,
    idx: T,
    state: Vec<T>,
}

impl<T> LaggedFibonacciRand<T> 
    where T: PrimitiveType + Default + PartialOrd + Debug {

    /// `w`: word size in number bits to determine the range of values generated by the Rand, 0 < w <= (sizeof(T)*8);
    /// `r`: the size of the internal state
    /// `s`: lagged step when compute the current state, $0 < s < r$
    pub fn new<Sd: Seed<T>>(sd: &Sd, w: T, s: T, r: T) -> Result<Self> {
        if w == T::default() || s == T::default() || r == T::default() {
            Err(RandError::new(RandErrKind::InvalidRngPara, format!("all parameters cannot be the {:?}", T::default())))
        } else if s >= r {
            Err(RandError::new(RandErrKind::InvalidRngPara, "s must be less than the r"))
        } else if w > T::bits_len() {
            Err(RandError::new(RandErrKind::InvalidRngPara, format!("w must be less than or equal to {:?}", T::bits_len())))
        } else {
            sd.seed().map(|x| {
                Self {
                    word_size: w,
                    short_lag: s,
                    long_lag: r,
                    seed: Err(x),
                    carry: T::default(),
                    idx: T::default(),
                    state: Vec::new(),
                }
            })
        }
    }
}

/// only used for the LaggedFibonacciRand initialization
struct OnceSeed<T> {
    seed: Cell<Option<T>>,
}

impl<T> OnceSeed<T> {
    fn new(seed: T) -> Result<Self> {
        Ok(Self{ seed: Cell::new(Some(seed)) })
    }
}

impl<T: PrimitiveType> Seed<T> for OnceSeed<T> {
    fn seed(&self) -> Result<T> {
        self.seed.take().ok_or(RandError::new(RandErrKind::NoNewRandSeedGen, "OnceSeed only generate seed once"))
    }
}

macro_rules! lfr_impl {
    ($Type0: ty) => {
        impl LaggedFibonacciRand<$Type0> {
            fn check_init(&mut self)  {
                match self.seed {
                    Err(x) => {
                        let once_seed = OnceSeed::new(x).unwrap();
                        let mut lcr = LinearCongruentialRand::new(&once_seed, 40014, 0, 2147483563).unwrap();
                        let n = ((self.word_size + 31) >> 5) as usize;
                        self.state.clear();
                        (0..(self.long_lag as usize)).for_each(|_i| {
                            let (mut sum, mut factor) = (<$Type0>::default(), 1);
                            (0..n).for_each(|_j| {
                                sum = sum.overflowing_add(lcr.gen().unwrap().overflowing_mul(factor).0).0;
                                factor = factor.overflowing_mul( if <$Type0>::bits_len() <= 32 {0} else {(32 as $Type0).mask() + 1}).0;
                            });
                            self.state.push(self.word_size.mask() & sum);
                        });
                        self.carry = if self.state.last().unwrap_or(&<$Type0>::default()) == &<$Type0>::default() {1} else {0};
                        self.idx = 0;
                        self.seed = Ok(x);
                    },
                    _ => {},
                }
            }
        }
        
        impl Source<$Type0> for LaggedFibonacciRand<$Type0> {
            fn gen(&mut self) -> Result<$Type0> {
                self.check_init();
                let ps = if self.idx < self.short_lag {(self.long_lag + self.idx) - self.short_lag} else {self.idx - self.short_lag} as usize;
                let idx = self.idx as usize;
                let carry = self.carry;
                let xi = if self.state[ps] >= (self.state[idx] + self.carry) {
                    self.carry = 0;
                    (self.state[ps].overflowing_sub(self.state[idx]).0).overflowing_sub(carry).0
                } else {
                    self.carry = 1;
                    let w = if self.word_size == <$Type0>::bits_len() {<$Type0>::default()} else {1 << self.word_size};
                    ((w.overflowing_sub(self.state[idx]).0).overflowing_sub(carry).0).overflowing_add(self.state[ps]).0
                };
                
                self.state[idx] = xi;
                self.idx += 1;
                if self.idx >= self.long_lag {self.idx = 0;}
                Ok(xi)
            }
        
            fn reset<Sd: Seed<$Type0>>(&mut self, sd: &Sd) -> Result<()> {
                sd.seed().map(|x| {
                    self.seed = Err(x);
                    self.check_init();
                })
            }
        }
    };
}
        
lfr_impl!(u32);
lfr_impl!(u64);
lfr_impl!(usize);

/// 24-bit RANLUX generator by Martin Lüscher and Fred James, 1994
#[macro_export]
macro_rules! ranlux24_base {
    ($Sd: ident) => {
        rmath::rand::LaggedFibonacciRand::new(&$Sd, 24, 10, 24)
    };
}

/// 48-bit RANLUX generator by Martin Lüscher and Fred James, 1994
#[macro_export]
macro_rules! ranlux48_base {
    ($Sd: ident) => {
        rmath::rand::LaggedFibonacciRand::new(&$Sd, 48, 5, 12)
    };
}