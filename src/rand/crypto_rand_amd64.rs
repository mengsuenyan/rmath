use crate::rand::{DefaultRand, PrimitiveType, Seed, Result, Source};

#[derive(Clone)]
pub struct CryptoRand<T> {
    rd:DefaultRand<T>,
}

impl<T: PrimitiveType> CryptoRand<T> {
    pub fn new<Sd: Seed<T>>(sd: &Sd) -> Result<Self> {
        DefaultRand::new(sd).map(|x| {
            Self {
                rd: x,
            }
        })
    }
}

macro_rules! cr_impl {
    ($Type0: ty) => {
        impl Source<$Type0> for CryptoRand<$Type0> {
            fn gen(&mut self) -> Result<$Type0> {
                self.rd.gen()
            }
        
            fn reset<Sd: Seed<$Type0>>(&mut self, sd: &Sd) -> Result<()> {
                self.rd.reset(sd)
            }
        }
    };
}

cr_impl!(u32);
cr_impl!(usize);
cr_impl!(u64);
