/// The DefaultRand implement by the system time in the non-x86/x86_64 platform
use crate::rand::{PrimitiveType, Seed, Result, Source, DefaultSeed};

#[derive(Clone)]
pub struct DefaultRand<T> {
    seed: DefaultSeed<T>,
    state: T,
}

impl<T: PrimitiveType> DefaultRand<T> {
    pub fn new<Sd: Seed<T>>(sd: &Sd) -> Result<Self> {
        sd.seed().map(|x| {
            Self {
                seed: DefaultSeed::new().unwrap(),
                state: x,
            }
        })
    }
}

macro_rules! dr_impl {
    ($Type0: ty) => {
       impl Source<$Type0> for DefaultRand<$Type0> {
           fn gen(&mut self) -> Result<$Type0> {
               self.state = self.state ^ self.seed.seed().unwrap();
               Ok(self.state)
           }
       
           fn reset<Sd: Seed<$Type0>>(&mut self, sd: &Sd) -> Result<()> {
               sd.seed().map(|x| {
                   self.state = x;
               })
           }
       }
    };
}

dr_impl!(u32);
dr_impl!(u64);
dr_impl!(usize);
