use std::marker::PhantomData;
use crate::rand::{Seed, PrimitiveType, Result, RandErrKind, RandError, Source};

// #[cfg(target_os = "windows")]
use crate::os::windows::bcrypt::{BCrypt, AlgorithmHandle, CNGAlgorithmIdentifier, AlgorithmHandleFlag};
#[cfg(target_os = "linux")]
use crate::os::linux::BCrypt;

#[derive(Clone)]
pub struct CryptoRand<T> {
    bcrypt: BCrypt,
    ph: PhantomData<T>,
}

impl<T: PrimitiveType> CryptoRand<T> {
    #[cfg(target_os = "windows")]
    pub fn new<Sd: Seed<T>>(_sd: &Sd) -> Result<Self> {
        let alg_id = match AlgorithmHandle::ms_primitive_provider(CNGAlgorithmIdentifier::BCRYPT_RNG_ALGORITHM,
                                                                  AlgorithmHandleFlag::default()) {
            Ok(x) => x,
            Err(e) => {
                let s = format!("{}", e);
                return Err(RandError::new(RandErrKind::InnerErr, s));
            },
        };
    
        Ok(Self {
            bcrypt: BCrypt::new(alg_id),
            ph: PhantomData
        })
    }
    
    #[cfg(target_os = "linux")]
    pub fn new<Sd: Seed<T>>(_sd: &Sd) -> Result<Self> {
        Ok(Self {
            bcrypt: BCrypt::new(),
            ph: PhantomData,
        })
    }
}

macro_rules! cr_impl {
    ($Type0: ty, $Len: literal) => {
        impl Source<$Type0> for CryptoRand<$Type0> {
            fn gen(&mut self) -> Result<$Type0> {
                let mut buf = [0u8; $Len];
                match self.bcrypt.gen_random(buf.as_mut()) {
                    Err(e) => {
                        return Err(RandError::new(RandErrKind::InnerErr, format!("{}", e)));
                    },
                    _ => {},
                };
                
                Ok(<$Type0>::from_le_bytes(buf))
            }
        
            fn reset<Sd: Seed<$Type0>>(&mut self, _sd: &Sd) -> Result<()> {
                Ok(())
            }
        }
    };
}

cr_impl!(u32, 4);
cr_impl!(u64, 8);

#[cfg(target_pointer_width = "32")]
cr_impl!(usize, 4);
#[cfg(target_pointer_width = "64")]
cr_impl!(usize, 8);
