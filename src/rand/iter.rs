use crate::rand::{RandError, Source, PrimitiveType};
use std::marker::PhantomData;

pub struct Iter<'a, T, P> 
    where P: PrimitiveType, T: 'a + Source<P> {
    pub(super) inner: &'a mut T,
    pub(super) last_err: Option<RandError>,
    pub(super) ph: PhantomData<P>,
}

impl<'a, T, P> Iter<'a, T, P> 
    where P: PrimitiveType, T: 'a + Source<P> {
    pub fn last_error(&self) -> Option<&RandError> {
        self.last_err.as_ref()
    }
    
    pub fn clear_error(&mut self) {
        self.last_err = None;
    }
}

impl<'a, T, P> Iterator for Iter<'a, T, P> 
    where P: PrimitiveType, T: 'a + Source<P> {
    type Item = P;

    fn next(&mut self) -> Option<Self::Item> {
        if self.last_err.is_none() {
            match self.inner.gen() {
                Ok(x) => Some(x),
                Err(e) => {
                    self.last_err = Some(e);
                    None
                }
            }
        } else {
            None
        }
    }
}

macro_rules! iter_impl {
    ($SourceType0: ident, $Type0: ty) => {
        impl $SourceType0<$Type0> {
            pub fn iter_mut(&mut self) -> crate::rand::iter::Iter<'_, Self, $Type0> {
                crate::rand::iter::Iter {
                    inner: self,
                    last_err: None,
                    ph: std::marker::PhantomData,
                }
            }
        }
    };
    ($SourceType1: ident, $Type1: ty, $($Type2: ty),+) => {
        iter_impl!($SourceType1, $Type1);
        iter_impl!($SourceType1, $($Type2),+);
    };
}
