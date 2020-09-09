use crate::parse_err::ParseErrKind;
use std::error::Error;
use std::fmt::{Display, Formatter, Result, Debug};

#[derive(Debug)]
pub struct NatError {
    kind: ParseErrKind,
    error: Option<Box<dyn Error + Send + Sync>>,
}

impl NatError {
    pub fn new<E>(kind: ParseErrKind, error: E) -> NatError 
        where E: Into<Box<dyn Error+Sync+Send>>{
        NatError {kind, error: Some(error.into())}
    }
    
    pub fn kind(&self) -> ParseErrKind {
        self.kind
    }
}

impl Display for NatError {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self.error.as_ref() {
            Some(x) => std::fmt::Display::fmt(x, f),
            None => write!(f, "{:?}", self.kind),
        }
    }
}

impl Error for NatError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self.error.as_ref() {
            Some(x) => x.source(),
            None => None
        }
    }
}