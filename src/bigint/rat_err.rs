use std::fmt::{Debug, Formatter, Result, Display};
use std::error::Error;

#[derive(Copy, Clone, Eq, PartialEq)]
pub enum RatErrKind {
    DenominatorIsZero,
    NumeratorIsZero,
    ParseStringWrong,
}

impl Debug for RatErrKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            RatErrKind::DenominatorIsZero => {
                write!(f, "{}", "DenominatorIsZero")
            },
            RatErrKind::NumeratorIsZero => {
                write!(f, "{}", "NumeratorIsZero")
            },
            RatErrKind::ParseStringWrong => {
                write!(f, "{}", "ParseStringWrong")
            }
        }
    }
}

#[derive(Debug)]
pub struct RatError {
    kind: RatErrKind,
    error: Option<Box<dyn Error + Send + Sync>>,
}

impl RatError {
    pub fn new<E>(kind: RatErrKind, error: E) -> RatError 
        where E: Into<Box<dyn Error + Sync + Send>> {
        RatError {
            kind,
            error: Some(error.into()),
        }
    }
    
    pub fn kind(&self) -> RatErrKind {
        self.kind
    }
}

impl Display for RatError {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self.error.as_ref() {
            Some(x) => std::fmt::Display::fmt(x, f),
            None => write!(f, "{:?}", self.kind),
        }
    }
}

impl Error for RatError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self.error.as_ref() {
            Some(x) => x.source(),
            None => None
        }
    }
}