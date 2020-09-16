use std::fmt::{Debug, Formatter, Display};
use std::error::Error;

#[derive(Copy, Clone, Eq, PartialEq)]
pub enum RandErrKind {
    NoNewRandSeedGen,
    NoNewRandNumberGen,
    DivisorIsZero,
    InvalidRngPara,
    InnerErr,
}

impl Debug for RandErrKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            RandErrKind::NoNewRandSeedGen => write!(f, "{}", "NoNewRandSeedGen"),
            RandErrKind::NoNewRandNumberGen => write!(f, "{}", "NoNewRandNumberGen"),
            RandErrKind::DivisorIsZero => write!(f, "{}", "DivisorIsZero"),
            RandErrKind::InvalidRngPara => write!(f, "{}", "InvalidRngPara"),
            RandErrKind::InnerErr => write!(f, "{}", "InnerErr"),
        }
    }
}

#[derive(Debug)]
pub struct RandError {
    kind: RandErrKind,
    error: Option<Box<dyn Error + Send + Sync>>,
}

impl RandError {
    pub fn new<E>(kind: RandErrKind, error: E) -> RandError 
        where E: Into<Box<dyn Error + Sync +Send>>{
        RandError {
            kind,
            error: Some(error.into()),
        }
    }
    
    pub fn kind(&self) -> RandErrKind {
        self.kind
    }
}

impl Display for RandError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self.error.as_ref() {
            Some(x) => std::fmt::Display::fmt(x, f),
            None => write!(f, "{:?}", self.kind),
        }
    }
}

impl Error for RandError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self.error.as_ref() {
            Some(x) => x.source(),
            None => None
        }
    }
}
