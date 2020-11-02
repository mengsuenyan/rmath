use std::fmt::{Debug, Formatter, Display};
use std::error::Error;

#[derive(Copy, Clone, Eq, PartialEq)]
pub enum FloatErrKind {
    ExponentOverflow,
    ExponentUnderflow,
    ParseStringWrong,
}

impl Debug for FloatErrKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            FloatErrKind::ParseStringWrong => {
                write!(f, "{}", "ParseStringWrong")
            }
            FloatErrKind::ExponentOverflow=> {
                write!(f, "{}", "ExponentOverflow")
            }
            FloatErrKind::ExponentUnderflow=> {
                write!(f, "{}", "ExponentUnderflow")
            }
        }
    }
}

#[derive(Debug)]
pub struct FloatError {
    kind: FloatErrKind,
    error: Option<Box<dyn Error + Send + Sync>>,
}

impl FloatError {
    pub fn new<E>(kind: FloatErrKind, error: E) -> FloatError 
        where E: Into<Box<dyn Error + Sync + Send>>{
        FloatError {
            kind,
            error: Some(error.into()),
        }
    }
    
    pub fn kind(&self) -> FloatErrKind {
        self.kind
    }
}

impl Display for FloatError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self.error.as_ref() {
            Some(x) => std::fmt::Display::fmt(x, f),
            None => write!(f, "{:?}", self.kind),
        }
    }
}

impl Error for FloatError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self.error.as_ref() {
            Some(x) => x.source(),
            None => None
        }
    }
}