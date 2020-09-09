use std::fmt::{Debug, Formatter, Result};

#[derive(Copy, Clone, Eq, PartialEq)]
pub enum ParseErrKind {
    BeginWithIllegalChar,
    IllegalCharEncounter,
}

impl Debug for ParseErrKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            ParseErrKind::BeginWithIllegalChar => {
                write!(f, "{}", "The string to be parsed begin with an illegal character")
            },
            ParseErrKind::IllegalCharEncounter => {
                write!(f, "{}", "Illegal character encountered during parsing")
            }
        }
    }
}