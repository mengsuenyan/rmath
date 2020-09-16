use crate::os::windows::bcrypt::NTSTATUS;
use std::fmt::{Debug, Formatter, Display};
use std::error::Error;

pub(crate) const STATUS_SUCCESS: NTSTATUS = 0x00000000;

/// An invalid parameter was passed to a service or function.
pub(crate) const STATUS_INVALID_PARAMETER: NTSTATUS = NTSTATUS::from_le_bytes(0xC000000Du32.to_le_bytes()); // winnt

/// An invalid HANDLE was specified.
pub(crate) const STATUS_INVALID_HANDLE: NTSTATUS = NTSTATUS::from_le_bytes(0xC0000008u32.to_le_bytes());    // winnt

pub(crate) const STATUS_NOT_FOUND: NTSTATUS = NTSTATUS::from_le_bytes(0xC0000225u32.to_le_bytes());

/// Not enough virtual memory or paging file quota is available to complete the specified operation.
pub(crate) const STATUS_NO_MEMORY: NTSTATUS  = NTSTATUS::from_le_bytes(0xC0000017u32.to_le_bytes());    // winnt


pub struct NtErrorKind {
    kind: NTSTATUS
}

#[derive(Debug)]
pub struct NtError {
    kind: NtErrorKind,
    err: Option<Box<dyn Error + Sync + Send>>,
}

impl NtError {
    pub(crate) fn new<E>(kind: NtErrorKind, err: E) -> Self
        where E: Into<Box<dyn Error + Sync +Send>> {
        Self {
            kind,
            err: Some(err.into()),
        }
    }
}

impl Display for NtError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self.err.as_ref() {
            Some(x) => {
                write!(f, "{:?}, source: {}", self.kind, x)
            },
            None => {
                write!(f, "{:?}", self.kind)
            }
        }
    }
}

impl Error for NtError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self.err.as_ref() {
            Some(x) => x.source(),
            None => None
        }
    }
}


impl NtErrorKind {
    pub(crate) fn new(status: NTSTATUS) -> Self {
        NtErrorKind {kind: status}
    }
    
    fn msg_map(&self) -> &'static str {
        let msg: &'static str = if self.kind == STATUS_INVALID_HANDLE {
            "invalid handle was specified"
        } else if self.kind == STATUS_NO_MEMORY {
            "Not enough virtual memory or paging file quota is available to complete the specified operation"
        } else if self.kind == STATUS_INVALID_PARAMETER {
            "An invalid parameter was passed to a service or function"
        } else if self.kind == STATUS_NOT_FOUND {
            "The object not found"
        }
        else {
            ""
        };
        
        msg
    }
}

impl Debug for NtErrorKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let msg = self.msg_map();
        write!(f, "code: {:#x}, msg: {}", self.kind, msg)
    }
}