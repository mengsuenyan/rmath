use crate::os::windows::winnt::{PVOID, LONG};
use crate::os::windows::minwindef::ULONG;
use crate::os::windows::ntstatus::{NtError, NtErrorKind, STATUS_SUCCESS};
use std::rc::Rc;
use std::os::windows::ffi::{OsStrExt, EncodeWide};
use std::ffi::OsStr;

pub type BCRYPT_ALG_HANDLE = PVOID;
pub type NTSTATUS = LONG;

mod inner {
    use crate::os::windows::bcrypt::{BCRYPT_ALG_HANDLE, NTSTATUS};
    use crate::os::windows::winnt::LPCWSTR;
    use crate::os::windows::minwindef::{ULONG, PUCHAR};
    
    pub const CNG_ALGORITHM_ID: [&'static str; 1] = [
        "RNG"
    ];
    
    #[link(name = "bcrypt")]
    extern "system" {
        pub fn BCryptOpenAlgorithmProvider(phAlgorithm: *mut BCRYPT_ALG_HANDLE, pszAlgId: LPCWSTR, pszImplementation: LPCWSTR, dwFlags: ULONG) -> NTSTATUS;
        pub fn BCryptGenRandom(hAlgorithm: BCRYPT_ALG_HANDLE, pbBuffer: PUCHAR, cbBuffer: ULONG, dwFlags: ULONG) -> NTSTATUS;
        pub fn BCryptCloseAlgorithmProvider(hAlgorithm: BCRYPT_ALG_HANDLE, dwFlags: ULONG) -> NTSTATUS;
    }
}


#[repr(C)]
#[derive(Copy, Clone)]
pub enum CNGAlgorithmIdentifier {
    BCRYPT_RNG_ALGORITHM = 0,
}

impl OsStrExt for CNGAlgorithmIdentifier {
    fn encode_wide(&self) -> EncodeWide {
        let cngid = inner::CNG_ALGORITHM_ID[(*self) as usize];
        let osstr: &OsStr = cngid.as_ref();
        osstr.encode_wide()
    }
}

#[derive(Copy, Clone)]
pub struct AlgorithmHandleFlag(ULONG);

impl Default for AlgorithmHandleFlag {
    fn default() -> Self {
        Self(0)
    }
}

pub struct AlgorithmHandle {
    handle: BCRYPT_ALG_HANDLE 
}

impl Drop for AlgorithmHandle {
    fn drop(&mut self) {
        unsafe {
            inner::BCryptCloseAlgorithmProvider(self.handle, 0);
        }
    }
}

impl AlgorithmHandle {
    pub const fn alg_handle_hmac_flag() -> AlgorithmHandleFlag {
        AlgorithmHandleFlag(0x00000008)
    }

    pub const fn pro_dispatch_flag() ->  AlgorithmHandleFlag {
        AlgorithmHandleFlag(0x00000001)
    }

    pub const fn hash_reusable_flag() -> AlgorithmHandleFlag {
        AlgorithmHandleFlag(0x00000020)
    }
    
    fn open_algorithm_provider(alg_id: *const u16, implementation: *const u16, flag: ULONG) -> std::result::Result<Self, NtError> {
        let mut handle = std::ptr::null_mut();
        let ntstatus = unsafe {
            inner::BCryptOpenAlgorithmProvider(&mut handle, alg_id, implementation, flag)
        };
        
        if ntstatus == STATUS_SUCCESS {
            Ok(Self {handle})
        } else {
            Err(NtError::new(NtErrorKind::new(ntstatus), "BCryptOpenAlgorithmProvider"))
        }
    }
    
    /// Identifies the basic Microsoft CNG provider. 
    pub fn ms_primitive_provider(alg_id: CNGAlgorithmIdentifier, flag: AlgorithmHandleFlag) -> std::result::Result<Self, NtError> {
        let p: &OsStr = "Microsoft Primitive Provider".as_ref();
        let mut v: Vec<u16> = p.encode_wide().collect();
        v.push(0);
        let mut alg_id: Vec<u16> = alg_id.encode_wide().collect();
        alg_id.push(0);
        Self::open_algorithm_provider(alg_id.as_ptr(), v.as_ptr(), flag.0)
    }
    
    /// Identifies the TPM key storage provider that is provided by Microsoft.
    pub fn ms_platform_crypto_provider(alg_id: CNGAlgorithmIdentifier, flag: AlgorithmHandleFlag) -> std::result::Result<Self, NtError> {
        let p: &OsStr = "Microsoft Platform Crypto Provider".as_ref();
        let v: Vec<u16> = p.encode_wide().collect();
        let mut alg_id: Vec<u16> = alg_id.encode_wide().collect();
        alg_id.push(0);
        Self::open_algorithm_provider(alg_id.as_ptr(), v.as_ptr(), flag.0)
    }

    pub fn auto_select_provider(alg_id: CNGAlgorithmIdentifier, flag: AlgorithmHandleFlag) -> std::result::Result<Self, NtError> {
        let mut alg_id: Vec<u16> = alg_id.encode_wide().collect();
        alg_id.push(0);
        Self::open_algorithm_provider(alg_id.as_ptr(), std::ptr::null(), flag.0)
    }
}

#[derive(Clone)]
pub struct BCrypt {
    agl_hd: Rc<AlgorithmHandle>,
}

impl BCrypt {
    pub fn new(agl_hd: AlgorithmHandle) -> Self {
        Self {
            agl_hd: Rc::new(agl_hd),
        }
    }
    
    pub fn gen_random(&mut self, buf: &mut [u8]) -> std::result::Result<(), NtError> {
        let ntstatus = unsafe {
            inner::BCryptGenRandom(self.agl_hd.handle, buf.as_mut_ptr(), buf.len() as ULONG, 0)
        };
        
        if ntstatus == STATUS_SUCCESS {
            Ok(())
        } else {
            Err(NtError::new(NtErrorKind::new(ntstatus), "BCryptGenRandom"))
        }
    }
}

