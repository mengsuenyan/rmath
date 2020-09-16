
fn main() {
    let os = {
        #[cfg(target_os = "windows")]
            {1}
        #[cfg(target_os = "linux")]
            {2}
        #[cfg(not(any(target_os = "windows", target_os = "linux")))]
            {0}
    };
    if os < 1 {
        panic!("The rmath only support the Windows/Linux system");
    }
    
    if (std::mem::size_of::<usize>() != std::mem::size_of::<u32>()) && 
        (std::mem::size_of::<usize>()) != std::mem::size_of::<u64>() {
        panic!("The rmath does support the 32bit/64bit system");
    }
    
    if std::is_x86_feature_detected!("avx2") {
        println!("cargo:rustc-cfg=rmath_avx2=\"support\"");
    }
    
    if std::is_x86_feature_detected!("rdseed") {
        println!("cargo:rustc-cfg=rmath_rdseed=\"support\"");
    }
    
    if std::is_x86_feature_detected!("rdrand") {
        println!("cargo:rustc-cfg=rmath_rdrand=\"support\"");
    }
}