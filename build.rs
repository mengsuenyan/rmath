
fn main() {
    if std::is_x86_feature_detected!("avx2") {
        println!("cargo:rustc-cfg=rmath_avx2=\"support\"");
    }

    // if std::is_x86_feature_detected!("rdrand") {
    //     println!("cargo:rustc-cfg=rdrand_is_support");
    // }
}