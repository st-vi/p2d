use std::env;
use std::path::PathBuf;

fn main() {
    // Get the target platform (e.g., x86_64-unknown-linux-gnu)
    let target = env::var("TARGET").unwrap();

    // Path to your bundled PaToH library
    let lib_dir = PathBuf::from(env::var("CARGO_MANIFEST_DIR").unwrap()).join("lib/patoh");

    // Add the directory containing the library to the linker search path
    println!("cargo:rustc-link-search=native={}", lib_dir.display());

    // If you're using a static library (libpatoh.a), link statically
    if target.contains("linux") || target.contains("darwin") {
        // Linux or macOS, static linking
        println!("cargo:rustc-link-lib=static=patoh");
    } else if target.contains("windows") {
        // Windows, dynamic linking
        println!("cargo:rustc-link-lib=dylib=patoh");
    } else {
        panic!("Unsupported platform");
    }

    // Rebuild if the library changes
    println!("cargo:rerun-if-changed=libs/libpatoh.a");
    println!("cargo:rerun-if-changed=libs/libpatoh.so");
}
