use std::env;
use std::path::PathBuf;
use std::process::Command;

use rustc_version::Channel;

fn main() {
    check_nightly_version();

    let sysroot = Command::new(env::var("RUSTC").unwrap())
        .arg("--print=sysroot")
        .output()
        .expect("Could not invoke rustc to find rust sysroot");
    let sysroot = String::from_utf8(sysroot.stdout)
        .expect("Rust sysroot path contains a non-UTF8 character")
        .trim()
        .to_string();

    let mut rustlib_path = PathBuf::new();
    rustlib_path.push(sysroot);
    rustlib_path.push("lib/rustlib");
    rustlib_path.push(env::var("TARGET").unwrap());
    rustlib_path.push("lib");
    let path_string = rustlib_path
        .into_os_string()
        .into_string()
        .expect("Unexpected non-Unicode character in rustlib path");
    println!("cargo:rustc-env=RUSTLIB={}", path_string);
}

// This can be simplified into Cargo.toml if
// https://github.com/rust-lang/rfcs/pull/2495 ever lands.
fn check_nightly_version() {
    let version = rustc_version::version_meta()
        .expect("Could not find rustc version");
    if version.channel != Channel::Nightly {
        panic!(
            "C2Rust requires rustc nightly, but version {} was found",
            version.semver,
        );
    }
}
