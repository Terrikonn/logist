//! This build script detects target platforms that lack proper support for
//! atomics and sets `cfg` flags accordingly.

use std::{
    env,
    str,
};

fn main() {
    let target = match rustc_target() {
        Some(target) => target,
        None => return,
    };

    if target_has_atomic_cas(&target) {
        println!("cargo:rustc-cfg=atomic_cas");
    }

    if target_has_atomics(&target) {
        println!("cargo:rustc-cfg=has_atomics");
    }

    println!("cargo:rerun-if-changed=build.rs");
}

fn target_has_atomic_cas(target: &str) -> bool {
    ![
        "thumbv6m-none-eabi",
        "msp430-none-elf",
        "riscv32i-unknown-none-elf",
        "riscv32imc-unknown-none-elf",
    ]
    .contains(&target)
}

fn target_has_atomics(target: &str) -> bool {
    ![
        "msp430-none-elf",
        "riscv32i-unknown-none-elf",
        "riscv32imc-unknown-none-elf",
    ]
    .contains(&target)
}

fn rustc_target() -> Option<String> {
    env::var("TARGET").ok()
}
