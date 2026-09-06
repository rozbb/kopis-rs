#![no_std]
//! Forces monomorphisation of every kopis operation.
//!
//! The crate's whole API is const-generic, so a `libkopis.rlib` built on its own contains no
//! instantiated KEM code at all — a disassembler pointed at it would report a clean bill for an
//! empty file. `scan-instrs.py` builds this crate instead, for each target and backend, and
//! disassembles both rlibs: kopis code ends up spread across the two.
//!
//! Nothing here needs to run, or even to link. It only needs to exist in the object code.

/// One `extern "C"` entry point per parameter set, exercising keygen, encapsulation and
/// decapsulation so that every generic instance is codegen'd.
macro_rules! probe {
    ($f:ident, $m:ident, $sk:ident, $ct_len:ident) => {
        #[unsafe(no_mangle)]
        pub extern "C" fn $f(seed: &[u8; 32], randomness: &[u8; 32], out: &mut [u8; 32]) {
            use kopis::$m::{$ct_len, $sk};

            let sk = $sk::from_seed(seed);
            let (ct, _): ([u8; $ct_len], _) = sk.public_key().encapsulate_deterministic(randomness);
            let ss = sk.decapsulate(&ct);
            out.copy_from_slice(ss.as_bytes());
        }
    };
}

probe!(
    probe512,
    kopis512,
    Kopis512SecretKey,
    KOPIS512_CIPHERTEXT_LEN
);
probe!(
    probe768,
    kopis768,
    Kopis768SecretKey,
    KOPIS768_CIPHERTEXT_LEN
);
probe!(
    probe1024,
    kopis1024,
    Kopis1024SecretKey,
    KOPIS1024_CIPHERTEXT_LEN
);
