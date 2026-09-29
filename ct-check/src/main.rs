//! Constant-time validation harness for `kopis`.
//!
//! Run it under Valgrind's Memcheck — `../ct-check.sh` does that for you. Each check tags its
//! secret inputs via [`ct_check::classify`], runs one public API operation, and declassifies the
//! outputs. Anything Memcheck reports in between is a branch or a memory access that depended on
//! a secret.
//!
//! Inputs are fixed rather than random so that a failure reproduces exactly.

use ct_check::{classify, declassify, under_valgrind};

use std::{hint::black_box, process::ExitCode};

/// Deterministic filler for seeds and randomness. Values are public; only the *tagging* decides
/// what the harness treats as secret.
fn fill(byte: u8) -> [u8; 32] {
    let mut out = [0u8; 32];
    for (i, b) in out.iter_mut().enumerate() {
        *b = byte.wrapping_mul(i as u8).wrapping_add(byte);
    }
    out
}

/// Generates the checks for one Kopis variant.
///
/// Each variant is a distinct set of monomorphised functions — different `L`, `MU` and `T` mean
/// different NTT and serialisation code paths — so every one has to be exercised separately.
macro_rules! variant_checks {
    ($modname:ident, $sk:ident, $pk:ident, $ct_len:ident, $pk_len:ident) => {
        mod $modname {
            use super::{black_box, classify, declassify, fill};
            use kopis::$modname::{$ct_len, $pk, $pk_len, $sk};

            /// Key generation from a **secret** 32-byte seed. Checks constant-timeness wrt `seed`
            pub fn keygen() -> Vec<u8> {
                let mut out = Vec::new();
                for v in [0x11u8, 0xa7, 0xfe] {
                    let mut seed = fill(v);
                    classify(&mut seed);

                    let sk = $sk::from_seed(&seed);

                    declassify(&sk);
                    declassify(&seed);
                    out.extend_from_slice(sk.seed());
                    out.extend_from_slice(&sk.public_key().to_bytes());
                }
                out
            }

            /// Encapsulation against an already-expanded public key. Must be constant-time wrt the
            /// encapsulation randomness.
            pub fn encap() -> Vec<u8> {
                let mut out = Vec::new();
                for (ks, rs) in [(0x11u8, 0x22u8), (0x00, 0xff), (0x5c, 0x01)] {
                    let sk = $sk::from_seed(&fill(ks));
                    let pk = sk.public_key();

                    let mut randomness = fill(rs);
                    classify(&mut randomness);

                    let (ct, ss) = pk.encapsulate_deterministic(&randomness);

                    declassify(&randomness);
                    declassify(&ct);
                    declassify(ss.as_bytes());
                    out.extend_from_slice(&ct);
                    out.extend_from_slice(ss.as_bytes());
                }
                out
            }

            /// Deserialize a public key, then encapsulate to it. Must be constant-time wrt the
            /// public key bytes (not true in ML-KEM) and the encapsulation randomness.
            pub fn import_encap() -> Vec<u8> {
                let mut out = Vec::new();
                for (ps, rs) in [(0x3du8, 0x22u8), (0x00, 0xff), (0xff, 0x5c)] {
                    let mut pk_bytes = [0u8; $pk_len];
                    for (i, b) in pk_bytes.iter_mut().enumerate() {
                        *b = (i as u8).wrapping_mul(ps).wrapping_add(ps);
                    }
                    classify(&mut pk_bytes);

                    let pk = $pk::from_bytes(&pk_bytes);

                    let mut randomness = fill(rs);
                    classify(&mut randomness);

                    let (ct, ss) = pk.encapsulate_deterministic(&randomness);

                    // `pk` is declassified along with its source bytes: the expanded key holds
                    // the tags too, and leaving them on stack memory that later checks reuse
                    // would blur whose tag a report belongs to.
                    declassify(&pk);
                    declassify(&pk_bytes);
                    declassify(&randomness);
                    declassify(&ct);
                    declassify(ss.as_bytes());
                    out.extend_from_slice(&ct);
                    out.extend_from_slice(ss.as_bytes());
                }
                out
            }

            /// Decapsulate an attacker-chosen ciphertext. Must be constant-time in the
            /// ciphertext and the decapsulation key.
            pub fn decap() -> Vec<u8> {
                let mut out = Vec::new();
                for (ks, rs) in [(0x11u8, 0x22u8), (0x93, 0x4d)] {
                    // Test wrt a correct ciphertext, a bit-flipped ciphertext, and a random
                    // ciphertext

                    let mut sk = $sk::from_seed(&fill(ks));
                    let (valid_ct, expected) = sk.public_key().encapsulate_deterministic(&fill(rs));

                    let mut one_bit_off = valid_ct;
                    one_bit_off[0] ^= 1;

                    let mut garbage = [0u8; $ct_len];
                    for (i, b) in garbage.iter_mut().enumerate() {
                        *b = (i as u8).wrapping_mul(31).wrapping_add(ks);
                    }

                    for (mut ct, should_agree) in
                        [(valid_ct, true), (one_bit_off, false), (garbage, false)]
                    {
                        // Impl must be constant-time in both sk and ct
                        classify(&mut sk);
                        classify(&mut ct);

                        let ss = sk.decapsulate(black_box(&ct));

                        declassify(&sk);
                        declassify(&ct);
                        declassify(ss.as_bytes());

                        // Both sides are declassified, so comparing them is not itself a leak.
                        // This is here to notice if the operation under test ever stops actually
                        // running: a decapsulation the optimiser deleted, or one left broken by a
                        // refactor, would report zero errors and look exactly like a clean pass.
                        assert_eq!(
                            ss.as_bytes() == expected.as_bytes(),
                            should_agree,
                            "{}/decap produced the wrong shared secret",
                            stringify!($modname),
                        );

                        out.extend_from_slice(ss.as_bytes());
                    }
                }
                out
            }
        }
    };
}

variant_checks!(
    kopis512,
    Kopis512SecretKey,
    Kopis512PublicKey,
    KOPIS512_CIPHERTEXT_LEN,
    KOPIS512_PUBKEY_LEN
);
variant_checks!(
    kopis768,
    Kopis768SecretKey,
    Kopis768PublicKey,
    KOPIS768_CIPHERTEXT_LEN,
    KOPIS768_PUBKEY_LEN
);
variant_checks!(
    kopis1024,
    Kopis1024SecretKey,
    Kopis1024PublicKey,
    KOPIS1024_CIPHERTEXT_LEN,
    KOPIS1024_PUBKEY_LEN
);

/// Should-panic test. Make a data-dependent for loop bound and see if Valgrind catches it
fn selftest() -> u8 {
    let mut secret = [0u8; 32];
    secret[0] = 7;
    classify(&mut secret);
    let s = &secret;

    // Expected: "Conditional jump or move depends on uninitialised value(s)". This is a
    // secret-dependent loop bound rather than a plain `if`, because LLVM flattens a small `if`
    // into branchless arithmetic — which is, after all, the transformation we *want* it to make
    // everywhere else. A trip count survives.
    let mut acc = 0u8;
    for _ in 0..(s[0] & 7) {
        acc = acc.wrapping_add(black_box(1));
    }

    // Expected: "Use of uninitialised value of size 8" at the load. The index is a `u8` into a
    // 256-entry table, so there is no bounds check in the way; the address itself is the secret.
    // The table has to hold distinct values or the load folds to a constant and there is nothing
    // left to observe.
    let mut table = [0u8; 256];
    for (i, e) in table.iter_mut().enumerate() {
        *e = i as u8;
    }
    acc ^= black_box(table[s[1] as usize]);

    declassify(&secret);
    black_box(acc)
}

/// One runnable check: parameter set, operation name, and the body.
struct Check {
    variant: &'static str,
    op: &'static str,
    run: fn() -> Vec<u8>,
}

/// Shorthand so the table below stays readable.
const fn check(variant: &'static str, op: &'static str, run: fn() -> Vec<u8>) -> Check {
    Check { variant, op, run }
}

/// Every (variant, operation) pair the harness knows how to run.
const CHECKS: &[Check] = &[
    check("kopis512", "keygen", kopis512::keygen),
    check("kopis512", "encap", kopis512::encap),
    check("kopis512", "import_encap", kopis512::import_encap),
    check("kopis512", "decap", kopis512::decap),
    check("kopis768", "keygen", kopis768::keygen),
    check("kopis768", "encap", kopis768::encap),
    check("kopis768", "import_encap", kopis768::import_encap),
    check("kopis768", "decap", kopis768::decap),
    check("kopis1024", "keygen", kopis1024::keygen),
    check("kopis1024", "encap", kopis1024::encap),
    check("kopis1024", "import_encap", kopis1024::import_encap),
    check("kopis1024", "decap", kopis1024::decap),
];

const USAGE: &str = "\
usage: ct-check [--selftest]

  --selftest  run the negative control instead of the checks: deliberately leaky code that
              Valgrind must report. Used to prove the harness can see a leak at all.

Meant to be run under Valgrind; `./ct-check.sh` in the repo root does that.
";

fn main() -> ExitCode {
    let mut selftest_only = false;

    for arg in std::env::args().skip(1) {
        match arg.as_str() {
            "-h" | "--help" => {
                print!("{USAGE}");
                return ExitCode::SUCCESS;
            }
            "--selftest" => selftest_only = true,
            other => {
                eprintln!("ct-check: unrecognised argument `{other}`\n\n{USAGE}");
                return ExitCode::FAILURE;
            }
        }
    }

    if !under_valgrind() {
        eprintln!(
            "ct-check: not running under Valgrind, so nothing is being checked. \
             Use `./ct-check.sh` instead."
        );
    }

    if selftest_only {
        println!("running selftest (Valgrind is expected to report errors here)");
        black_box(selftest());
        black_box(selftest_public_key());
        return ExitCode::SUCCESS;
    }

    for c in CHECKS {
        println!("running {}/{}", c.variant, c.op);
        black_box((c.run)());
    }
    println!("ran {} check(s)", CHECKS.len());
    ExitCode::SUCCESS
}
