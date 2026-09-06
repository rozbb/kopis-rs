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

/// Generates the three checks for one Kopis variant.
///
/// Each variant is a distinct set of monomorphised functions — different `L`, `MU` and `T` mean
/// different NTT and serialisation code paths — so all three have to be exercised separately.
macro_rules! variant_checks {
    ($modname:ident, $sk:ident, $ct_len:ident) => {
        mod $modname {
            use super::{black_box, classify, declassify, fill};
            use kopis::$modname::{$ct_len, $sk};

            /// Key generation from a **secret** 32-byte seed.
            ///
            /// Nothing is expected to be reported, which is not a given for a lattice KEM: a
            /// scheme that rejection-samples its public matrix would branch on values derived
            /// from a seed this check has tagged, and would need those reports allowlisted.
            /// Kopis deserialises 13-bit coefficients instead, so there is nothing to allowlist.
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

            /// Encapsulation against a public key, with **secret** encapsulation randomness.
            ///
            /// The public key is untagged: the caller of a KEM encapsulation knows it. Only the
            /// randomness — and therefore the shared secret — is secret here.
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

            /// Decapsulation with a **secret** key and a public, attacker-chosen ciphertext.
            ///
            /// This is the check that matters most: it is the oracle a chosen-ciphertext attacker
            /// actually gets to query. The ciphertext stays public because the attacker picks it.
            ///
            /// Three shapes of ciphertext are driven through, because the implicit-rejection path
            /// is only meaningful if both outcomes of the re-encryption comparison are covered,
            /// and a single mismatching bit is the case most likely to expose an early-exit
            /// comparison:
            ///   * a well-formed ciphertext, which re-encrypts to itself;
            ///   * one with a single bit flipped, which does not;
            ///   * an entirely unstructured one.
            pub fn decap() -> Vec<u8> {
                let mut out = Vec::new();
                for (ks, rs) in [(0x11u8, 0x22u8), (0x93, 0x4d)] {
                    let mut sk = $sk::from_seed(&fill(ks));
                    let (valid_ct, expected) = sk.public_key().encapsulate_deterministic(&fill(rs));

                    let mut one_bit_off = valid_ct;
                    one_bit_off[0] ^= 1;

                    let mut garbage = [0u8; $ct_len];
                    for (i, b) in garbage.iter_mut().enumerate() {
                        *b = (i as u8).wrapping_mul(31).wrapping_add(ks);
                    }

                    for (ct, should_agree) in
                        [(valid_ct, true), (one_bit_off, false), (garbage, false)]
                    {
                        // The whole expanded key is tagged, seed and PKE secret alike. That is
                        // stricter than necessary — the cached public matrix lives in here too —
                        // but a stricter tag can only add reports, never hide one.
                        classify(&mut sk);

                        let ss = sk.decapsulate(black_box(&ct));

                        declassify(&sk);
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

variant_checks!(kopis512, Kopis512SecretKey, KOPIS512_CIPHERTEXT_LEN);
variant_checks!(kopis768, Kopis768SecretKey, KOPIS768_CIPHERTEXT_LEN);
variant_checks!(kopis1024, Kopis1024SecretKey, KOPIS1024_CIPHERTEXT_LEN);

/// Negative control: code that is *supposed* to be reported.
///
/// A silently broken shim — headers from a different Valgrind, a `classify` that got inlined into
/// nothing, a run that never actually reached Valgrind — would make every other check pass for
/// the wrong reason. So `ct-check.sh --selftest` runs this and fails if Memcheck stays quiet.
///
/// Both classic leak shapes are here, since they are reported differently: a branch whose
/// direction depends on a secret, and a table index that does.
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
///
/// A check hands back the key material and shared secrets it produced. `main` sinks that through
/// `black_box` so the operation under test cannot be optimised away as an unused computation.
///
/// Every check in the table runs on every invocation. There is no way to ask for a subset: a
/// partial run is a weaker claim that looks identical to a full one in the output, and narrowing
/// saves a couple of minutes at most.
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
    check("kopis512", "decap", kopis512::decap),
    check("kopis768", "keygen", kopis768::keygen),
    check("kopis768", "encap", kopis768::encap),
    check("kopis768", "decap", kopis768::decap),
    check("kopis1024", "keygen", kopis1024::keygen),
    check("kopis1024", "encap", kopis1024::encap),
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
        println!("running selftest (Valgrind is expected to report two errors here)");
        black_box(selftest());
        return ExitCode::SUCCESS;
    }

    for c in CHECKS {
        println!("running {}/{}", c.variant, c.op);
        black_box((c.run)());
    }
    println!("ran {} check(s)", CHECKS.len());
    ExitCode::SUCCESS
}
