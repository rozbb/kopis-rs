//! This module runs known-answer tests (KATs) using the test vectors distributed with the pqm4
//! implementation of Kopis.
//!
//! Vectors are read from `pqm4_test_vectors-kopis<LEVEL>-<IMPL>.txt`, where `<LEVEL>` is 512, 768,
//! or 1024, and `<IMPL>` is `speed` or `stack` (the two pqm4 implementations of each parameter
//! set, which must agree with each other and with us). Every line that starts with `#` is a
//! comment and is skipped, as are blank lines. The remaining lines come in groups of 6, one group
//! per test vector, with the labels appearing in this fixed order:
//!
//! * `keyseed`: The 32-byte seed the secret key is expanded from.
//! * `encseed`: The 32-byte randomness used to encapsulate to the corresponding public key.
//! * `pk`: The serialized public key derived from `keyseed`.
//! * `sk`: The _expanded_ secret key. This crate does not expose the expanded form, so this line
//!   is parsed for structure and then ignored.
//! * `ct`: The serialized ciphertext produced by encapsulating with `encseed`.
//! * `ss`: The shared secret corresponding to `ct`.
//!
//! Each line has the form `<label><SPACE><content>`, where `<content>` is hex-encoded bytes.

use std::{fs, path::Path};

use kopis::{kopis512, kopis768, kopis1024};

/// The labels of the 6 lines making up a test vector, in the order they appear in the file.
const LABELS: [&str; 6] = ["keyseed", "encseed", "pk", "sk", "ct", "ss"];

/// The pqm4 implementations that each parameter set has vectors for. Both must produce identical
/// answers.
const IMPLS: [&str; 2] = ["speed", "stack"];

/// A single pqm4 known-answer test vector. The expanded `sk` line is not represented here, since
/// this crate only ever handles the 32-byte seed form of a secret key.
#[derive(Debug)]
struct Pqm4Vector {
    /// The line number (1-indexed) the vector starts on. Used for error messages.
    line_num: usize,
    /// The 32-byte seed the secret key is expanded from.
    keyseed: [u8; 32],
    /// The 32-byte randomness used to encapsulate.
    encseed: [u8; 32],
    /// The serialized public key derived from `keyseed`.
    pk: Vec<u8>,
    /// The serialized ciphertext produced by encapsulating with `encseed`.
    ct: Vec<u8>,
    /// The shared secret corresponding to `ct`.
    ss: Vec<u8>,
}

/// Splits a content line into its label and its decoded bytes. Panics if the line is malformed.
fn parse_line(line: &str, line_num: usize) -> (&str, Vec<u8>) {
    let (label, content) = line
        .split_once(' ')
        .unwrap_or_else(|| panic!("line {line_num}: expected `<label><SPACE><hex>`, got {line:?}"));
    let bytes = hex::decode(content)
        .unwrap_or_else(|e| panic!("line {line_num}: could not hex-decode {label}: {e}"));

    (label, bytes)
}

/// Converts a decoded field into a fixed-size array. Panics if the length is wrong.
fn to_array<const N: usize>(bytes: &[u8], label: &str, line_num: usize) -> [u8; N] {
    bytes.try_into().unwrap_or_else(|_| {
        panic!(
            "line {line_num}: {label} is {} bytes, expected {N}",
            bytes.len()
        )
    })
}

/// Reads every vector from `path`.
fn read_vectors(path: &Path) -> Vec<Pqm4Vector> {
    let contents = fs::read_to_string(path)
        .unwrap_or_else(|e| panic!("could not read test-vector file {}: {e}", path.display()));

    // Pair each line with its 1-indexed line number, then drop comments and blank lines.
    let lines: Vec<(usize, &str)> = contents
        .lines()
        .enumerate()
        .map(|(i, line)| (i + 1, line.trim_end()))
        .filter(|(_, line)| !line.is_empty() && !line.starts_with('#'))
        .collect();

    assert_eq!(
        lines.len() % LABELS.len(),
        0,
        "expected a multiple of {} content lines, got {}",
        LABELS.len(),
        lines.len()
    );

    lines
        .chunks_exact(LABELS.len())
        .map(|chunk| {
            let mut fields = Vec::with_capacity(LABELS.len());
            for (&expected_label, &(line_num, line)) in LABELS.iter().zip(chunk.iter()) {
                let (label, bytes) = parse_line(line, line_num);
                assert_eq!(
                    label, expected_label,
                    "line {line_num}: expected label {expected_label:?}, got {label:?}"
                );
                fields.push((line_num, bytes));
            }

            // Destructure in `LABELS` order. `sk` is the expanded secret key, which this crate
            // does not expose, so it is dropped.
            let [keyseed, encseed, pk, _sk, ct, ss]: [(usize, Vec<u8>); 6] =
                fields.try_into().unwrap();

            Pqm4Vector {
                line_num: keyseed.0,
                keyseed: to_array(&keyseed.1, "keyseed", keyseed.0),
                encseed: to_array(&encseed.1, "encseed", encseed.0),
                pk: pk.1,
                ct: ct.1,
                ss: ss.1,
            }
        })
        .collect()
}

/// Reads and verifies every vector file for a single Kopis level. This is a macro because each
/// level uses distinct key/ciphertext types.
macro_rules! pqm4_kat_test {
    (
        $test_name:ident,
        $level:expr,
        $sk_ty:ty,
        $pk_ty:ty,
        $ct_len:expr
    ) => {
        #[test]
        fn $test_name() {
            for impl_name in IMPLS {
                let path_str = format!("tests/pqm4_test_vectors-kopis{}-{impl_name}.txt", $level);
                let path = Path::new(&path_str);
                let vectors = read_vectors(path);
                assert!(!vectors.is_empty(), "{path_str}: no test vectors were read");

                for vector in &vectors {
                    let ctx = format!("{path_str}: vector starting on line {}", vector.line_num);

                    // Expand the secret key from its seed and check that the derived public key
                    // matches the recorded one.
                    let sk = <$sk_ty>::expand_from_seed(&vector.keyseed);
                    let mut pk_bytes = [0u8; <$pk_ty>::SERIALIZED_LEN];
                    sk.public_key().serialize(&mut pk_bytes);
                    assert_eq!(
                        pk_bytes.as_slice(),
                        vector.pk.as_slice(),
                        "{}: derived public key does not match recorded pk",
                        ctx
                    );

                    // Deserialize the recorded public key and re-run the deterministic
                    // encapsulation. The ciphertext and shared secret must match the recorded
                    // values.
                    let pk = <$pk_ty>::from_bytes(&pk_bytes);
                    let (ct, ss) = pk.encapsulate_deterministic(&vector.encseed);
                    assert_eq!(
                        ct.as_slice(),
                        vector.ct.as_slice(),
                        "{}: recomputed ct does not match recorded value",
                        ctx
                    );
                    assert_eq!(
                        ss.as_bytes().as_slice(),
                        vector.ss.as_slice(),
                        "{}: recomputed ss does not match recorded value",
                        ctx
                    );

                    // Decapsulating the recorded ciphertext must recover the recorded shared
                    // secret.
                    let recorded_ct = to_array::<{ $ct_len }>(&vector.ct, "ct", vector.line_num);
                    let decapped_ss = sk.decapsulate(&recorded_ct);
                    assert_eq!(
                        decapped_ss.as_bytes().as_slice(),
                        vector.ss.as_slice(),
                        "{}: decapsulated ss does not match recorded value",
                        ctx
                    );
                }
            }
        }
    };
}

pqm4_kat_test!(
    pqm4_kat_kopis512,
    512,
    kopis512::Kopis512SecretKey,
    kopis512::Kopis512PublicKey,
    kopis512::KOPIS512_CIPHERTEXT_LEN
);
pqm4_kat_test!(
    pqm4_kat_kopis768,
    768,
    kopis768::Kopis768SecretKey,
    kopis768::Kopis768PublicKey,
    kopis768::KOPIS768_CIPHERTEXT_LEN
);
pqm4_kat_test!(
    pqm4_kat_kopis1024,
    1024,
    kopis1024::Kopis1024SecretKey,
    kopis1024::Kopis1024PublicKey,
    kopis1024::KOPIS1024_CIPHERTEXT_LEN
);
