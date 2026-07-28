//! This module runs known-answer tests (KATs) using the test vectors distributed with the pqm4
//! implementation of Kopis.
//!
//! Vectors are read from `pqm4_test_vectors.txt`. Every line that starts with `#` is a comment and
//! is skipped, as are blank lines. The remaining lines come in groups of 6, one group per test
//! vector, with the labels appearing in this fixed order:
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
//!
//! The vector file holds Kopis-768 vectors.

use std::{fs, path::Path};

use kopis::kopis768::{
    KOPIS768_CIPHERTEXT_LEN, Kopis768Ciphertext, Kopis768PublicKey, Kopis768SecretKey,
};

/// The labels of the 6 lines making up a test vector, in the order they appear in the file.
const LABELS: [&str; 6] = ["keyseed", "encseed", "pk", "sk", "ct", "ss"];

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

fn test_file(filename: &str) {
    let path = Path::new(filename);
    let vectors = read_vectors(path);
    assert!(!vectors.is_empty(), "no test vectors were read");

    for vector in &vectors {
        let ctx = || format!("vector starting on line {}", vector.line_num);

        // Expand the secret key from its seed and check that the derived public key matches the
        // recorded one.
        let sk = Kopis768SecretKey::expand_from_seed(&vector.keyseed);
        let mut pk_bytes = [0u8; Kopis768PublicKey::SERIALIZED_LEN];
        sk.public_key().serialize(&mut pk_bytes);
        assert_eq!(
            pk_bytes.as_slice(),
            vector.pk.as_slice(),
            "{}: derived public key does not match recorded pk",
            ctx()
        );

        // Deserialize the recorded public key and re-run the deterministic encapsulation. The
        // ciphertext and shared secret must match the recorded values.
        let pk = Kopis768PublicKey::from_bytes(&pk_bytes);
        let (ct, ss) = pk.encapsulate_deterministic(&vector.encseed);
        assert_eq!(
            ct.as_slice(),
            vector.ct.as_slice(),
            "{}: recomputed ct does not match recorded value",
            ctx()
        );
        assert_eq!(
            ss.as_bytes().as_slice(),
            vector.ss.as_slice(),
            "{}: recomputed ss does not match recorded value",
            ctx()
        );

        // Decapsulating the recorded ciphertext must recover the recorded shared secret.
        let recorded_ct: Kopis768Ciphertext =
            to_array::<KOPIS768_CIPHERTEXT_LEN>(&vector.ct, "ct", vector.line_num);
        let decapped_ss = sk.decapsulate(&recorded_ct);
        assert_eq!(
            decapped_ss.as_bytes().as_slice(),
            vector.ss.as_slice(),
            "{}: decapsulated ss does not match recorded value",
            ctx()
        );
    }
}

#[test]
fn pqm4_kats() {
    let filenames = [
        "pqm4_test_vectors-kopis768-speed.txt",
        "pqm4_test_vectors-kopis768-stack.txt",
    ];

    for filename in filenames {
        test_file(&format!("tests/{filename}"));
    }
}
