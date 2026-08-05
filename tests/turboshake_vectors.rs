//! Generates `lean/turboshake_vectors.jsonl`: 100 CTurboSHAKE128/256 vectors for the Lean spec.

use std::fmt::Write as _;
use std::fs;

use turboshake::digest::{ExtendableOutput, Update, XofReader};
use turboshake::{CTurboShake128, CTurboShake256};

const OUT: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/turboshake_vectors.jsonl");

/// Domain separators: the two Kopis uses, the RFC's, and both ends of the legal `01..=7f`.
const DOMAIN_SEPS: [u8; 5] = [0x01, 0x02, 0x03, 0x1f, 0x7f];

/// `(input length, output length)`, straddling both rates (168, 136) and the 8-byte word.
const CASES: [(usize, usize); 10] = [
    (0, 32),
    (1, 32),
    (17, 64),
    (135, 32),
    (136, 136),
    (137, 168),
    (167, 8),
    (168, 169),
    (169, 200),
    (1000, 512),
];

/// RFC 9861 `ptn(n)`: `00 01 .. F9 FA` repeated, truncated to `n`.
fn ptn(n: usize) -> Vec<u8> {
    (0..n).map(|i| (i % 251) as u8).collect()
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().fold(String::new(), |mut s, b| {
        let _ = write!(s, "{b:02x}");
        s
    })
}

fn xof128<const DS: u8>(msg: &[u8], out_len: usize) -> Vec<u8> {
    let mut h = CTurboShake128::<DS>::default();
    h.update(msg);
    let mut out = vec![0u8; out_len];
    h.finalize_xof().read(&mut out);
    out
}

fn xof256<const DS: u8>(msg: &[u8], out_len: usize) -> Vec<u8> {
    let mut h = CTurboShake256::<DS>::default();
    h.update(msg);
    let mut out = vec![0u8; out_len];
    h.finalize_xof().read(&mut out);
    out
}

fn row(jsonl: &mut String, variant: u16, ds: u8, msg: &[u8], digest: &[u8]) {
    let _ = writeln!(
        jsonl,
        r#"{{"description":"TurboSHAKE{variant}(ptn({}), D=0x{ds:02x}, {})","variant":{variant},"ds":{ds},"input":"{}","output":"{}"}}"#,
        msg.len(),
        digest.len(),
        hex(msg),
        hex(digest),
    );
}

/// `DS` is a const generic on `CTurboShake*`, so each separator needs its own instantiation.
fn emit<const DS: u8>(jsonl: &mut String) {
    for (in_len, out_len) in CASES {
        let msg = ptn(in_len);
        row(jsonl, 128, DS, &msg, &xof128::<DS>(&msg, out_len));
        row(jsonl, 256, DS, &msg, &xof256::<DS>(&msg, out_len));
    }
}

#[test]
fn generate() {
    let mut jsonl = String::new();
    emit::<{ DOMAIN_SEPS[0] }>(&mut jsonl);
    emit::<{ DOMAIN_SEPS[1] }>(&mut jsonl);
    emit::<{ DOMAIN_SEPS[2] }>(&mut jsonl);
    emit::<{ DOMAIN_SEPS[3] }>(&mut jsonl);
    emit::<{ DOMAIN_SEPS[4] }>(&mut jsonl);

    assert_eq!(jsonl.lines().count(), DOMAIN_SEPS.len() * CASES.len() * 2);
    fs::write(OUT, jsonl).unwrap();
}

/// The generator's oracle is the `turboshake` crate, so anchor that crate to the published
/// vectors — otherwise the Lean spec would only ever be checked against another implementation.
#[test]
fn matches_rfc9861() {
    let cases: [(String, &str); 4] = [
        (
            hex(&xof128::<0x1f>(&[], 32)),
            "1e415f1c5983aff2169217277d17bb538cd945a397ddec541f1ce41af2c1b74c",
        ),
        (
            hex(&xof128::<0x01>(&[0xff; 3], 32)),
            "bf323f940494e88ee1c540fe660be8a0c93f43d15ec006998462fa994eed5dab",
        ),
        (
            hex(&xof256::<0x1f>(&[], 64)),
            "367a329dafea871c7802ec67f905ae13c57695dc2c6663c61035f59a18f8e7db\
             11edc0e12e91ea60eb6b32df06dd7f002fbafabb6e13ec1cc20d995547600db0",
        ),
        (
            hex(&xof256::<0x1f>(&ptn(17), 64)),
            "b3bab0300e6a191fbe6137939835923578794ea54843f5011090fa2f3780a9e5\
             cb22c59d78b40a0fbff9e672c0fbe0970bd2c845091c6044d687054da5d8e9c7",
        ),
    ];
    for (i, (got, want)) in cases.iter().enumerate() {
        assert_eq!(got, want, "RFC 9861 vector {i}");
    }
}
