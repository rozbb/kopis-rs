//! This file implements the IND-CPA-secure Kopis PKE scheme

use crate::{
    arithmetic::{Matrix, NttMatrix, RingElem},
    consts::{DOMSEP_KGEXPAND, DOMSEP_PKHASH, MAX_L, MAX_T, RING_DEG},
    sample::{gen_matrix_from_seed, gen_secret_from_seed},
    ser::deserialize_generic,
};

use turboshake::CTurboShake256;
use turboshake::digest::{ExtendableOutput, Update, XofReader};
use zeroize::{Zeroize, ZeroizeOnDrop};

const H1_VAL: u16 = 1 << (13 - 10 - 1);

/// The serialized length of one public-vector ring element: an element of `R10`, packed
/// at `10` bits per coefficient, i.e. 320 bytes.
const PK_VEC_ELEM_BYTES: usize = 10 * RING_DEG / 8;

/// A secret key for the Kopis PKE scheme (expanded form, NTT domain).
#[derive(Zeroize, ZeroizeOnDrop)]
pub(crate) struct PkeSecretKey<const L: usize>(NttMatrix<L, 1>);

/// A public key for the Kopis PKE scheme
#[derive(Clone)]
pub struct PkePublicKey<const L: usize> {
    /// The seed used to generate `mat_a` and thus `mat_a_ntt`
    matrix_seed: [u8; 32],
    /// The expanded public matrix `mat_a`, in NTT form. Precomputed here so that repeated encryptions
    /// (e.g. every encapsulation and every FO re-encryption during decapsulation) don't have to
    /// re-run the XOF that derives it from `matrix_seed`, nor re-transform it.
    mat_a_ntt: NttMatrix<L, L>,
    /// The public vector in NTT form, precomputed for the inner product in every encryption.
    vec_ntt: NttMatrix<L, 1>,
    /// The serialized public vector. Stored here so that `vec_ntt` doesn't have to be
    /// repeatedly converted on `Self::serialize`
    vec_bytes: [[u8; PK_VEC_ELEM_BYTES]; L],
}

impl<const L: usize> PkePublicKey<L> {
    pub const SERIALIZED_LEN: usize = 32 + L * 10 * RING_DEG / 8;

    /// Serializes this public key to a byte string. `out_buf` MUST have length
    /// `Self::SERIALIZED_LEN`
    // Explicit index loop (not `.iter().enumerate()`) to stay friendly to the aeneas extractor.
    #[allow(clippy::needless_range_loop)]
    pub(crate) fn serialize(&self, out_buf: &mut [u8]) {
        assert_eq!(out_buf.len(), Self::SERIALIZED_LEN);

        // The stored bytes are already the serialization: the L packed vector chunks, then the
        // seed. Copy each chunk into place, then the seed as the 32-byte tail.
        for i in 0..L {
            let start = i * PK_VEC_ELEM_BYTES;
            out_buf[start..start + PK_VEC_ELEM_BYTES].copy_from_slice(&self.vec_bytes[i]);
        }
        out_buf[L * PK_VEC_ELEM_BYTES..].copy_from_slice(&self.matrix_seed);
    }

    // `needless_range_loop`: explicit index loop kept for aeneas-extraction friendliness.
    #[allow(clippy::unwrap_used, clippy::needless_range_loop)]
    pub(crate) fn from_bytes(bytes: &[u8]) -> Self {
        assert_eq!(bytes.len(), Self::SERIALIZED_LEN);

        let (vec_slice, seed) = bytes.split_at(Self::SERIALIZED_LEN - 32);
        let matrix_seed: [u8; 32] = seed.try_into().unwrap(); // checked above

        // Deserialize the vector transiently, only to build its NTT form; the structured vector
        // itself is not kept.
        let vec = Matrix::deserialize_10(vec_slice);
        let vec_ntt = NttMatrix::from_uniform_matrix(&vec);

        // Store the vector's packed bytes verbatim (10-bit packing is canonical, so this is
        // exactly what `serialize` would re-emit).
        let mut vec_bytes = [[0u8; PK_VEC_ELEM_BYTES]; L];
        for i in 0..L {
            let start = i * PK_VEC_ELEM_BYTES;
            vec_bytes[i].copy_from_slice(&vec_slice[start..start + PK_VEC_ELEM_BYTES]);
        }

        let mat_a = gen_matrix_from_seed::<L>(&matrix_seed);
        let mat_a_ntt = NttMatrix::from_uniform_matrix(&mat_a);
        Self {
            matrix_seed,
            mat_a_ntt,
            vec_bytes,
            vec_ntt,
        }
    }

    /// Returns the public key hash
    ///
    // `needless_range_loop`: explicit index loop kept for aeneas-extraction friendliness, as in
    // `serialize` above. The parts cannot be passed to `turboshake256_hash` instead, because
    // there are `L + 1` of them and a `&[&[u8]]` is a nested borrow, which aeneas rejects.
    #[allow(clippy::needless_range_loop)]
    pub(crate) fn hash(&self) -> [u8; 32] {
        // pkh = TurboSHAKE256(pk, 32, DOMSEP_PKHASH)
        let mut hasher = CTurboShake256::<DOMSEP_PKHASH>::default();
        for i in 0..L {
            hasher.update(&self.vec_bytes[i]);
        }
        hasher.update(&self.matrix_seed);

        let mut out = [0u8; 32];
        let mut reader = hasher.finalize_xof();
        reader.read(&mut out);
        out
    }
}

/// The maximum length of a ciphertext (PKE or KEM, since they're the same), for all parameter
/// choices, for a message that is 32-bytes.
pub const fn max_ciphertext_len() -> usize {
    // b' is in R10^ℓ and c is in R_T
    MAX_L * 10 * RING_DEG / 8 + MAX_T * RING_DEG / 8
}

/// The length of a ciphertext (PKE or KEM, since they're the same) for a given parameter choice,
/// for a message that is 32-bytes
pub const fn ciphertext_len<const L: usize, const T: usize>() -> usize {
    // b' is in R10^ℓ and c is in R_T
    L * 10 * RING_DEG / 8 + T * RING_DEG / 8
}

/// Expands a 32-byte secret key into the full decapsulation key components.
///
/// Returns (vec_s, z, pk, pkh) where:
/// - `vec_s` is the secret vector
/// - `z` is 32 bytes used for rejection in decapsulation
/// - `pk` is the public key
/// - `pkh` is the hash of the public key
// `needless_range_loop`: explicit index loop kept for aeneas-extraction friendliness.
#[allow(clippy::needless_range_loop)]
pub(crate) fn expand_decap_key<const L: usize, const MU: usize>(
    sk: &[u8; 32],
) -> (PkeSecretKey<L>, [u8; 32], PkePublicKey<L>, [u8; 32]) {
    // mat_seed || secret_seed || r = TurboSHAKE256(sk || ℓ, 96, DOMSEP_KGEXPAND)
    let mut mat_seed = [0u8; 32];
    let mut secret_seed = [0u8; 32];
    let mut z = [0u8; 32];

    let mut xof = {
        let mut hasher = CTurboShake256::<DOMSEP_KGEXPAND>::default();
        hasher.update(sk);
        hasher.update(&[L as u8]);
        hasher.finalize_xof()
    };
    xof.read(&mut mat_seed);
    xof.read(&mut secret_seed);
    xof.read(&mut z);

    let mat_a = gen_matrix_from_seed::<L>(&mat_seed);
    let vec_s = gen_secret_from_seed::<L, MU>(&secret_seed);
    let mat_a_ntt = NttMatrix::from_uniform_matrix(&mat_a);
    let vec_s_ntt = NttMatrix::from_secret_matrix(&vec_s);

    // vec_b = CompressToR10(transpose(mat_A) * vec_s)
    let b = {
        let mut prod = mat_a_ntt.mul_transpose(&vec_s_ntt);
        prod.wrapping_add_to_all(H1_VAL);
        prod.shift_right(13 - 10);
        prod
    };

    // b was shifted by 3, so each coeff is < 2^13, as required by from_uniform_matrix
    let vec_ntt = NttMatrix::from_uniform_matrix(&b);

    // Pack b into its serialized bytes; we keep those, not the structured vector.
    let mut vec_bytes = [[0u8; PK_VEC_ELEM_BYTES]; L];
    for i in 0..L {
        b.0[i][0].serialize(&mut vec_bytes[i], 10);
    }

    let pk = PkePublicKey {
        matrix_seed: mat_seed,
        mat_a_ntt,
        vec_bytes,
        vec_ntt,
    };
    let pkh = pk.hash();

    (PkeSecretKey(vec_s_ntt), z, pk, pkh)
}

/// Decrypts a ciphertext using the given secret key. `ciphertext` MUST have length
/// `ciphertext_len::<L, T>()`.
pub(crate) fn decrypt<const L: usize, const T: usize>(
    sk: &PkeSecretKey<L>,
    ciphertext: &[u8],
) -> [u8; 32] {
    assert_eq!(ciphertext.len(), ciphertext_len::<L, T>());
    // b' is in R^l_P and c is in R_T
    let (bprime_bytes, c_bytes) = ciphertext.split_at(L * 10 * RING_DEG / 8);

    let bprime: Matrix<L, 1> = Matrix::deserialize_10(bprime_bytes);
    let bprime_ntt = NttMatrix::from_uniform_matrix(&bprime);

    let mut c = RingElem::deserialize(c_bytes, T);
    c.shift_left(10 - T);

    let v = bprime_ntt.mul_transpose(&sk.0);
    let v = v.0[0][0];

    // Compute v - c + h₂
    let mut mprime = &v - &c;
    let h2_val = (1 << (10 - 2)) - (1 << (10 - T - 1)) + (1 << (13 - 10 - 1));
    mprime.wrapping_add_to_all(h2_val);
    mprime.shift_right(10 - 1);

    let mut m = [0u8; 32];
    mprime.serialize(&mut m, 1);
    m
}

/// Encrypts a message with a given public key and randomness. `out_buf` MUST have length
/// `ciphertext_len::<L, T>()`.
pub(crate) fn encrypt_deterministic<const L: usize, const MU: usize, const T: usize>(
    pk: &PkePublicKey<L>,
    msg: &[u8; 32],
    randomness: &[u8; 32],
    out_buf: &mut [u8],
) {
    assert_eq!(out_buf.len(), ciphertext_len::<L, T>());

    let vec_sprime = gen_secret_from_seed::<L, MU>(randomness);
    let sprime_ntt = NttMatrix::from_secret_matrix(&vec_sprime);

    let bprime = {
        let mut prod = pk.mat_a_ntt.mul(&sprime_ntt);
        prod.wrapping_add_to_all(H1_VAL);
        prod.shift_right(13 - 10);
        prod
    };

    let vprime: Matrix<1, 1> = pk.vec_ntt.mul_transpose(&sprime_ntt);
    let vprime = vprime.0[0][0];

    let mut msg_polyn = RingElem(deserialize_generic(msg, 1));
    msg_polyn.shift_left(10 - 1);

    // Compute v' - mp + h₁
    let mut c = &vprime - &msg_polyn;
    c.wrapping_add_to_all(H1_VAL);
    c.shift_right(10 - T);

    // b' is in R^l_P and c is in R_T
    let (bprime_buf, c_buf) = out_buf.split_at_mut(L * 10 * RING_DEG / 8);
    bprime.serialize(bprime_buf, 10);
    c.serialize(c_buf, T);
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::consts::*;

    use rand::RngCore;

    // Tests that Decrypt(Encrypt(m)) == m
    #[test]
    fn encryption_correctness() {
        test_enc_dec::<KOPIS512_L, KOPIS512_T, KOPIS512_MU>();
        test_enc_dec::<KOPIS768_L, KOPIS768_T, KOPIS768_MU>();
        test_enc_dec::<KOPIS1024_L, KOPIS1024_T, KOPIS1024_MU>();
    }

    // Helper function that encrypts and decrypts a random 32-byte message
    fn test_enc_dec<const L: usize, const T: usize, const MU: usize>() {
        let mut rng = rand::rng();
        let mut backing_buf = [0u8; max_ciphertext_len()];

        for _ in 0..100 {
            // Generate a random secret key seed and expand it
            let mut sk_seed = [0u8; 32];
            rng.fill_bytes(&mut sk_seed);
            let (sk, _, pk, _) = expand_decap_key::<L, MU>(&sk_seed);

            // Encrypt a random message
            let mut enc_seed = [0u8; 32];
            let mut msg = [0u8; 32];
            rng.fill_bytes(&mut enc_seed);
            rng.fill_bytes(&mut msg);
            let ct_buf = &mut backing_buf[..T * RING_DEG / 8 + L * 10 * RING_DEG / 8];
            encrypt_deterministic::<L, MU, T>(&pk, &msg, &enc_seed, ct_buf);

            // Decrypt and check equality
            let recovered_msg = decrypt::<L, T>(&sk, ct_buf);
            assert_eq!(msg, recovered_msg);
        }
    }
}
