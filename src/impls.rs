//! This file implements the external-facing API of our KEM

use crate::{
    consts::*,
    kem::{KemPublicKey, KemSecretKey, SharedSecret},
    pke::ciphertext_len,
};

use rand_core::CryptoRng;
use zeroize::Zeroize;

/// Defines convenience types and impls for a given Kopis variant
macro_rules! variant_impl {
    (
        $variant_name:ident,
        $mod_doc:expr,
        $pubkey_name:ident,
        $privkey_name:ident,
        $ciphertext_name:ident,
        $ciphertext_len_name:ident,
        $pubkey_len_name:ident,
        $variant_ell:expr,
        $variant_mu:expr,
        $variant_modt_bits:expr
    ) => {
        #[doc = $mod_doc]
        pub mod $variant_name {
            use super::*;

            /// A secret key for this KEM
            pub type $privkey_name = KemSecretKey<$variant_ell>;

            /// A public key for this KEM
            pub type $pubkey_name = KemPublicKey<$variant_ell>;

            /// The length of a ciphertext, or "encapsulated key", for this KEM
            pub const $ciphertext_len_name: usize =
                ciphertext_len::<$variant_ell, $variant_modt_bits>();

            /// The length of a public key, or "encapsulation key", for this KEM
            pub const $pubkey_len_name: usize = KemPublicKey::<$variant_ell>::SERIALIZED_LEN;

            /// A ciphertext, or "encapsulated key", for this KEM. This is just a bytestring with
            /// length `
            #[doc = stringify!($ciphertext_len_name)]
            /// `.
            pub type $ciphertext_name = [u8; $ciphertext_len_name];

            impl $privkey_name {
                /// Generate a fresh secret key
                pub fn generate_from_rng(rng: &mut impl CryptoRng) -> Self {
                    KemSecretKey::generate_inner::<$variant_mu>(rng)
                }

                /// Deserializes a secret key from a 32-byte seed
                pub fn from_seed(bytes: &[u8; 32]) -> Self {
                    KemSecretKey::expand_from_seed::<$variant_mu>(bytes)
                }

                /// Returns the public key corresponding to this secret key
                pub fn public_key(&self) -> &$pubkey_name {
                    &self.kem_pk
                }
            }

            impl $pubkey_name {
                /// Serializes this public key to bytes
                pub fn to_bytes(&self) -> [u8; Self::SERIALIZED_LEN] {
                    let mut buf = [0u8; Self::SERIALIZED_LEN];
                    self.serialize(&mut buf);
                    buf
                }
            }

            impl $pubkey_name {
                pub fn from_bytes(bytes: &[u8; $pubkey_len_name]) -> Self {
                    Self::from_bytes_inner(bytes)
                }

                /// Encapsulates a fresh shared secret
                pub fn encapsulate_with_rng(
                    &self,
                    rng: &mut impl CryptoRng,
                ) -> ($ciphertext_name, SharedSecret) {
                    let mut randomness = [0u8; 32];
                    rng.fill_bytes(&mut randomness);
                    let out = self.encapsulate_deterministic(&randomness);

                    randomness.zeroize();
                    out
                }

                /// Encapsulates a shared secret using the given 32-byte `randomness`. This is
                /// deterministic given `randomness`, and is primarily useful for testing and
                /// known-answer test (KAT) vectors.
                pub fn encapsulate_deterministic(
                    &self,
                    randomness: &[u8; 32],
                ) -> ($ciphertext_name, SharedSecret) {
                    let mut ct = [0u8; $ciphertext_len_name];
                    let ss = crate::kem::encap_deterministic::<
                        $variant_ell,
                        $variant_mu,
                        $variant_modt_bits,
                    >(randomness, &self, &mut ct);

                    (ct, ss)
                }
            }

            impl $privkey_name {
                /// Decapsulates an encapsulated key and returns the resulting shared secret. If
                /// the encapsulated key is invalid, then the shared secret will be pseudorandom
                /// garbage.
                pub fn decapsulate(&self, encapsulated_key: &$ciphertext_name) -> SharedSecret {
                    crate::kem::decap::<$variant_ell, $variant_mu, $variant_modt_bits>(
                        &self,
                        encapsulated_key,
                    )
                }
            }

            /// Basic test that keygen, encap, decap, ser, and deser work
            #[test]
            fn test_api() {
                use subtle::ConstantTimeEq;

                let mut rng = rand::rng();
                let sk = $privkey_name::generate_from_rng(&mut rng);
                let pk = sk.public_key();

                // Serialize and deserialize the keys
                let sk_seed = sk.seed();
                let sk = $privkey_name::from_seed(&sk_seed);

                let pk_bytes = pk.to_bytes();
                let pk = $pubkey_name::from_bytes(&pk_bytes);

                let (ct, ss1) = pk.encapsulate_with_rng(&mut rng);
                let ct_bytes = ct.as_ref();

                let ct_arr = ct_bytes.try_into().unwrap();
                let ss2 = sk.decapsulate(&ct_arr);

                assert!(bool::from(ss1.ct_eq(&ss2)));
            }
        }
    };
}

variant_impl!(
    kopis512,
    "Kopis-512 is designed to have security close to that of AES-128",
    Kopis512PublicKey,
    Kopis512SecretKey,
    Kopis512Ciphertext,
    KOPIS512_CIPHERTEXT_LEN,
    KOPIS512_PUBKEY_LEN,
    KOPIS512_L,
    KOPIS512_MU,
    KOPIS512_T
);

variant_impl!(
    kopis768,
    "Kopis-768 is designed to have security close to that of AES-192",
    Kopis768PublicKey,
    Kopis768SecretKey,
    Kopis768Ciphertext,
    KOPIS768_CIPHERTEXT_LEN,
    KOPIS768_PUBKEY_LEN,
    KOPIS768_L,
    KOPIS768_MU,
    KOPIS768_T
);

variant_impl!(
    kopis1024,
    "Kopis-1024 is designed to have security close to that of AES-256",
    Kopis1024PublicKey,
    Kopis1024SecretKey,
    Kopis1024Ciphertext,
    KOPIS1024_CIPHERTEXT_LEN,
    KOPIS1024_PUBKEY_LEN,
    KOPIS1024_L,
    KOPIS1024_MU,
    KOPIS1024_T
);
