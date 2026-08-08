use kopis::{
    SharedSecret,
    kopis768::{
        KOPIS768_CIPHERTEXT_LEN, KOPIS768_PUBKEY_LEN, Kopis768Ciphertext, Kopis768PublicKey,
        Kopis768SecretKey,
    },
    subtle::ConstantTimeEq,
};

fn main() {
    let mut rng = rand::rng();

    // Alice generates a keypair
    let sk = Kopis768SecretKey::generate_from_rng(&mut rng);
    let pk = sk.public_key();

    // Alice serializes the secret key, and saves to disk
    let sk_seed = sk.seed();

    // Alice serializes her pubkey and sends to bob
    let _pk_bytes = pk.to_bytes();
    let pk_bytes = _pk_bytes.as_slice();

    // Bob receives the public key and deserializes
    // The API only accepts fixed-len slices, so we have to cast it first
    let pk_arr: &[u8; KOPIS768_PUBKEY_LEN] = pk_bytes.try_into().unwrap();
    let pk = Kopis768PublicKey::from_bytes(pk_arr);

    // Bob encapsulates to Alice and gets a shared secret ss1
    let (_ct, ss1): (Kopis768Ciphertext, SharedSecret) = pk.encapsulate_with_rng(&mut rng);
    let ct = _ct.as_slice();

    // Alice receives the ciphertext. She reconstructs her decap key from her saved seed
    let sk = Kopis768SecretKey::from_seed(sk_seed);
    let ct_arr: &[u8; KOPIS768_CIPHERTEXT_LEN] = ct.try_into().unwrap();
    let ss2 = sk.decapsulate(ct_arr);

    // Check the shared secrets are equal
    assert!(bool::from(ss1.ct_eq(&ss2)));

    println!("KEM ran successfully");
}
