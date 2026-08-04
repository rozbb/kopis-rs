use kopis::{
    kopis512::Kopis512SecretKey, kopis768::Kopis768SecretKey, kopis1024::Kopis1024SecretKey,
};

use criterion::{BatchSize, Criterion, criterion_group, criterion_main};

// Every benchmark below drives `bench_with_input` off a fixture built once, outside the timing
// loop. Criterion passes that fixture through `black_box` before it invokes the closure (see
// `routine.rs`), which is what stops the loop-invariant work here — key expansion, matrix setup,
// hashing of fixed inputs — from being folded out of the measurement. Wrapping the individual
// fields in `black_box` as well was measured to make no difference.

macro_rules! bench_kopis_variant {
    ($bench_name:ident, $privkey_name:ident) => {
        fn $bench_name(c: &mut Criterion) {
            let seed = [0u8; 32];
            let sk = $privkey_name::expand_from_seed(&seed);
            let pk = sk.public_key();
            let (ct, _) = pk.encapsulate_deterministic(&seed);

            let input = (seed, sk, pk, ct);
            let mut group = c.benchmark_group(stringify!($bench_name));

            group.bench_with_input("gen-keypair-derand", &input, |b, (seed, ..)| {
                b.iter(|| $privkey_name::expand_from_seed(seed))
            });

            group.bench_with_input("encap-derand", &input, |b, (seed, _, pk, _)| {
                b.iter(|| pk.encapsulate_deterministic(seed))
            });

            group.bench_with_input("decap", &input, |b, (_, sk, _, ct)| {
                b.iter(|| sk.decapsulate(ct))
            });

            group.finish();
        }
    };
}

macro_rules! bench_libcrux_variant {
    ($bench_name:ident, $mod_name:path) => {
        fn $bench_name(c: &mut Criterion) {
            use $mod_name as base_mod;

            use base_mod::portable::unpacked::*;

            let kg_randomness = [0u8; 64];
            let encap_randomness = [0u8; 32];

            let kp = generate_key_pair(kg_randomness);
            let (ct, _) = encapsulate(kp.public_key(), encap_randomness);

            let input = (kg_randomness, encap_randomness, kp, ct);
            let mut group = c.benchmark_group(stringify!($bench_name));

            group.bench_with_input("gen-keypair-derand", &input, |b, (kg_randomness, ..)| {
                b.iter(|| generate_key_pair(*kg_randomness))
            });

            group.bench_with_input("encap-derand", &input, |b, (_, encap_randomness, kp, _)| {
                // Borrowing the unpacked public key out of the keypair is not part of encap.
                let pk = kp.public_key();
                b.iter(|| encapsulate(pk, *encap_randomness))
            });

            group.bench_with_input("decap", &input, |b, (_, _, kp, ct)| {
                b.iter(|| decapsulate(kp, ct))
            });

            group.finish();
        }
    };
}

bench_libcrux_variant!(libcruxmlkem512, libcrux_ml_kem::mlkem512);
bench_libcrux_variant!(libcruxmlkem768, libcrux_ml_kem::mlkem768);
bench_libcrux_variant!(libcruxmlkem1024, libcrux_ml_kem::mlkem1024);

bench_kopis_variant!(kopis512, Kopis512SecretKey);
bench_kopis_variant!(kopis768, Kopis768SecretKey);
bench_kopis_variant!(kopis1024, Kopis1024SecretKey);

fn graviolamlkem768(c: &mut Criterion) {
    use graviola::key_agreement::mlkem768::*;

    let kg_randomness = [0u8; 64];
    let encap_randomness = [0u8; 32];

    // Derandomized throughout, to match the other two implementations' fixtures.
    let sk = DecapKey::keygen_internal(&kg_randomness);
    let pk = sk.encapsulation_key();
    let (_, ct) = pk.clone().encaps_internal(Message(encap_randomness));

    let input = (kg_randomness, encap_randomness, sk, pk, ct);
    let mut group = c.benchmark_group("graviolamlkem768");

    group.bench_with_input("gen-keypair-derand", &input, |b, (kg_randomness, ..)| {
        b.iter(|| DecapKey::keygen_internal(kg_randomness))
    });

    // `encaps_internal` consumes the `EncapKey`, so each iteration needs a fresh one. That clone
    // copies ~5.8 KB of unpacked key material, which is setup rather than encapsulation work, so
    // `iter_batched` keeps it out of the measurement.
    group.bench_with_input(
        "encap-derand",
        &input,
        |b, (_, encap_randomness, _, pk, _)| {
            b.iter_batched(
                || pk.clone(),
                |pk| pk.encaps_internal(Message(*encap_randomness)),
                BatchSize::SmallInput,
            )
        },
    );

    group.bench_with_input("decap", &input, |b, (_, _, sk, _, ct)| {
        b.iter(|| sk.decaps_internal(ct))
    });

    group.finish();
}

fn bench_aws_lc(c: &mut Criterion) {
    use aws_lc_rs::kem;

    let kg_randomness = [0u8; 64];
    let encap_randomness = [0u8; 32];

    let sk = kem::DecapsulationKey::generate(&kem::ML_KEM_768).unwrap();
    let pk = sk.encapsulation_key().unwrap();
    let (ct, _) = pk.encapsulate().unwrap();

    let input = (sk, pk, ct);
    let mut group = c.benchmark_group("aws-lc");

    group.bench_function("aws-lc-rs-mlkem768/keygen-rand", |b| {
        b.iter(|| {
            kem::DecapsulationKey::generate_deterministic(&kem::ML_KEM_768, &kg_randomness).unwrap()
        });
    });

    group.bench_with_input("aws-lc-rs-mlkem768/encap-rand", &input, |b, (_, pk, _)| {
        b.iter(|| pk.encapsulate_deterministic(&encap_randomness).unwrap());
    });

    group.bench_with_input("aws-lc-rs-mlkem768/decap", &input, |b, (sk, _, ct)| {
        b.iter(|| {
            let ct_shallow_copy = kem::Ciphertext::from(ct.as_ref());
            sk.decapsulate(ct_shallow_copy)
        });
    });
}

criterion_group!(kopis_benches, kopis512, kopis768, kopis1024);
criterion_group!(aws_lc_benches, bench_aws_lc);
criterion_group!(graviola_benches, graviolamlkem768);
criterion_group!(
    libcrux_benches,
    libcruxmlkem512,
    libcruxmlkem768,
    libcruxmlkem1024
);

criterion_main!(
    kopis_benches,
    libcrux_benches,
    graviola_benches,
    aws_lc_benches
);
