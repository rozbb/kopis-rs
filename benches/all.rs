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

macro_rules! bench_awslc_variant {
    ($bench_name:ident, $level:ident) => {
        fn $bench_name(c: &mut Criterion) {
            use aws_lc_rs::kem;

            let kg_randomness = [0u8; 64];
            let encap_randomness = [0u8; 32];

            let sk = kem::DecapsulationKey::generate(&kem::$level).unwrap();
            let pk = sk.encapsulation_key().unwrap();
            let (ct, _) = pk.encapsulate().unwrap();

            let input = (sk, pk, ct);
            let mut group = c.benchmark_group(stringify!($bench_name));

            group.bench_function("keygen-derand", |b| {
                b.iter(|| {
                    kem::DecapsulationKey::generate_deterministic(&kem::$level, &kg_randomness)
                        .unwrap()
                });
            });

            group.bench_with_input("encap-derand", &input, |b, (_, pk, _)| {
                b.iter(|| pk.encapsulate_deterministic(&encap_randomness).unwrap());
            });

            group.bench_with_input("decap", &input, |b, (sk, _, ct)| {
                b.iter(|| {
                    let ct_shallow_copy = kem::Ciphertext::from(ct.as_ref());
                    sk.decapsulate(ct_shallow_copy)
                });
            });
        }
    };
}

bench_kopis_variant!(kopis512, Kopis512SecretKey);
bench_kopis_variant!(kopis768, Kopis768SecretKey);
bench_kopis_variant!(kopis1024, Kopis1024SecretKey);

bench_libcrux_variant!(libcrux_mlkem512, libcrux_ml_kem::mlkem512);
bench_libcrux_variant!(libcrux_mlkem768, libcrux_ml_kem::mlkem768);
bench_libcrux_variant!(libcrux_mlkem1024, libcrux_ml_kem::mlkem1024);

bench_awslc_variant!(awslc_mlkem512, ML_KEM_512);
bench_awslc_variant!(awslc_mlkem768, ML_KEM_768);
bench_awslc_variant!(awslc_mlkem1024, ML_KEM_1024);

fn graviola_mlkem768(c: &mut Criterion) {
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

criterion_group!(kopis_benches, kopis512, kopis768, kopis1024);
criterion_group!(
    awslc_benches,
    awslc_mlkem512,
    awslc_mlkem768,
    awslc_mlkem1024
);
criterion_group!(graviola_benches, graviola_mlkem768);
criterion_group!(
    libcrux_benches,
    libcrux_mlkem512,
    libcrux_mlkem768,
    libcrux_mlkem1024
);

criterion_main!(
    kopis_benches,
    libcrux_benches,
    graviola_benches,
    awslc_benches
);
