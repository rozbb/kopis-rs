use kopis::{
    kopis512::Kopis512SecretKey, kopis768::Kopis768SecretKey, kopis1024::Kopis1024SecretKey,
};

use criterion::{Criterion, criterion_group, criterion_main};

// Only the graviola benchmark needs batched iteration.
use criterion::BatchSize;

// Every benchmark below drives `bench_with_input` off a fixture built once, outside the timing
// loop. Criterion passes that fixture through `black_box` before it invokes the closure (see
// `routine.rs`), which is what stops the loop-invariant work here — key expansion, matrix setup,
// hashing of fixed inputs — from being folded out of the measurement. Wrapping the individual
// fields in `black_box` as well was measured to make no difference.
//
// Every one of them uses `iter_with_large_drop` rather than `iter`, and that is not a formatting
// preference. These routines return whole KEM keys — 16 KB for an unpacked kopis-768 secret key,
// 26 KB at kopis-1024 — and `iter` both moves that value out of the timing closure and drops it
// on the clock. The move is the expensive half: measured on an M1, `iter` reported 23.7 us for a
// kopis-768 key expansion that takes 11.6 us, and the overhead scales with the returned type, so
// it fell hardest on kopis (16 KB, `ZeroizeOnDrop`), mildly on graviola (7 KB, has a `Drop`) and
// not at all on aws-lc-rs, whose `DecapsulationKey` is a 16-byte handle over `EVP_PKEY`. Under
// `iter` the comparison was partly a comparison of return-type shapes.
//
// `iter_with_large_drop` collects the outputs and drops them after the clock stops, which removes
// both. It is not free either — it writes each iteration to a fresh slot in a ~1 MB batch instead
// of reusing one buffer, and at kopis-1024's 26 KB key that cache pressure cancels out the
// deferred drop — but it is the documented tool for the job and it is applied uniformly.

macro_rules! bench_kopis_variant {
    ($bench_name:ident, $privkey_name:ident) => {
        fn $bench_name(c: &mut Criterion) {
            let seed = [0u8; 32];
            let sk = $privkey_name::from_seed(&seed);
            let pk = sk.public_key().clone();
            let (ct, _) = pk.encapsulate_deterministic(&seed);

            let input = (seed, sk, pk, ct);
            let mut group = c.benchmark_group(stringify!($bench_name));

            group.bench_with_input("gen-keypair-derand", &input, |b, (seed, ..)| {
                b.iter_with_large_drop(|| $privkey_name::from_seed(seed))
            });

            group.bench_with_input("encap-derand", &input, |b, (seed, _, pk, _)| {
                b.iter_with_large_drop(|| pk.encapsulate_deterministic(seed))
            });

            group.bench_with_input("decap", &input, |b, (_, sk, _, ct)| {
                b.iter_with_large_drop(|| sk.decapsulate(ct))
            });

            group.finish();
        }
    };
}

macro_rules! bench_libcrux_variant {
    ($bench_name:ident, $backend:ident, $mod_name:path) => {
        fn $bench_name(c: &mut Criterion) {
            use $mod_name as base_mod;

            use base_mod::$backend::unpacked::*;

            let kg_randomness = [0u8; 64];
            let encap_randomness = [0u8; 32];

            let kp = generate_key_pair(kg_randomness);
            let (ct, _) = encapsulate(kp.public_key(), encap_randomness);

            let input = (kg_randomness, encap_randomness, kp, ct);
            let mut group = c.benchmark_group(stringify!($bench_name));

            group.bench_with_input("gen-keypair-derand", &input, |b, (kg_randomness, ..)| {
                b.iter_with_large_drop(|| generate_key_pair(*kg_randomness))
            });

            group.bench_with_input("encap-derand", &input, |b, (_, encap_randomness, kp, _)| {
                // Borrowing the unpacked public key out of the keypair is not part of encap.
                let pk = kp.public_key();
                b.iter_with_large_drop(|| encapsulate(pk, *encap_randomness))
            });

            group.bench_with_input("decap", &input, |b, (_, _, kp, ct)| {
                b.iter_with_large_drop(|| decapsulate(kp, ct))
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
                b.iter_with_large_drop(|| {
                    kem::DecapsulationKey::generate_deterministic(&kem::$level, &kg_randomness)
                        .unwrap()
                });
            });

            group.bench_with_input("encap-derand", &input, |b, (_, pk, _)| {
                b.iter_with_large_drop(|| pk.encapsulate_deterministic(&encap_randomness).unwrap());
            });

            group.bench_with_input("decap", &input, |b, (sk, _, ct)| {
                b.iter_with_large_drop(|| {
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

bench_libcrux_variant!(libcrux_serial_mlkem512, portable, libcrux_ml_kem::mlkem512);
bench_libcrux_variant!(libcrux_serial_mlkem768, portable, libcrux_ml_kem::mlkem768);
bench_libcrux_variant!(
    libcrux_serial_mlkem1024,
    portable,
    libcrux_ml_kem::mlkem1024
);

// libcrux exposes its AVX2 backend only on x86, so these are absent on AArch64 — where they would
// not merely be filtered out at run time but fail to compile.
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
bench_libcrux_variant!(libcrux_avx2_mlkem512, avx2, libcrux_ml_kem::mlkem512);
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
bench_libcrux_variant!(libcrux_avx2_mlkem768, avx2, libcrux_ml_kem::mlkem768);
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
bench_libcrux_variant!(libcrux_avx2_mlkem1024, avx2, libcrux_ml_kem::mlkem1024);

bench_awslc_variant!(awslc_mlkem512, ML_KEM_512);
bench_awslc_variant!(awslc_mlkem768, ML_KEM_768);
bench_awslc_variant!(awslc_mlkem1024, ML_KEM_1024);

// graviola has hand-written ML-KEM assembly for both x86_64 (AVX2) and AArch64 (NEON), behind one
// portable API, so this benchmark builds and runs on either.
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
        b.iter_with_large_drop(|| DecapKey::keygen_internal(kg_randomness))
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
        b.iter_with_large_drop(|| sk.decaps_internal(ct))
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
criterion_group!(
    libcrux_serial_benches,
    libcrux_serial_mlkem512,
    libcrux_serial_mlkem768,
    libcrux_serial_mlkem1024
);

criterion_group!(graviola_benches, graviola_mlkem768);
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
criterion_group!(
    libcrux_avx2_benches,
    libcrux_avx2_mlkem512,
    libcrux_avx2_mlkem768,
    libcrux_avx2_mlkem1024
);

#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
criterion_main!(
    kopis_benches,
    libcrux_serial_benches,
    libcrux_avx2_benches,
    graviola_benches,
    awslc_benches
);

#[cfg(not(any(target_arch = "x86", target_arch = "x86_64")))]
criterion_main!(
    kopis_benches,
    libcrux_serial_benches,
    graviola_benches,
    awslc_benches
);
