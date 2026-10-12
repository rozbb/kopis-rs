use kopis::{
    kopis512::Kopis512SecretKey, kopis768::Kopis768SecretKey, kopis1024::Kopis1024SecretKey,
};

use criterion::{Criterion, criterion_group, criterion_main};

// Only the graviola benchmark needs batched iteration.
use criterion::BatchSize;

// We use `iter_with_large_drop` so that we do not count zeroization time

macro_rules! bench_kopis_variant {
    ($bench_name:ident, $privkey_name:ident) => {
        fn $bench_name(c: &mut Criterion) {
            let seed = [0u8; 32];
            let sk = $privkey_name::from(&seed);
            let pk = sk.public_key().clone();
            let (ct, _) = pk.encapsulate_deterministic(&seed);

            let input = (seed, sk, pk, ct);
            let mut group = c.benchmark_group(stringify!($bench_name));

            group.bench_with_input("gen-keypair-derand", &input, |b, (seed, ..)| {
                b.iter_with_large_drop(|| $privkey_name::from(seed))
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

bench_kopis_variant!(kopis512, Kopis512SecretKey);
bench_kopis_variant!(kopis768, Kopis768SecretKey);
bench_kopis_variant!(kopis1024, Kopis1024SecretKey);

criterion_group!(kopis_benches, kopis512, kopis768, kopis1024);
criterion_main!(kopis_benches);
