use arrav::Arrav;
use criterion::{black_box, criterion_group, criterion_main, Criterion};

macro_rules! bench_len {
    ($c:ident, $t:ty, $width:expr) => {
        $c.bench_function(
            concat!("len ", stringify!($t), "x", stringify!($width)),
            |b| b.iter(|| Arrav::<$t, $width>::repeat(black_box(5)).unwrap().len()),
        );
    };
}

pub fn criterion_benchmark(c: &mut Criterion) {
    bench_len!(c, u8, 32);
    bench_len!(c, u8, 16);
    bench_len!(c, u8, 8);
    bench_len!(c, u16, 16);
    bench_len!(c, u16, 8);
    bench_len!(c, u32, 8);
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
