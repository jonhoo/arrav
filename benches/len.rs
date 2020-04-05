use arrav::Arrav;
use criterion::{black_box, criterion_main, BenchmarkId, Criterion};

macro_rules! bench_len {
    ($c:ident, $t:ty, $width:expr) => {{
        let mut group = $c.benchmark_group(concat!(stringify!($t), "x", stringify!($width)));
        let lens = if $width == 4 {
            &[0, 1, 2, 3, 4][..]
        } else {
            assert!($width > 4);
            assert!($width % 4 == 0);
            &[
                0,
                1,
                $width / 4,
                $width / 2,
                3 * $width / 4,
                $width - 1,
                $width,
            ][..]
        };
        for len in lens {
            group.bench_with_input(BenchmarkId::from_parameter(len), len, |b, &len| {
                let mut av = Arrav::<$t, $width>::repeat(black_box(5)).unwrap();
                while av.len() != len {
                    av.pop().unwrap();
                }
                b.iter(|| av.len());
            });
        }
        group.finish();
    }};
}

pub fn len() {
    use std::time::Duration;
    let mut c = Criterion::default()
        .configure_from_args()
        .warm_up_time(Duration::from_secs(1))
        .sample_size(20)
        .measurement_time(Duration::from_secs(1));
    bench_len!(c, u8, 32);
    bench_len!(c, u8, 24);
    bench_len!(c, u8, 16);
    bench_len!(c, u8, 8);
    bench_len!(c, u8, 4);
    bench_len!(c, u16, 16);
    bench_len!(c, u16, 8);
    bench_len!(c, u16, 4);
    bench_len!(c, u32, 8);
    bench_len!(c, u32, 4);
}

criterion_main!(len);
