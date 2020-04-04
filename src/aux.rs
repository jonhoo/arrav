use crate::*;

macro_rules! impl_sentinel_by_max {
    ($t:tt) => {
        impl Sentinel for $t {
            const SENTINEL: Self = std::$t::MAX;
        }
    };
}

impl_sentinel_by_max!(u8);
impl_sentinel_by_max!(i8);
impl_sentinel_by_max!(u16);
impl_sentinel_by_max!(i16);
impl_sentinel_by_max!(u32);
impl_sentinel_by_max!(i32);
impl_sentinel_by_max!(u64);
impl_sentinel_by_max!(i64);
impl_sentinel_by_max!(u128);
impl_sentinel_by_max!(i128);
impl_sentinel_by_max!(usize);
impl_sentinel_by_max!(isize);
