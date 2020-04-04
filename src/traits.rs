use crate::*;
use std::convert::TryFrom;
use std::ops::Index;
use std::{fmt, ops};

// === constructors ===

impl<T, const N: usize> Default for Arrav<T, N>
where
    T: Copy + Sentinel,
    [T; N]: std::array::LengthAtMost32,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<T, const N: usize> TryFrom<[T; N]> for Arrav<T, N>
where
    T: Copy + Sentinel,
    [T; N]: std::array::LengthAtMost32,
{
    type Error = ([T; N], self::errors::IsSentinel<T>);
    fn try_from(arr: [T; N]) -> Result<Self, Self::Error> {
        Self::from_array(arr)
    }
}

impl<T, const N: usize> std::iter::FromIterator<T> for Arrav<T, N>
where
    T: Copy + Sentinel,
    [T; N]: std::array::LengthAtMost32,
{
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = T>,
    {
        let mut v = Arrav::new();
        v.extend(iter);
        v
    }
}

impl<T, const N: usize> std::iter::Extend<T> for Arrav<T, N>
where
    T: Copy + Sentinel,
    [T; N]: std::array::LengthAtMost32,
{
    fn extend<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = T>,
    {
        let start = self.len();
        let iter = iter.into_iter();
        for (i, t) in iter.enumerate() {
            if i == self.capacity() {
                panic!("iterator does not fit in Arrav<_, {}>", N)
            } else if t == T::SENTINEL {
                panic!("iterator produced sentinel value")
            } else {
                self.ts[start + i] = t;
            }
        }
    }
}

// === printers ===

impl<T: fmt::Debug, const N: usize> fmt::Debug for Arrav<T, N>
where
    T: Copy + Sentinel,
    [T; N]: std::array::LengthAtMost32,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

// === derefs ===

impl<T, const N: usize> AsRef<[T]> for Arrav<T, N>
where
    T: Copy + Sentinel,
    [T; N]: std::array::LengthAtMost32,
{
    fn as_ref(&self) -> &[T] {
        let len = self.len();
        &self.ts[..len]
    }
}

impl<T, const N: usize> std::ops::Deref for Arrav<T, N>
where
    T: Copy + Sentinel,
    [T; N]: std::array::LengthAtMost32,
{
    type Target = [T];
    fn deref(&self) -> &Self::Target {
        let len = Self::len(self);
        &self.ts[..len]
    }
}

// NOTE: we cannot safely implement DerefMut or IndexMut, since the user might override
// the value with the sentinel, which would invalidate the data structure's integrity!

impl<T, const N1: usize, const N2: usize> PartialEq<Arrav<T, N2>> for Arrav<T, N1>
where
    T: PartialEq + Copy + Sentinel,
    [T; N1]: std::array::LengthAtMost32,
    [T; N2]: std::array::LengthAtMost32,
{
    fn eq(&self, rhs: &Arrav<T, N2>) -> bool {
        let mut rhs = rhs.iter();
        for t in self.iter() {
            match rhs.next() {
                Some(rhs) if rhs == t => {}
                _ => return false,
            }
        }
        rhs.next().is_none()
    }
}

impl<T, const N: usize> Eq for Arrav<T, N>
where
    T: Eq + Copy + Sentinel,
    [T; N]: std::array::LengthAtMost32,
{
}

impl<T, const N1: usize, const N2: usize> PartialOrd<Arrav<T, N2>> for Arrav<T, N1>
where
    T: PartialOrd + Copy + Sentinel,
    [T; N1]: std::array::LengthAtMost32,
    [T; N2]: std::array::LengthAtMost32,
{
    fn partial_cmp(&self, other: &Arrav<T, N2>) -> Option<std::cmp::Ordering> {
        self.iter().partial_cmp(other.iter())
    }
}

impl<T, const N: usize> Ord for Arrav<T, N>
where
    T: Ord + Copy + Sentinel,
    [T; N]: std::array::LengthAtMost32,
{
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.iter().cmp(other.iter())
    }
}

impl<T, const N: usize> PartialEq<[T]> for Arrav<T, N>
where
    T: Copy + Sentinel,
    [T; N]: std::array::LengthAtMost32,
{
    fn eq(&self, rhs: &[T]) -> bool {
        if rhs.len() > N {
            // can't possibly be ==
            return false;
        }

        let mut rhs = rhs.iter();
        for t in self.iter() {
            match rhs.next() {
                Some(rhs) if rhs == &t => {}
                _ => return false,
            }
        }
        rhs.next().is_none()
    }
}

impl<T, const N: usize, const AN: usize> PartialEq<[T; AN]> for Arrav<T, N>
where
    T: Copy + Sentinel,
    [T; N]: std::array::LengthAtMost32,
{
    fn eq(&self, rhs: &[T; AN]) -> bool {
        self == &rhs[..]
    }
}

// === accessors ===

impl<T, const N: usize> Index<usize> for Arrav<T, N>
where
    T: Copy + Sentinel,
    [T; N]: std::array::LengthAtMost32,
{
    type Output = T;
    fn index(&self, idx: usize) -> &Self::Output {
        self.get(idx)
            .unwrap_or_else(move || errors::index_len_fail(idx, self.len()))
    }
}

impl<T, const N: usize> Index<ops::Range<usize>> for Arrav<T, N>
where
    T: Copy + Sentinel,
    [T; N]: std::array::LengthAtMost32,
{
    type Output = [T];
    fn index(&self, idx: ops::Range<usize>) -> &Self::Output {
        if idx.start > idx.end {
            errors::index_order_fail(idx.start, idx.end)
        } else if idx.end > self.capacity()
            || (idx.end != 0 && *unsafe { self.get_unchecked(idx.end - 1) } == T::SENTINEL)
        {
            errors::index_len_fail(idx.end, self.len())
        }
        unsafe { self.get_unchecked_range(idx) }
    }
}
