use crate::*;

/// Immutable `Arrav` iterator
///
/// This struct is created using [`Arrav::iter`].
#[derive(Debug, Copy, Clone)]
pub struct ArravIter<T, const N: usize>
where
    T: Copy + Sentinel,
    [T; N]: std::array::LengthAtMost32,
{
    v: Arrav<T, N>,
    at: usize,
}

impl<T, const N: usize> IntoIterator for Arrav<T, N>
where
    T: Copy + Sentinel,
    [T; N]: std::array::LengthAtMost32,
{
    type IntoIter = ArravIter<T, N>;
    type Item = T;
    fn into_iter(self) -> Self::IntoIter {
        ArravIter::new(self)
    }
}

impl<T, const N: usize> ArravIter<T, N>
where
    T: Copy + Sentinel,
    [T; N]: std::array::LengthAtMost32,
{
    pub(crate) const fn new(v: Arrav<T, N>) -> Self {
        Self { v, at: 0 }
    }
}

impl<T, const N: usize> Iterator for ArravIter<T, N>
where
    T: Copy + Sentinel,
    [T; N]: std::array::LengthAtMost32,
{
    type Item = T;
    fn next(&mut self) -> Option<Self::Item> {
        let t = *self.v.get(self.at)?;
        self.at += 1;
        Some(t)
    }
}

impl<'a, T, const N: usize> IntoIterator for &'a Arrav<T, N>
where
    T: Copy + Sentinel,
    [T; N]: std::array::LengthAtMost32,
{
    type IntoIter = ArravIter<T, N>;
    type Item = T;
    fn into_iter(self) -> Self::IntoIter {
        Arrav::into_iter(*self)
    }
}
