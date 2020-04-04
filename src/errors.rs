use std::fmt;

/// The provided value was `T`'s [sentinel value](Sentinel).
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub struct IsSentinel<T>(pub T);

impl<T: fmt::Debug> std::error::Error for IsSentinel<T> {}
impl<T> fmt::Display for IsSentinel<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "value is the type's sentinel value, which cannot be represented"
        )
    }
}

/// The reason why a call to [`Arrav::try_push`] failed.
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub enum PushErrorKind {
    /// The `Arrav` was already at capacity.
    Full,
    /// The value provided to `try_push` was the pushed type's [sentinel value](Sentinel).
    IsSentinel,
}

/// An error that occurred on a call to [`Arrav::try_push`].
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub struct PushError<T> {
    /// The item provided to `try_push` that could not be pushed.
    pub item: T,
    /// The reason the item could not be pushed.
    pub kind: PushErrorKind,
}

impl<T: fmt::Debug> std::error::Error for PushError<T> {}
impl<T> fmt::Display for PushError<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.kind {
            PushErrorKind::Full => write!(f, "Arrav was full"),
            PushErrorKind::IsSentinel => write!(f, "pushed item had sentinel value"),
        }
    }
}

#[inline(never)]
#[cold]
pub(super) fn index_len_fail(index: usize, len: usize) -> ! {
    panic!("index {} out of range for Arrav of length {}", index, len);
}

#[inline(never)]
#[cold]
pub(super) fn index_order_fail(index: usize, end: usize) -> ! {
    panic!("Arrav index starts at {} but ends at {}", index, end);
}
