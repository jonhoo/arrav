//! A sentinel-based, heapless, `Vec`-like type.
//!
//! Arrays are great, because they do not require allocation.
//! But arrays are fixed-size.
//!
//! Slices are great, because you can make them smaller.
//! But slices aren't `Sized`.
//!
//! Vectors are great, because you can make them bigger.
//! But vectors require allocation.
//!
//! This type provides a type that acts like a vector but is represented exactly like an array.
//! Unlike other array-backed vector-like types, but like C-style strings and arrays, `Arrav` uses
//! a sentinel value (dictated by [`Sentinel`]) to indicate unoccupied elements. This makes `push`
//! and `pop` a little slower, but avoids having to store the length separately. The trade-off is
//! that the sentinel value can no longer be stored in the array.
//!
//! `Arrav` is intended for when you have a _small_ but variable number of _small_ values that you
//! want to store compactly (e.g., because they're going to be stored in a large number of
//! elements). This is also why the "search" for the sentinel value to determine the array's length
//! (and thus for `push` and `pop`) is unlikely to matter in practice.
//!
//! Unlike C-style strings and arrays, which use `NULL` as the sentinel, `Arrav` uses the _max_
//! value of the type (like `std::u8::MAX`). This means that unless you are saturating the type's
//! range, you won't even notice the sentinel.
//!
//! # Semi-Important Tidbits
//!
//! **This crate uses the highly experimental const generics feature, and requires nightly.**
//!
//! The crate supports `no_std` environments without `alloc`. Just turn off the `std` feature.
//!
//! Wondering why the name? Arrav looks like the word "Array", but with "a bit chopped off" 🤷
//!
//! # Examples
//!
//! ```
//! use arrav::Arrav;
//! let mut av = Arrav::<_, 4>::new();
//! assert_eq!(av.capacity(), 4);
//! assert!(av.is_empty());
//!
//! av.try_push(1).unwrap();
//! av.try_push(2).unwrap();
//! av.try_push(std::i32::MAX).unwrap_err();
//!
//! assert_eq!(av.len(), 2);
//! assert_eq!(av[0], 1);
//!
//! assert_eq!(av.pop(), Some(2));
//! assert_eq!(av.len(), 1);
//!
//! av.set(0, 7).unwrap();
//! assert_eq!(av[0], 7);
//!
//! av.extend([1, 2, 3].iter().copied());
//!
//! for x in &av {
//!     println!("{}", x);
//! }
//! assert_eq!(av, [7, 1, 2, 3]);
//!
//! assert_eq!(av.len(), av.capacity());
//! av.try_push(3).unwrap_err();
//! ```
//!
//! The [`avec!`] macro is provided to make initialization more convenient:
//!
//! ```
//! use arrav::avec;
//! let av = avec![1, 2, 3];
//! assert_eq!(av.capacity(), 3);
//! assert_eq!(av, [1, 2, 3]);
//! ```
//!
//! It can also initialize each element of a `Arrav<T>` with a given value.
//! This may be more efficient than performing allocation and initialization
//! in separate steps, especially when initializing a vector of zeros:
//!
//! ```
//! use arrav::{Arrav, avec};
//! let av = arrav::avec![0; 5];
//! assert_eq!(av, [0, 0, 0, 0, 0]);
//!
//! // The following is equivalent, but potentially slower:
//! let mut av1: Arrav<_, 5> = Arrav::new();
//! av1.resize(5, 0);
//! assert_eq!(av, av1);
//! ```

#![feature(
    const_generics,
    const_generic_impls_guard,
    const_fn,
    const_if_match,
    const_panic,
    slice_index_methods,
    min_specialization
)]
#![allow(incomplete_features)]
#![deny(missing_docs, unreachable_pub)]
#![warn(rust_2018_idioms, intra_doc_link_resolution_failure)]
#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(feature = "std", deny(missing_debug_implementations))]

/// `Arrav` error types.
pub mod errors;
/// `Arrav` iterator types.
pub mod iter;
mod macros;
mod traits;

use core::ops;

/// A `Vec`-like type backed only by an array.
///
/// # Sentinels
///
/// `Arrav<T>` uses a [sentinel value](Sentinel) for each type `T` to indicate the end of the
/// array. For this reason, you can never insert a [`T::SENTINEL`](Sentinel::SENTINEL) into an
/// `Arrav<T>` — it would make the list be in an inconsistent state! All safe methods on `Arrav`
/// return an error if you attempt to insert the sentinel value for the array's type, or they panic
/// if no `Result` return type is provided.
///
/// # Representation
///
/// In memory, an `Arrav<T, N>` is represented exactly like a `[T; N]`.
///
/// # Indexing
///
/// The `Arrav` type allows to access values by index, because it implements the
/// [`Index`] trait. An example might help:
///
/// ```
/// let v = arrav::avec![0, 2, 4, 6];
/// println!("{}", v[1]); // will display '2'
/// ```
///
/// However be careful: if you try to access an index which isn't in the `Arrav`,
/// as your code will panic! You cannot do this:
///
/// ```should_panic
/// let v = arrav::avec![0, 2, 4, 6];
/// println!("{}", v[6]); // it will panic!
/// ```
///
/// Use [`get`] if you want to check whether the index is in the `Arrav`.
///
/// # Slicing
///
/// You can slice an `Arrav` just like you would an array.
/// To get a slice, use `&`. Example:
///
/// ```
/// fn read_slice(_: &[usize]) { /* .. */ }
///
/// let v = vec![0, 1];
/// read_slice(&v);
///
/// // ... and that's all!
/// // you can also do it like this:
/// let x : &[usize] = &v;
/// ```
///
/// You can also get a sub-slice using `&[Range]`:
///
/// ```
/// fn read_slice(_: &[usize]) { /* .. */ }
///
/// let v = vec![0, 1, 2];
/// read_slice(&v[1..2]);
/// ```
///
/// In Rust, it's more common to pass slices as arguments rather than vectors
/// when you just want to provide a read access.
///
/// # Mutability
///
/// Since an `Arrav<T>` cannot hold all legal values of `T` (specifically, not the sentinel value),
/// you cannot safely get mutable access to the elements of the arrav. Instead, you must use
/// [`set`], which returns an error if the sentinel value is inserted, or the unsafe [`get_mut`]
/// method.
#[derive(Copy, Clone, Hash)]
#[repr(transparent)]
pub struct Arrav<T: Copy, const N: usize>
where
    [T; N]: core::array::LengthAtMost32,
{
    ts: [T; N],
}

/// A type that has a sentinel value that can be used to indicate termination in [`Arrav`].
pub trait Sentinel: PartialEq {
    /// The sentinel value for a type used to indicate termination in [`Arrav`].
    const SENTINEL: Self;
}

// === constructors ===

impl<T, const N: usize> Arrav<T, N>
where
    T: Copy + Sentinel,
    [T; N]: core::array::LengthAtMost32,
{
    /// Constructs a new, empty `Arrav<T, N>`.
    ///
    /// You will generally want to specify the capacity of the `Arrav` when you construct it:
    ///
    /// ```
    /// # #![allow(unused_mut)]
    /// # use arrav::Arrav;
    /// let mut av: Arrav<i32, 4> = Arrav::new();
    /// ```
    ///
    /// You can often give `_` instead of the type (here `i32`), but this [will not work] for the
    /// capacity.
    ///
    ///   [will not work]: https://github.com/rust-lang/rust/issues/70754
    pub const fn new() -> Self {
        Arrav {
            ts: [T::SENTINEL; N],
        }
    }

    /// Constructs a new `Arrav<T, N>` and fills it with copies of `e`.
    ///
    /// You will generally want to specify the capacity of the `Arrav` when you construct it:
    ///
    /// ```
    /// # #![allow(unused_mut)]
    /// # use arrav::Arrav;
    /// let mut av: Arrav<_, 4> = Arrav::repeat(3).unwrap();
    /// ```
    // TODO: this can be const once we can match against associated consts
    pub fn repeat(e: T) -> Result<Self, errors::IsSentinel<T>>
    where
        T: Copy,
    {
        match e {
            e if e == T::SENTINEL => Err(errors::IsSentinel(e)),
            _ => Ok(Arrav { ts: [e; N] }),
        }
    }

    // TODO: one day this can be const, and then we make it pub
    pub(crate) fn from_array(arr: [T; N]) -> Result<Self, ([T; N], errors::IsSentinel<T>)> {
        for t in &arr {
            if t == &T::SENTINEL {
                return Err((arr, errors::IsSentinel(*t)));
            }
        }
        Ok(Self { ts: arr })
    }
}

impl<T, const N: usize> Arrav<T, N>
where
    T: Copy,
    [T; N]: core::array::LengthAtMost32,
{
    /// Constructs a new `Arrav<T, N>` directly from a backing array.
    ///
    /// This method does not check that `T::SENTINEL` only appears in a suffix of the array's
    /// elements. If it appears elsewhere, methods will do strange things.
    pub const unsafe fn from_array_unchecked(arr: [T; N]) -> Self {
        Self { ts: arr }
    }
}

// === meta ===

impl<T, const N: usize> Arrav<T, N>
where
    T: Copy,
    [T; N]: core::array::LengthAtMost32,
{
    /// Returns the number of elements the `Arrav` can hold without
    /// reallocating.
    ///
    /// # Examples
    ///
    /// ```
    /// # use arrav::Arrav;
    /// let av: Arrav<i32, 10> = Arrav::new();
    /// assert_eq!(av.capacity(), 10);
    /// ```
    pub const fn capacity(&self) -> usize {
        N
    }
}

impl<T, const N: usize> Arrav<T, N>
where
    T: Copy + Sentinel,
    [T; N]: core::array::LengthAtMost32,
{
    /// Returns the number of elements in the `Arrav`, also referred to
    /// as its 'length'.
    ///
    /// Since the `Arrav` does not store the number of non-sentinel elements, it must search the
    /// elements of the backing array for the first sentinel in order to compute the length. This
    /// should be very fast for small `N`, but may become a bottleneck at large `N`.
    ///
    /// # Examples
    ///
    /// ```
    /// let av = arrav::avec![1, 2, 3];
    /// assert_eq!(av.len(), 3);
    /// ```
    #[inline]
    pub fn len(&self) -> usize
    where
        Self: SpecializedLen,
    {
        self.fast_len()
    }

    /// Returns `true` if the `Arrav` contains no elements.
    ///
    /// # Examples
    ///
    /// ```
    /// # use arrav::Arrav;
    /// let mut v: Arrav<_, 4> = Arrav::new();
    /// assert!(v.is_empty());
    ///
    /// v.try_push(1).unwrap();
    /// assert!(!v.is_empty());
    /// ```
    // TODO: this can be const once we can match on SENTINEL
    pub fn is_empty(&self) -> bool {
        N == 0 || self.ts[0] == T::SENTINEL
    }

    /// Returns an iterator over the elements.
    ///
    /// # Examples
    ///
    /// ```
    /// # use arrav::avec;
    /// let x = avec![1, 2, 4];
    /// let mut iterator = x.iter();
    ///
    /// assert_eq!(iterator.next(), Some(1));
    /// assert_eq!(iterator.next(), Some(2));
    /// assert_eq!(iterator.next(), Some(4));
    /// assert_eq!(iterator.next(), None);
    /// ```
    pub const fn iter(&self) -> iter::ArravIter<T, N> {
        iter::ArravIter::new(*self)
    }
}

// === accessors ===

impl<T: Copy, const N: usize> Arrav<T, N>
where
    T: Copy + Sentinel,
    [T; N]: core::array::LengthAtMost32,
{
    /// Gets a reference to the element at position `index`.
    ///
    /// Returns `None` if `index` is greater than or equal to the arrav's [length](len).
    #[inline]
    // TODO: once we can match on SENTINEL, this can be const
    pub fn get(&self, index: usize) -> Option<&T> {
        if index >= self.capacity() {
            None
        } else {
            match unsafe { self.ts.get_unchecked(index) } {
                t if *t == T::SENTINEL => None,
                t => Some(t),
            }
        }
    }

    /// Gets a reference to the slice of elements whose indices fall in the given range.
    ///
    /// Returns `None` if the range does not fall within the bounds of the `Arrav`.
    #[inline]
    pub fn get_range(&self, index: ops::Range<usize>) -> Option<&[T]> {
        if index.start > index.end
            || index.end > self.capacity()
            || (index.end != 0 && *unsafe { self.get_unchecked(index.end - 1) } == T::SENTINEL)
        {
            None
        } else {
            unsafe { Some(self.get_unchecked_range(index)) }
        }
    }

    /// Sets the value at `index` to `value`.
    ///
    /// Returns an error if `value` is the [sentinel value](Sentinel).
    ///
    /// # Panics
    ///
    /// Panics if `index` is outside the bounds of the `Arrav`.
    #[inline]
    // TODO: once we can match on SENTINEL, this can be const
    pub fn set(&mut self, index: usize, value: T) -> Result<(), errors::IsSentinel<T>> {
        if value == T::SENTINEL {
            return Err(errors::IsSentinel(value));
        }

        if index >= self.capacity() {
            errors::index_len_fail(index, self.len());
        } else {
            match unsafe { self.ts.get_unchecked_mut(index) } {
                ot if *ot == T::SENTINEL => {
                    errors::index_len_fail(index, self.len());
                }
                ot => {
                    *ot = value;
                }
            }
        }

        Ok(())
    }
}

// === mutators ===

impl<T, const N: usize> Arrav<T, N>
where
    T: Copy + Sentinel,
    [T; N]: core::array::LengthAtMost32,
{
    /// Appends an element to the back of the `Arrav`.
    ///
    /// Returns `Err` if the provided value is `T`'s [sentinel value], or if the `Arrav` is already
    /// full.
    ///
    ///   [sentinel value](Sentinel)
    ///
    /// # Examples
    ///
    /// ```
    /// # use arrav::Arrav;
    /// let mut av: Arrav<i32, 3> = Arrav::new();
    /// av.try_push(1).unwrap();
    /// av.try_push(2).unwrap();
    /// assert_eq!(av, [1, 2]);
    ///
    /// // this fails since it is pushing the sentinel value
    /// av.try_push(std::i32::MAX).unwrap_err();
    ///
    /// // this fills the arrav to capacity
    /// av.try_push(3).unwrap();
    ///
    /// // this fails since the arrav is full
    /// av.try_push(4).unwrap_err();
    /// ```
    #[inline]
    pub fn try_push(&mut self, t: T) -> Result<(), errors::PushError<T>> {
        if t == T::SENTINEL {
            return Err(errors::PushError {
                kind: errors::PushErrorKind::IsSentinel,
                item: t,
            });
        }
        let i = self.len();
        if i == self.capacity() {
            Err(errors::PushError {
                kind: errors::PushErrorKind::Full,
                item: t,
            })
        } else {
            debug_assert!(self.ts[i] == T::SENTINEL);
            debug_assert!(i == 0 || self.ts[i - 1] != T::SENTINEL);
            self.ts[i] = t;
            Ok(())
        }
    }

    /// Removes the last element from the `Arrav` and returns it, or [`None`] if it
    /// is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// # use arrav::avec;
    /// let mut av = avec![1, 2, 3];
    /// assert_eq!(av.pop(), Some(3));
    /// assert_eq!(av, [1, 2]);
    /// assert_eq!(av.pop(), Some(2));
    /// assert_eq!(av.pop(), Some(1));
    /// assert_eq!(av.pop(), None);
    /// ```
    #[inline]
    pub fn pop(&mut self) -> Option<T> {
        let i = self.len();
        if i == 0 {
            None
        } else {
            let i = i - 1;
            debug_assert!(self.ts[i] != T::SENTINEL);
            debug_assert!(i == self.capacity() - 1 || self.ts[i + 1] == T::SENTINEL);
            Some(core::mem::replace(&mut self.ts[i], T::SENTINEL))
        }
    }

    /// Clears the `Arrav`, removing all values.
    ///
    /// Note that this method has no effect on the allocated capacity
    /// of the `Arrav`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use arrav::avec;
    /// let mut v = avec![1, 2, 3];
    ///
    /// v.clear();
    ///
    /// assert!(v.is_empty());
    /// ```
    pub fn clear(&mut self) {
        for i in 0..self.capacity() {
            match unsafe { self.get_unchecked_mut(i) } {
                t if t == &T::SENTINEL => break,
                t => *t = T::SENTINEL,
            }
        }
    }

    /// Increases the capacity of an `Arrav` by moving to a larger backing array.
    ///
    /// # Examples
    ///
    /// ```
    /// # use arrav::{Arrav, avec};
    /// let v = avec![1];
    /// assert_eq!(v.capacity(), 1);
    /// let v: Arrav<_, 3> = v.expand();
    /// assert_eq!(v.capacity(), 3);
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if `N2 < N`.
    ///
    /// ```should_panic
    /// # use arrav::{Arrav, avec};
    /// let v = avec![1, 2, 3];
    /// assert_eq!(v.capacity(), 3);
    /// let v: Arrav<_, 1> = v.expand();
    /// ```
    // TODO: one day, this can be const, and the should_panic above can be compile_fail
    #[inline]
    pub fn expand<const N2: usize>(self) -> Arrav<T, N2>
    where
        [T; N2]: core::array::LengthAtMost32,
    {
        assert!(
            N2 >= N,
            "cannot expand from {} into smaller array {}",
            N,
            N2
        );

        let mut new: Arrav<T, N2> = Arrav::new();
        // safety: N2 > N
        unsafe { core::intrinsics::copy_nonoverlapping(self.ts.as_ptr(), new.ts.as_mut_ptr(), N) };
        new
    }

    /// Resizes the `Arrav` in-place so that `len` is equal to `new_len`.
    ///
    /// If `new_len` is greater than `len`, the `Arrav` is extended by the
    /// difference, with each additional slot filled with `value`.
    /// If `new_len` is less than `len`, the `Arrav` is simply truncated.
    ///
    /// # Examples
    ///
    /// ```
    /// # use arrav::{Arrav, avec};
    /// let mut v: Arrav<_, 3> = avec![1].expand();
    /// v.resize(3, 2);
    /// assert_eq!(v, [1, 2, 2]);
    ///
    /// let mut v = avec![1, 2, 3, 4];
    /// v.resize(2, 0);
    /// assert_eq!(v, [1, 2]);
    /// ```
    pub fn resize(&mut self, new_len: usize, value: T) -> Result<(), errors::IsSentinel<T>> {
        assert!(
            new_len <= self.capacity(),
            "asked to resize beyond capacity"
        );
        if value == T::SENTINEL {
            return Err(errors::IsSentinel(value));
        }
        // set everything before new_len
        for i in 0..new_len {
            let t = unsafe { self.ts.get_unchecked_mut(i) };
            if *t == T::SENTINEL {
                *t = value;
            }
        }
        // clear everything beyond new_len
        for i in new_len..self.capacity() {
            let t = unsafe { self.ts.get_unchecked_mut(i) };
            if *t == T::SENTINEL {
                break;
            }
            *t = T::SENTINEL;
        }

        Ok(())
    }

    /// Creates an `Arrav` from an iterator.
    ///
    /// Returns `Err` if one of the values in the iterator is the sentinel value.
    ///
    /// # Panics
    ///
    /// Panics if the iterator yields more than `N` elements.
    ///
    /// # Examples
    ///
    /// ```
    /// # use arrav::{Arrav, avec};
    /// use std::iter::FromIterator;
    /// let five_fives = std::iter::repeat(5).take(5);
    /// let v: Arrav<_, 5> = Arrav::try_from_iter(five_fives).unwrap();
    /// assert_eq!(v, avec![5, 5, 5, 5, 5]);
    ///
    /// Arrav::<_, 1>::try_from_iter(std::iter::once(std::i32::MAX)).unwrap_err();
    /// ```
    pub fn try_from_iter<I>(iter: I) -> Result<Self, errors::IsSentinel<T>>
    where
        I: IntoIterator<Item = T>,
    {
        let mut v = Arrav::new();
        let iter = iter.into_iter();
        for (i, t) in iter.enumerate() {
            if i == v.capacity() {
                panic!("iterator does not fit in Arrav<_, {}>", N)
            } else if t == T::SENTINEL {
                return Err(errors::IsSentinel(t));
            } else {
                v.ts[i] = t;
            }
        }
        Ok(v)
    }

    /// Extends an `Arrav` with elements from an iterator.
    ///
    /// Returns `Err` if one of the values in the iterator is the sentinel value. The values
    /// yielded by the iterator _before_ the sentinel value are still pushed.
    ///
    /// # Panics
    ///
    /// Panics if the capacity of the `Arrav` is exceeded.
    ///
    /// # Examples
    ///
    /// ```
    /// # use arrav::{Arrav, avec};
    /// let mut v: Arrav<_, 5> = Arrav::new();
    /// v.try_push(1).unwrap();
    /// v.try_extend(vec![2, 3, 4]).unwrap();
    /// assert_eq!(v, avec![1, 2, 3, 4]);
    ///
    /// v.try_extend(vec![5, std::i32::MAX]).unwrap_err();
    /// assert_eq!(v, avec![1, 2, 3, 4, 5]);
    /// ```
    pub fn try_extend<I>(&mut self, iter: I) -> Result<(), errors::IsSentinel<T>>
    where
        I: IntoIterator<Item = T>,
    {
        let start = self.len();
        let iter = iter.into_iter();
        for (i, t) in iter.enumerate() {
            if i == self.capacity() {
                panic!("iterator does not fit in Arrav<_, {}>", N)
            } else if t == T::SENTINEL {
                return Err(errors::IsSentinel(t));
            } else {
                self.ts[start + i] = t;
            }
        }
        Ok(())
    }

    /// Removes an element from the `Arrav` and returns it.
    ///
    /// The removed element is replaced by the last element of the `Arrav`.
    ///
    /// This does not preserve ordering, but is O(1).
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// # use arrav::avec;
    /// let mut v = avec![1, 2, 3, 4];
    ///
    /// assert_eq!(v.swap_remove(1), 2);
    /// assert_eq!(v, [1, 4, 3]);
    ///
    /// assert_eq!(v.swap_remove(0), 1);
    /// assert_eq!(v, [3, 4]);
    /// ```
    pub fn swap_remove(&mut self, index: usize) -> T {
        let t = *self.get(index).unwrap_or_else(|| {
            errors::index_len_fail(index, self.len());
        });

        // find last element to swap with
        // starting at index because we know it exists
        let mut end = index;
        let mut lastt = &t;
        while end + 1 < self.capacity() {
            let t = unsafe { self.ts.get_unchecked(end + 1) };
            if t == &T::SENTINEL {
                break;
            }
            lastt = t;
            end += 1;
        }

        if end == index {
            // index is last element, so just remove it
            *unsafe { self.ts.get_unchecked_mut(index) } = T::SENTINEL;
        } else {
            // place @end at @index, then delete @end
            let lastt = *lastt;
            *unsafe { self.ts.get_unchecked_mut(index) } = lastt;
            *unsafe { self.ts.get_unchecked_mut(end) } = T::SENTINEL;
        }
        t
    }
}

// === unsafe accessors ===

impl<T: Copy, const N: usize> Arrav<T, N>
where
    T: Copy + Sentinel,
    [T; N]: core::array::LengthAtMost32,
{
    /// Gets a reference to the element at position `index`.
    ///
    /// # Safety
    ///
    /// This method does not perform any bounds checks or sentinel checks on the index.
    #[inline]
    pub unsafe fn get_unchecked(&self, index: usize) -> &T {
        self.ts.get_unchecked(index)
    }

    /// Gets a reference to the slice of elements whose indices fall in the given range.
    ///
    /// # Safety
    ///
    /// This method does not perform any bounds checks or sentinel checks on the index.
    #[inline]
    pub unsafe fn get_unchecked_range(&self, index: ops::Range<usize>) -> &[T] {
        self.ts.get_unchecked(index)
    }

    /// Gets an exclusive reference to the element at position `index`.
    ///
    /// This method _does_ perform bounds and sentinel checks.
    ///
    /// # Safety
    ///
    /// This method is unsafe, because you must ensure that you do not use the returned reference
    /// to overwrite the `T` with `T`'s sentinel value.
    #[inline]
    pub unsafe fn get_mut(&mut self, index: usize) -> Option<&mut T> {
        if index >= self.capacity() {
            None
        } else {
            match self.ts.get_unchecked_mut(index) {
                t if *t == T::SENTINEL => None,
                t => Some(t),
            }
        }
    }

    /// Gets an exclusive reference to the element at position `index`.
    ///
    /// # Safety
    ///
    /// This method does not perform bounds or sentinel checks.
    ///
    /// Like [`get_mut`], this method is also unsafe because you must ensure that you do not use
    /// the returned reference to overwrite the `T` with `T`'s sentinel value.
    #[inline]
    pub unsafe fn get_unchecked_mut(&mut self, index: usize) -> &mut T {
        self.ts.get_unchecked_mut(index)
    }
}

// === specializations ===

// The performance of `Arrav::len` is key to the performance of `Arrav`, so we want to provide
// optimized versions of it wherever we can. Even limited specialization lets us do that:
//
// TODO: SIMD would be _awesome_ here given that this is needed to call push, pop, and the various
// derefs to slices. I think that to do it we may need to extend `Sentinel` to also include a
// `const HINT: u8` associated constant, and then use that to quickly skip over parts of the `[T;
// N]` to find the first sentinel. we _may_ need specialization

#[doc(hidden)]
pub trait SpecializedLen {
    fn fast_len(&self) -> usize;
}

// Provide a fall-back that always applies
impl<T, const N: usize> SpecializedLen for Arrav<T, N>
where
    T: Copy + Sentinel,
    [T; N]: core::array::LengthAtMost32,
{
    #[inline]
    default fn fast_len(&self) -> usize {
        match N {
            0 => 0,
            1 => {
                if self.ts[0] == T::SENTINEL {
                    0
                } else {
                    1
                }
            }
            _ => self
                .ts
                .iter()
                .position(|v| *v == T::SENTINEL)
                .unwrap_or(self.capacity()),
        }
    }
}

macro_rules! specialize {
    ($t:ty, $width:expr, $stride:expr, $stype:ident, $test:ident) => {
        // $stype is just $t + "x" + $width
        #[cfg(feature = "simd")]
        impl SpecializedLen for Arrav<$t, $width> {
            #[inline]
            fn fast_len(&self) -> usize {
                let needle = packed_simd::$stype::splat(<$t>::SENTINEL);
                for start in (0..$width).step_by($stride) {
                    debug_assert!(start + $stride <= self.ts.len());
                    let haystack = unsafe { self.ts.get_unchecked(start..start + $stride) };
                    let search = packed_simd::$stype::from_slice_aligned(haystack);
                    let eq = search.eq(needle);
                    if eq.any() {
                        // found the sentinel!
                        let offset = if let Some(i) = haystack.iter().position(|&t| t == <$t>::SENTINEL) {
                            i
                        } else if cfg!(debug_assertions) {
                            unreachable!()
                        } else {
                            // safety: simd told us the sentinel was here
                            unsafe { core::hint::unreachable_unchecked() }
                        };
                        return start + offset;
                    }
                }
                // all the items are there
                $width
            }
        }

        #[cfg(all(test, feature = "simd"))]
        mod $test {
            use super::*;
            #[test]
            fn test_specialized_len() {
                let mut v: Arrav<$t, $width> = avec![1; $width];
                for removed in 0..$width {
                    assert_eq!(v.len(), $width - removed);
                    assert_eq!(v.pop(), Some(1));
                }
                assert_eq!(v.len(), 0);
                assert!(v.is_empty());
                assert_eq!(v.pop(), None);
            }
        }
    }
}

// NOTE: don't add a SIMD specialization just because it looks cool!
// here's what you do:
//
//  1. add a specialize!() call below for the [T, N] you have in mind.
//  2. add a benchmark to benches/len.rs -- the format should hopefully be obvious.
//  3. run `cargo bench len --no-default-features --features std` to benchmark the
//     non-simd version of calls to `len`.
//  4. run `cargo bench len` to benchmark the simd version.
//  5. look for the "len " benchmark for the specialization you added.
//  6. if the change seems significant, make a commit that contains the output from
//     step 4 for your new specialization in the commit message. please place the
//     criterion output in a fenced code block (```), check that you don't
//     accidentally have any tabs in there, and check that the output is correctly
//     aligned.
//  7. repeat if you want to add more specializations.

specialize!(u8, 32, 8, u8x8, u8_32);
specialize!(u8, 16, 4, u8x4, u8_16);
specialize!(u8, 8, 4, u8x4, u8_8);
specialize!(u16, 16, 4, u16x4, u16_16);
specialize!(u16, 8, 4, u16x4, u16_8);
specialize!(u32, 8, 4, u32x4, u32_8);

// copies of the above for signed types, assuming the same benchmark results hold
specialize!(i8, 32, 8, i8x8, i8_32);
specialize!(i8, 16, 4, i8x4, i8_16);
specialize!(i8, 8, 4, i8x4, i8_8);
specialize!(i16, 16, 4, i16x4, i16_16);
specialize!(i16, 8, 4, i16x4, i16_8);
specialize!(i32, 8, 4, i32x4, i32_8);

macro_rules! impl_sentinel_by_max {
    ($t:tt) => {
        impl Sentinel for $t {
            const SENTINEL: Self = ::core::$t::MAX;
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
