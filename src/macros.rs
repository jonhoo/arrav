/// Creates a [`Arrav`] containing the arguments.
///
/// `avec!` allows `Arrav`s to be defined with the same syntax as array expressions.
/// There are two forms of this macro:
///
/// - Create a [`Arrav`] containing a given list of elements:
///
/// ```
/// let v = arrav::avec![1, 2, 3];
/// assert_eq!(v[0], 1);
/// assert_eq!(v[1], 2);
/// assert_eq!(v[2], 3);
/// ```
///
/// - Create a [`Arrav`] from a given element and size:
///
/// ```
/// let v = arrav::avec![1; 3];
/// assert_eq!(&*v, &[1, 1, 1]);
/// ```
///
/// [`Vec`]: ../std/vec/struct.Vec.html
#[macro_export]
macro_rules! avec {
    ($elem:expr; $n:expr) => {{
        #[allow(unused_imports)]
        use ::core::convert::TryFrom;
        $crate::Arrav::<_, $n>::repeat($elem).expect("cannot insert sentinel into Arrav")
    }};
    ($($x:expr),*) => {{
        #[allow(unused_imports)]
        use ::core::convert::TryFrom;
        let v = [
            $({
                // TODO: match on sentinel value directly when supported
                match $x {
                    x if x == $crate::Sentinel::SENTINEL => panic!("cannot insert sentinel into Arrav"),
                    x => x
                }
            }),*
        ];
        unsafe { $crate::Arrav::<_, { $crate::avec![@count_tts ($($x),*)] }>::from_array_unchecked(v) }
    }};
    ($($x:expr,)*) => ($crate::avec![$($x),*]);

    // macros for counting:
    // https://danielkeep.github.io/tlborm/book/blk-counting.html#slice-length
    // these can't be moved into the macro case below because of
    // https://github.com/rust-lang/rust/issues/35853
    (@replace_expr ($_t:expr, $sub:expr)) => {$sub};
    (@count_tts ($($e:expr),*)) => {<[()]>::len(&[$($crate::avec!(@replace_expr ($e, ()))),*])};
}

/// Produce an [`Arrav`] type that fits in a given container type.
///
/// Using `ArravOf!`, you can easily write out an `Arrav` type that can contain as many of one type
/// as fit in the size of a different type. This is better explain with examples:
///
/// ```
/// #![feature(const_panic, const_if_match)]
/// use arrav::{Arrav, ArravOf};
/// use std::mem::{size_of, size_of_val};
///
/// let v: ArravOf! {u64 as u8} = Arrav::new();
/// assert_eq!(size_of_val(&v), size_of::<u64>());
/// assert_eq!(v.capacity(), 64 / 8);
///
/// let v: ArravOf! {usize as u8} = Arrav::new();
/// assert_eq!(size_of_val(&v), size_of::<usize>());
/// assert_eq!(v.capacity(), size_of_val(&0usize) /* bytes */ * 8 / 8);
/// ```
///
/// - Create a [`Arrav`] from a given element and size:
///
/// ```
/// let v = arrav::avec![1; 3];
/// assert_eq!(&*v, &[1, 1, 1]);
/// ```
///
/// [`Vec`]: ../std/vec/struct.Vec.html
#[macro_export]
macro_rules! ArravOf {
    ($container:ty as $t:ty) => {
        $crate::Arrav<$t, {
            assert!(::core::mem::size_of::<$container>() >= ::core::mem::size_of::<$t>());
            ::core::mem::size_of::<$container>() / ::core::mem::size_of::<$t>()
        }>
    }
}

#[cfg(test)]
use crate::*;

// test the macros in-crate so we get nice, expanded errors

#[test]
fn let_tiny_vec() {
    let v = <ArravOf! {u32 as u8}>::new();
    assert_eq!(v.len(), 0);
    assert_eq!(v.capacity(), 4);
    assert!(v.is_empty());
}

#[test]
fn arrayof_size() {
    use std::mem::size_of;

    assert!(size_of::<ArravOf! {u8 as u8}>() <= size_of::<u8>());
    assert!(size_of::<ArravOf! {u16 as u8}>() <= size_of::<u16>());
    assert!(size_of::<ArravOf! {u32 as u8}>() <= size_of::<u32>());
    assert!(size_of::<ArravOf! {u64 as u8}>() <= size_of::<u64>());
    assert!(size_of::<ArravOf! {u128 as u8}>() <= size_of::<u128>());
    assert!(size_of::<ArravOf! {usize as u8}>() <= size_of::<usize>());

    assert!(size_of::<ArravOf! {u16 as u16}>() <= size_of::<u16>());
    assert!(size_of::<ArravOf! {u32 as u16}>() <= size_of::<u32>());
    assert!(size_of::<ArravOf! {u64 as u16}>() <= size_of::<u64>());
    assert!(size_of::<ArravOf! {u128 as u16}>() <= size_of::<u128>());
    assert!(size_of::<ArravOf! {usize as u16}>() <= size_of::<usize>());

    assert!(size_of::<ArravOf! {u32 as u32}>() <= size_of::<u32>());
    assert!(size_of::<ArravOf! {u64 as u32}>() <= size_of::<u64>());
    assert!(size_of::<ArravOf! {u128 as u32}>() <= size_of::<u128>());
    if size_of::<usize>() >= size_of::<u64>() {
        assert!(size_of::<ArravOf! {usize as u32}>() <= size_of::<usize>());
    }

    assert!(size_of::<ArravOf! {u64 as u64}>() <= size_of::<u64>());
    assert!(size_of::<ArravOf! {u128 as u64}>() <= size_of::<u128>());
    if size_of::<usize>() >= size_of::<u64>() {
        assert!(size_of::<ArravOf! {usize as u64}>() <= size_of::<usize>());
    }

    assert!(size_of::<ArravOf! {u128 as u128}>() <= size_of::<u128>());
}

#[test]
fn avec_elem() {
    let v0 = avec![0; 0];
    assert_eq!(v0.len(), 0);
    assert!(v0.is_empty());

    let v1 = avec![0; 1];
    assert_eq!(v1.len(), 1);
    assert!(!v1.is_empty());

    let v2 = avec![0; 2];
    assert_eq!(v2.len(), 2);
    assert!(!v2.is_empty());
}

#[test]
#[should_panic]
fn avec_elem_fail() {
    let _ = avec![std::u8::MAX; 1];
}

#[test]
fn avec_enum() {
    // NOTE: can't be Arrav<u8, _> b/c of https://github.com/rust-lang/rust/issues/70754
    let v0: Arrav<u8, 0> = avec![];
    assert_eq!(v0.len(), 0);
    assert!(v0.is_empty());

    let v1 = avec![0];
    assert_eq!(v1.len(), 1);
    assert_eq!(v1[0], 0);
    assert!(!v1.is_empty());

    let v2 = avec![0, 1];
    assert_eq!(v2.len(), 2);
    assert_eq!(v2[0], 0);
    assert_eq!(v2[1], 1);
    assert!(!v2.is_empty());
}

#[test]
#[should_panic]
fn avec_enum_fail() {
    let _ = avec![std::u8::MAX];
}

/// ```compile_fail
/// #![feature(const_if_match, const_panic)]
/// // fail to compile if T does not fit in container type
/// let _ = std::mem::size_of::<arrav::ArravOf! {u8 as u16}>();
/// ```
#[allow(dead_code)]
struct NotOk;
