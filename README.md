[![Crates.io](https://img.shields.io/crates/v/arrav.svg)](https://crates.io/crates/arrav)
[![Documentation](https://docs.rs/arrav/badge.svg)](https://docs.rs/arrav/)
[![Build Status](https://dev.azure.com/jonhoo/jonhoo/_apis/build/status/arrav?branchName=master)](https://dev.azure.com/jonhoo/jonhoo/_build/latest?definitionId=15&branchName=master)
[![Codecov](https://codecov.io/github/jonhoo/arrav/coverage.svg?branch=master)](https://codecov.io/gh/jonhoo/arrav)

A sentinel-based, heapless, `Vec`-like type.

Arrays are great, because they do not require allocation.
But arrays are fixed-size.

Slices are great, because you can make them smaller.
But slices aren't `Sized`.

Vectors are great, because you can make them bigger.
But vectors require allocation.

This type provides a type that acts like a vector but is represented
exactly like an array. Unlike other array-backed vector-like types, but
like C-style strings and arrays, `Arrav` uses a sentinel value to
indicate unoccupied elements. This makes `push` and `pop` a little
slower, but avoids having to store the length separately. The trade-off
is that the sentinel value can no longer be stored in the array.

`Arrav` is intended for when you have a _small_ but variable number of
_small_ values that you want to store compactly (e.g., because they're
going to be stored in a large number of elements). This is also why the
"search" for the sentinel value to determine the array's length (and
thus for `push` and `pop`) is unlikely to matter in practice.

Unlike C-style strings and arrays, which use `NULL` as the sentinel,
`Arrav` uses the _max_ value of the type (like `std::u8::MAX`). This
means that unless you are saturating the type's range, you won't even
notice the sentinel.

## License

Licensed under either of

 * Apache License, Version 2.0
   ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license
   ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

## Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be
dual licensed as above, without any additional terms or conditions.
