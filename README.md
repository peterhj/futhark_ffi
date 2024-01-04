# futhark_ffi

This is a helper library, written in Rust, for working with
FFI bindings to Futhark kernels compiled into dynamically linked
shared objects.

As this library is designed around the
[cacti](https://git.sr.ht/~ptrj/cacti)-flavored
[patchset](https://git.sr.ht/~ptrj/futhark) for
[Futhark](https://github.com/diku-dk/futhark),
it contains some idiosyncratic interfaces and is not intended
for general usage with upstream Futhark.
However, if you are writing your own FFI bindings to Futhark,
you may still find some parts of this library useful.

Related projects:
- [genfut](https://github.com/Erk-/genfut)
- [futhark-bindgen](https://github.com/zshipko/futhark-bindgen)
- [cargo-futhark](https://github.com/luleyleo/cargo-futhark)

## ABI and calling convention

When calling Futhark kernels whose types are not known at
host program compile time,
one minor sticking point is that there is no immediately
obvious facility for extracting the sizes of the Futhark array
handles (i.e. `struct memblock` and `struct memblock_dev`).
(Array shapes are stored inline following the memblock header;
in Rust, this would be called a dynamically-sized type.)

The Futhark compilation process does produce a neat JSON
manifest containing the expected dimensions of the array
arguments and outputs of kernels.
We do use this manifest for cross-checking.
However, sometimes it is also useful to be able to quickly
get the array dimensionality of a memblock and inspect the
inline shape,
without having to retrieve the manifest.

To that end, `futhark_ffi` provides some helper trait methods
for setting and masking pointer tag bits on pointers to
memblocks.
We avail ourselves of the empirical fact that the Futhark RTS
always `malloc`s memblocks,
so on typical 64-bit platforms we can use the least significant
3 bits of the memblock pointer to tag the array dimensionality,
equal to the length of the inline shape.

When using memblock pointer tag bits as above, the user of
`futhark_ffi` should respect the following calling convention:

1.  `_unset_ndim` on all memblock arguments
2.  `enter_kernel`
3.  `_set_ndim` on memblock arguments and fresh outputs
