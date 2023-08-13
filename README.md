This is a helper library, written in Rust, for working with
FFI bindings to Futhark kernels compiled into dynamically linked
shared objects.

As this library is designed around the
[cacti](https://git.sr.ht:~ptrj/cacti)-flavored
[fork](https://git.sr.ht/~ptrj/futhark)
of [Futhark](https://github.com/diku-dk/futhark),
it contains some idiosyncratic interfaces and is not intended
for general usage with mainline Futhark.
However, if you are writing your own FFI bindings to Futhark,
you may still find some parts of this library useful.
