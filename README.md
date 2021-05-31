# Coq array library

[![CI](https://github.com/tchajed/coq-array/actions/workflows/coq-action.yml/badge.svg)](https://github.com/tchajed/coq-array/actions/workflows/coq-action.yml)

Theorems about using lists as arrays, supporting indexing, in-bounds updates, and subslicing.

I don't use this library any more so it doesn't see new features. I do aim to
keep it working with new versions of Coq. Currently CI tests Coq 8.10 up to
master and the library is simple enough that I don't anticipate needing to drop
support for old versions.

If you can use [stdpp](https://gitlab.mpi-sws.org/iris/stdpp) I would recommend
using that, since it is well engineered and well maintained. However stdpp only
has `take` and `drop` (for list prefix and suffix) so subslicing doesn't have
convenient lemmas.

## Including this library

Using [coq-project-template](https://github.com/tchajed/coq-project-template):

```
git submodule add https://github.com/tchajed/coq-array vendor/array
git submodule add https://github.com/tchajed/coq-classes vendor/classes
```
