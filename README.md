# Coq array library

[![CI](https://github.com/tchajed/coq-array/actions/workflows/coq-action.yml/badge.svg)](https://github.com/tchajed/coq-array/actions/workflows/coq-action.yml)

Theorems about using lists as arrays, supporting indexing, in-bounds updates, and subslicing.

I don't use this library any more so it doesn't see new features. It should work on Rocq 9.0+.

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
