This package proves state recurrence for S071,
`1LB2RA3LA2RB_0RB3LB0LA1RA`, and hence `QHBound 0 s71_tm`.

The finite certificate uses two-cell blocks. `CheckerSound.v` proves that the
Boolean checks imply every closure clause required by `FARForward.v`.
`BlockMicro.v` and `LocalTable.v` verify the finite block computations on concrete
tapes. `MacroBridge.v` and `SafeCover.v` connect the resulting positive-cost
segments to every step of the blank-tape run, including implicit blank padding.
`ActualNoSpinout.v` then excludes a reachable B0 right spinout and uses
`NoSpinout.v` and `Progress.v` to obtain state recurrence.

The witness JSON is finite input data. Its provenance is a native FAR run of the
canonical machine using the implementation at
[nickdrozd/busy-beaver-stuff, commit 7157fe5](https://github.com/nickdrozd/busy-beaver-stuff/tree/7157fe57a9c39edb3dcecc28036f09c3405a683a).
The same source lists a symmetry-equivalent program in `FAR_SOLVES['spinout']`.
The Coq proof checks the extracted data directly; it does not trust the native
solver, the extraction, or the data renderer.

The complete case checkpoint, including this last case, is available from the
repository root with `make proof-2-4-checkpoint BUILD_JOBS=8`.
To build this package alone with the Coq toolchain active:

```sh
make -C four all -j2
python3 four/tools/check_burn43_s071_far.py
```

The driver regenerates `Data.v`, the exact-machine example, and the census
inventory under `four/build/burn43-s071-far/proof`, compiles the package, and runs
a fresh recursive kernel audit. Generated Coq literals and compiled objects stay
in the ignored build directory. The inventory theorem covers all completions of
the exact table. This package contributes one state-based case; it does not
establish an instruction-based bound or the exhaustive BBB(2,4) upper bound.
