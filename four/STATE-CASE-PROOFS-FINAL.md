# Final state case for BBB(2,4)

S071, `1LB2RA3LA2RB_0RB3LB0LA1RA`, completes the original 78 hard state
cases. Its Coq proof establishes `QHBound 0 s71_tm`: both states recur
arbitrarily late. The all-completion inventory covers the exact complete table
with codes `[5,10,12,11,3,13,0,6]` and packed code `2480798428`.

This completes the machine-case proofs. The universal BBB(2,4) upper bound still
requires exhaustive census assembly and the final two-root connection.
No instruction-based result is claimed by this package.

## Build and audit

With the tested Coq 8.18.0 / OCaml 4.14.2 toolchain, run from the repository root:

```bash
make proof-2-4-checkpoint BUILD_JOBS=8
```

This checks the public four-symbol development, the initial 36 cases, the
additional 30, the recent 11, and S071. Each case runner performs recursive
kernel audits. The final equality target, `make proof-2-4`, remains unavailable
until the exhaustive upper bound is assembled; its success report requires
the actual global equality theorem.

For S071 alone, activate the toolchain and run:

```bash
make -C four all -j2
python3 four/tools/check_burn43_s071_far.py
```

The runner checks frozen input and source hashes, regenerates the finite data
and exact inventory, compiles 20 modules, and freshly audits the full inventory
dependency closure without reusing prior audit receipts. Logs and the current
receipt are under `four/build/burn43-s071-far/proof/`. The frozen result is
[burn43-s071-far-checked.json](research/burn43-s071-far-checked.json).

## Proof method

An extracted finite-automata-reduction certificate uses two-cell blocks.
The generic Coq checker verifies its finite closure clauses. A recursive stack
grammar then supplies an invariant at every block boundary. Forty concrete
local executions, each at most five steps, preserve safety; positive segment
lengths and explicit blank-padding transport cover every actual machine step.
This excludes permanent B-only spinout and proves state recurrence.

The [source package](proof-sources/burn43-s071-far/) includes the generic
checker soundness proof, concrete execution bridge, and exact machine theorem.
The compact native witness and its renderer are untrusted input: Coq checks
the resulting finite certificate and local executions. Generated `Data.v`
and compiled objects stay under ignored `four/build/`.

Independent review reproduced the proof from a source-only checkout, built
all 41 core dependencies and 20 proof modules, and recursively checked 280
modules with zero audit reuse. It also verified exact all-completion types,
finite-certificate rejection controls and frozen-input guards. The finite
checker and local computations are axiom-free; final tape transport uses the
repository's existing functional extensionality axiom.
