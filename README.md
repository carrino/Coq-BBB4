# Coq-BBB4

A Coq formalization of the Beeping Busy Beaver BBB(4) results
produced by the [BBB harness](https://github.com/carrino/BBB):
machine-checked proofs of never-quasihalting / quasihalting (with
exact last-visit indices) for the BBB(4) holdout list, built on the
patterns of [Coq-BB5](https://github.com/carrino/Coq-BB5) and
[busycoq](https://github.com/carrino/busycoq).

See [SCOPING.md](SCOPING.md) for the full inventory of what needs
formalizing (20 certificate types over 3,685 decided machines, 28
still open upstream), the reuse assessment, the phased plan, and the
architecture.

## Current state

The Phase 0/1 vertical slice is in place:

- `theories/BBB4_Statement.v` — the (4,2) machine model
  (head-relative functional tape, `step`/`stepn`) and the
  quasihalting semantics that exists in neither reference repo:
  `VisitsAt` / `Visited` / `QuietFrom` / `QuasiHaltsSt` /
  `NeverQuasiHaltsSt` / `QuietAfter`, with the glue lemmas
  (never-QH implies not-QH and non-halting).
- `theories/CTape.v` — computable list-tape configurations, the
  `lift` denotation into the abstract model, step commutation, and
  decidable configuration equality up to blank padding.
- `theories/Checkers/Cycle.v` — the first verified checker
  (the harness's `inplace` certificate, generalized to
  head-relative configuration equality): `cycle_check_neverqh` and
  `cycle_check_qh`, each with a soundness theorem, closed by
  `vm_compute` per machine.
- `theories/Machines/Cycle_Examples.v` — end-to-end theorems for two
  concrete enumerated machines: `1RB0LC_0LA0LC_0LD0RD_1LA---` never
  quasihalts (state level); `1RB0LC_0LA0LC_0LD1RA_1LA---` is a
  non-halting quasihalter whose state D is last visited at
  configuration index 4.
- `theories/Tests/Cycle_Corruption.v` — negative controls in the BBB
  corruption-test tradition: mutated periods, claims, states and
  last-visit indices are all rejected.

Axiom footprint: `functional_extensionality_dep` only (as in
Coq-BB5).

## Build

Requires Coq (tested with 8.18):

```
make
```

## Next

Per SCOPING.md: the `tcycler` (translated cycler) checker — the
most-reused induction in the development — then the closure/liveness
framework (n-gram / RepWL / ranking rules) that carries ~2,800 of the
decided holdouts, and the certificate-table toolchain to ingest the
BBB harness's committed `.cert` files.
