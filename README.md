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
- `theories/GTape.v` — guarded (walled) configurations: runs that
  provably depend only on a bounded window of the left half-tape,
  denoting a *family* of abstract configurations (one per unknown
  rest below the wall).  `gsteps_lift`/`gmatch_lift` are the
  translated-cycle induction.
- `theories/Mirror.v` — left/right machine symmetry; all
  quasihalting properties transfer, so checkers are written
  one-sided and side-L certificates run on the mirrored machine.
- `theories/Checkers/TCycler.v` — the translated-cycler checker
  (the harness's `tcycler` certificate, parameters `(anchor_step,
  period_steps, reach)`), never-QH and exact-last-visit QH variants,
  with soundness theorems and mirrored corollaries.
- `theories/Machines/Cycle_Examples.v`,
  `theories/Machines/TCycler_Examples.v` — end-to-end theorems for
  five concrete machines, including the BBB README's worked example
  `1RB1LD_1LC0LD_1RC1RA_0LB0RA` (anchor 2,487,033, period 17,620,
  reach 91): `vm_compute` re-simulates the 2.5M-step prefix and the
  guarded lap in ~15 s and the machine is proved to never quasihalt.
- `theories/Closure.v` — the generic covering-abstraction / liveness
  engine behind the whole n-gram / RepWL never-QH family: closed
  abstract sets give non-halting and per-step coverage
  (`closure_invariant`); per-state liveness is proved by *rank
  certificates* (an infinite q-avoiding run would project to a
  rank-strictly-decreasing abstract walk — `rank_find`), which is
  equivalent to the C verifier's SCC acyclicity but nearly
  graph-theory-free in Coq.  Closure search and rank computation are
  untrusted; only the closedness and rank-decrease *checks* carry
  proofs.  Silent (never-visited) states are skipped soundly, matching
  the upstream `neverqh_rwlsilent` convention.
- `theories/Checkers/ExactClosure.v` — the engine's simplest
  instance (exact normalized configurations): decides in-place
  cyclers and blank-trail translated cyclers with *no* cycle
  parameters at all, and validates the engine for the n-gram / RepWL
  instances to come.
- `theories/Checkers/NGram.v` — the n-gram CPS instance (the
  harness's `neverqh_ngram` certificate): contexts carry the n cells
  each side of the head; two gram sets over-approximate the deeper
  tape (every half-tape window at depth ≥ 1); moves consume a
  depth-1 gram on the approached side and donate the departed side's
  window to its set.  The gram sets are found by an untrusted
  two-level fixpoint mirroring the C prover, then everything is
  re-checked against the final sets.  Certificate-compatible with
  upstream `(t, n)` parameters (representation is list-based for
  now, so large-`n` certificates await the `positive`-encoding
  performance pass).
- `theories/Tests/*_Corruption.v` — negative controls in the BBB
  corruption-test tradition: mutated periods, sides, claims, states
  and last-visit indices are all rejected.

Axiom footprint: `functional_extensionality_dep` only (as in
Coq-BB5).  Full build: ~25 s.

## Build

Requires Coq (tested with 8.18):

```
make
```

## Next

Per SCOPING.md: the RepWL block-closure instance; the
ranking-measure rules (a)/(b) as refinements of the engine's rank
argument (these carry `neverqh_rank`'s 2,611 machines); the
`positive`-encoding performance pass (PositiveMap sets, as in
Coq-BB5) so large-`n` committed certificates verify; and the
certificate-table toolchain to ingest the BBB harness's `.cert`
files in bulk.
