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

The Phase 0/1 vertical slice and the core of the Phase 2
closure/liveness framework (n-gram instance, ranking rules,
`positive`-encoding performance layer) are in place:

- `theories/BBB4_Statement.v` — the (4,2) machine model
  (head-relative functional tape, `step`/`stepn`) and the
  quasihalting semantics that exists in neither reference repo:
  `VisitsAt` / `Visited` / `QuietFrom` / `QuasiHaltsSt` /
  `NeverQuasiHaltsSt` / `QuietAfter`, with the glue lemmas
  (never-QH implies not-QH and non-halting).
- `theories/CTape.v` — computable list-tape configurations, the
  `lift` denotation into the abstract model, step commutation, and
  decidable configuration equality up to blank padding.
- `theories/Checkers/Halt.v` — halting machines quasihalt trivially
  (the harness's `halt` certificate).
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
- `theories/PosEnc.v` — the `positive`-encoding performance layer
  (the Coq-BB5 playbook): self-delimiting bit encoders composing
  into an injective configuration encoding `cconf_enc`, plus
  Patricia-trie sets (`MSetPositive`) and `nat` tables
  (`FMapPositive`) keyed by encodings.  The one trusted fact is
  `pset_of_mem` (trie hit over an injectively encoded list ⇒ list
  membership); everything else is representation.
- `theories/Closure.v` — the generic covering-abstraction / liveness
  engine behind the whole n-gram / RepWL never-QH family: closed
  abstract sets give non-halting and per-step coverage
  (`closure_invariant`); per-state liveness is proved by *rank
  certificates* (an infinite q-avoiding run would project to a
  rank-strictly-decreasing abstract walk — `rank_find`), which is
  equivalent to the C verifier's SCC acyclicity but nearly
  graph-theory-free in Coq.  Closure search and rank computation are
  untrusted; only the closedness and rank-decrease *checks* carry
  proofs.  All membership the engine performs is trie lookup keyed
  by `a_enc`, and the untrusted ranks come from reverse-topological
  peeling (depth-many passes on acyclic subgraphs, immediate bail-out
  on cyclic ones) instead of blind Bellman iteration.  Silent
  (never-visited) states are skipped soundly, matching the upstream
  `neverqh_rwlsilent` convention.
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
  upstream `(t, n)` parameters.  Gram sets are tries keyed by the
  window encoding and certificate rank/potential tables compile to
  `PositiveMap`s once per component, so large-`n` certificates
  verify: `theories/Machines/Sample_LexCert_N5.v` re-proves the
  README sample machine at n = 5 — a 2,264-context closure with a
  generated ranking certificate (`tools/gen_lex_cert.py`, now
  self-contained over `tools/lex_prover.py`) — in ~5 s, where the
  list-based representation took ~3 min on the same table, and
  plain-acyclicity probes that took 165 s answer in under a
  second.
- `theories/Tests/*_Corruption.v` — negative controls in the BBB
  corruption-test tradition: mutated periods, sides, claims, states
  and last-visit indices are all rejected.
- `theories/PattCount.v` + the pattern-measure section of
  `theories/Checkers/NGram.v` — the C verifier's **full `rkv_delta`
  measure vocabulary**: a word over the alphabet counted over the
  whole tape (`RgA`) or strictly left/right of the head
  (`RgL`/`RgR`), e.g. the digram measures `11/R`, `01/A` that ~30%
  of the upstream rank certificates need.  Values are pattern
  occurrences in the padded configuration text; deltas are read off
  the abstract context alone (`occ_update`: a cell rewrite only
  changes the count over the `2|p|-1` window around the head;
  half-tape pushes/pops are prefix-occurrence indicators, with the
  left side handled by reversing the pattern).  `pm_exact` is the
  per-step exactness theorem; the `pm_ok` guard makes malformed
  patterns fail closed.  New certificate constructors
  `NgRankE`/`NgPattE` carry *encoded-key* tables (`positive`
  literals, ~5x smaller than context terms; the data is untrusted,
  so no key/context correspondence needs proving).
- `theories/Machines/Bulk/TCyc_*.v` — all 40 upstream `tcycler`
  certificate machines on the existing verified translated-cycler
  checker (pure data: side, anchor, period, reach; generated by
  `tools/gen_tcycler_certs.py`, which picks each machine's
  cheapest-to-reverify certificate across the upstream re-sweeps).
- `theories/Checkers/TCyclerN.v` — a binary-fuel front end for the
  tcycler checker: unary `nat` fuel materializes under `vm_compute`
  (~16 bytes/step, and the checker's four `cvisits` passes repeat
  it), which put the 309M-step-anchor machine
  `1RB0LD_1RC1LD_1LD0RC_0LA1LB` beyond a 15 GB budget.  `cstepsN` /
  `cvisitsN` iterate with `N.iter` instead; soundness is the
  `Nat.iter`/`N.iter` equivalence plus the existing theorem, so the
  trusted simulation semantics are untouched.  Anchors over 10M
  steps are emitted against this checker.
- `theories/Machines/Bulk/Bulk_R*.v` — 293 machines the upstream
  harness boarded with *stronger* cert types but that fall to the
  n-gram rank pipeline directly (`tools/sweep_remaining.py`: free
  choice of `t`/`n` plus the relaxed pattern-window bounds make our
  prover slightly stronger than the upstream neverqh_rank one): the
  entire `neverqh_rwl` + `neverqh_rwlsilent` populations (20), all
  6 `bouncer` machines, and 267 of the 610 never-QH `irules`
  machines.  The `rwlrank`/`fuel`/`drift` machines genuinely need
  their abstractions (measured 0 hits).
- **`theories/Machines/Bulk/` — 2,632 machine theorems** (the entire
  `neverqh_rank` + `neverqh_ngram` population of the BBB harness,
  71% of all decided holdouts), generated by
  `tools/gen_bulk_certs.py` from the committed C certificates:
  per machine a TM definition, a ranking certificate, and a
  `NeverQuasiHaltsSt` theorem named by its bbchallenge text, closed
  by `vm_compute` re-deriving the closure and re-checking every
  edge.  The untrusted prover (`tools/bulk_prover.py`) re-implements
  the closure + ranking-rules search with the full measure
  vocabulary; `tools/check_coverage.py` cross-checks the generated
  manifest against the BBB holdout list.  `Tests/Bulk_Corruption.v`
  adds pattern-measure negative controls (tampered pattern/region,
  all-blank and over-long patterns, retargeting).

- `theories/Checkers/Wrap.v` + `theories/Machines/Bulk/Wrap_01.v` —
  **the first quasihalting theorems**: the harness's wrapped
  quiet-state construction.  `tm_wrap tm q` redirects state `q` to
  halt; a halt-free n-gram closure of the *wrapped* machine from the
  *real* machine's step-`t` configuration proves `q` is never
  visited after `t` (a `q`-configuration has no wrapped successor,
  and off `q` the two machines agree step for step, `wrap_agree`).
  No liveness argument at all — closedness (`closure_invariant`)
  suffices, so all 18 upstream `wrapctl`/`wrapfar` machines board on
  the n-gram abstraction without their RepWL/DFA machinery.  Per
  machine: `NonHalt tm /\ QuietAfter tm q s /\ QuasiHaltsSt tm` with
  the exact last-visit index `s`.

Axiom footprint: `functional_extensionality_dep` only (as in
Coq-BB5).  Full build: ~10 min on 4 cores (53 generated bulk files
of ~12 s each dominate; the core library is ~30 s; the 309M-step
tcycler outlier ~40 min on its own core).

## Build

Requires Coq (tested with 8.18):

```
make
```

## Coverage

Of the 3,713 BBB(4) holdouts: **2,983 have a Coq theorem** (2,965
never-QH + 18 QH with exact last-visit scores), 18 are open
upstream, and 712 have C certificates awaiting their checkers, by
type: `irules` 505, `neverqh_rwlrank` 106, `neverqh_fuel` 62,
`neverqh_drift` 17, counter certs 22.  Run
`BBB_REPO=... python3 tools/check_coverage.py` for the live table.

## Next

Per NEXT_SESSION.md, by coverage-per-effort: the fuel/drift rules
(c2)/(c3) on the existing engine (+79; build the record/extent
substrate first), the RepWL block-closure instance with the five
rank measures (`neverqh_rwlrank`, +106), the irules engine (772
machines, the largest single block, per SCOPING §5 phase 4), and
the 22 counter machines as busycoq-style individual proofs.
