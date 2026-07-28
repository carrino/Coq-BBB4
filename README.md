# Coq-BBB4

> **Contributors / agents: read the PLAYBOOK at the top of `NEXT_SESSION.md`
> before starting census or proof work** — it covers the compute discipline
> (heavy `native_compute` runs on stable hardware, never the preempting
> container), the committed-census cache, and the long-tail roadmap. The
> coverage numbers lower in *this* README are STALE; `NEXT_SESSION.md` +
> `tools/check_coverage.py` are authoritative.

> **What is actually proved, stated precisely — including what is NOT:
> [`docs/CLAIMS.md`](docs/CLAIMS.md).**  The frontier that remains, mapped by
> shape and blocker: [`docs/RESIDUE_MAP.md`](docs/RESIDUE_MAP.md).

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
- `theories/Records.v` — the record/extent substrate (SCOPING §4)
  the fuel/drift rules (c2)/(c3) stand on, proved once on the bare
  `step`/`stepn` semantics with **no axioms**: on each side of the
  head the nonblank cells lie inside a bounded window
  (`right_bounded`/`left_bounded`), a step grows each window by at
  most one, and a step *toward* a side shrinks that side's window.
  Consequences: `extent_le_steps` (after `n` steps from the blank
  tape every cell at offset `n` or beyond is blank) and
  `run_right_exhausts` — a run confined to a right-moving runner for
  `R` steps drives the right window to 0, i.e. the whole right
  half-tape blank.  That last fact is the record argument that makes
  a "fuel >= 1 on the movement side, forever" invariant impossible,
  so rule (c2) can discharge runner SCCs; the left-runner case rides
  the `Mirror` transfer.
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
  `neverqh_rwlsilent` convention.  The engine also carries the
  **runner rule (c2)** (`neverqh_fuel`, on top of `Records.v`):
  `runner_find` proves a state recurs when every one of its
  q-avoiding closure nodes both moves the head right and holds a
  right nonblank — the right window (a nat bounded by the step
  index) strictly shrinks on each avoided step yet fuel keeps it
  positive, an impossible descent.  `closure_check_neverqh_fuel`
  discharges each visited state by EITHER a lex-rank certificate OR
  the runner rule — the mix the upstream fuel procedure produces —
  and is parametric over two node predicates (`moves_right`,
  `rfuel_ge1`) that the fuel-refined abstraction supplies; the
  existing lex/rank instances are untouched (axiom footprint stays
  `functional_extensionality_dep`).
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
- `theories/Machines/Bulk/Bulk_R*.v` — 446 machines the upstream
  harness boarded with *stronger* cert types but that fall to the
  n-gram rank pipeline directly (`tools/sweep_remaining.py` and the
  digram-candidate second pass: free choice of `t`/`n`, relaxed
  pattern-window bounds, and digram measures offered to the
  procedure even when the upstream cert names none): the entire
  `neverqh_rwl` + `neverqh_rwlsilent` populations (20), all 6
  `bouncer` machines, and 420 of the 610 never-QH `irules`
  machines.  The `rwlrank`/`fuel`/`drift` machines genuinely need
  their abstractions (measured: 0 hits even in the second pass).
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
  the exact last-visit index `s`.  A second checker
  `ngram_check_qhbound` (same file) delivers the **census-grade**
  decision `NonHalt /\ QHBound (S t) /\ QuasiHaltsSt`: it adds the
  engine's plain-acyclicity rank liveness (`Closure.live_ok`) over the
  SAME wrapped closure, so every state that appears recurs (`rank_reach`
  + `live_appears_recur`) and every quiet state's last visit is `<= t`
  -- exactly the `QHBound` the census contract wants, from which the
  20,568 wrap-decidable residue machines can leave `D_census` (the
  plain-acyclicity gate catches ~24% now; the rest want measure-based
  liveness).  `theories/Tests/QHB_Probe.v` proves 150 residue machines
  this way under `vm_compute`.
- `theories/Checkers/FuelClass.v` — the capped sided-count *classes*
  for the fuel refinement, as a verified lower bound (`F0` no info /
  `F1` >= 1 / `F2` >= 2, all rule (c2) reads).  Unlike the exact
  capped count, a lower bound makes each per-move update a
  deterministic constructive function: `finc_sound` (a deposited
  write raises the class), `fdec_sound` (a crossed cell lowers it),
  `fc_ge1_sound` (>= 1 witnesses a nonblank).  Sound by construction
  (a lower-bound class covers any config with at least that many
  nonblanks), no axioms.
- `theories/Checkers/Fuel.v` + `theories/Tests/Fuel_Examples.v` —
  **the `neverqh_fuel` checker (rule (c2))**: instantiates the
  engine's `closure_check_neverqh_fuel` on the existing n-gram
  abstraction, so the full rank/pattern measure vocabulary and its
  exactness proofs carry over verbatim and each visited state is
  discharged by *either* a lex-rank certificate *or* the runner rule.
  The two runner node facts are read off the context: the head
  symbol pins the move direction (`fnode_moves_right`), and a
  nonblank in the right window witnesses right fuel
  (`fnode_rfuel_ge1`) — so this discharges runner SCCs whose fuel
  stays within `n` cells; the `FuelClass` classes are the drop-in for
  beyond-window fuel.  `ngram_check_neverqh_fuel_sound` has axiom
  footprint `functional_extensionality_dep`; `Fuel_Examples` re-proves
  a committed bulk machine through it end to end (`vm_compute`),
  confirming the checker subsumes the pure lex checker.  Landing the
  62 upstream machines next needs the untrusted prover to emit their
  runner-mode certificates.

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

Of the 3,713 BBB(4) holdouts: **3,136 have a Coq theorem** (3,118
never-QH + 18 QH with exact last-visit scores — 84.5%), 18 are open
upstream, and 559 have C certificates awaiting their checkers, by
type: `irules` 352, `neverqh_rwlrank` 106, `neverqh_fuel` 62,
`neverqh_drift` 17, counter certs 22.  Run
`BBB_REPO=... python3 tools/check_coverage.py` for the live table.

## Next

Per NEXT_SESSION.md, by coverage-per-effort: the fuel/drift rules
(c2)/(c3) on the existing engine (+79).  The liveness side is now
built and verified: `Records.v` (the record/extent substrate) and
the runner rule (c2) + combined `closure_check_neverqh_fuel` in
`Closure.v`.  What remains to LAND the fuel machines is the one
missing piece — the fuel-refined abstraction that supplies the two
node predicates: an n-gram context paired with the capped sided
nonblank classes {0,1,>=2}, `succs` propagating the class by the
sided-count delta (with the cap's conservative branch), the
class-0-with-a-nonblank-in-window prune, and `covers` pinning each
class to the true capped count (so `rfuel_ge1` is sound off-window).
Then: rule (c3) drift (the same substrate, +17), the RepWL
block-closure instance with the five rank measures
(`neverqh_rwlrank`, +106), the irules engine (352, the largest
single block, per SCOPING §5 phase 4), and the ~42 counter machines
as busycoq-style individual proofs.

## Counters track (individual proofs)

The ~40 counter-machine holdouts (SCOPING section 5 phase 5) are
being boarded as busycoq-style individual proofs, natively in the
BBB4 statement world: `theories/Counters/` carries the windowed-run
toolkit (`WTape.v`: walled `wsteps`, transport into `csteps`, the
`cycR`/`cycL`/`cycLW` repetition cycles), the never-quasihalting
closer (`LapGlue.v`: bootstrap + lap + visit witnesses), and the
shared counter encodings (`MonoCounter.v`).  Each machine's lap is
decomposed into ~15 windowed unit runs (closed by `reflexivity`)
chained through the cycles, with the binary increment's carry read
off a `positive` view; the decomposition is first validated
differentially against the raw simulator by the untrusted executors
in `tools/counters/`.  Boarded so far: the full `mono_counter`
family (#10 #26 #31) and the full `spacer_counter` family
(#16 #22 #23) -- 6 machines, each
`nqh_<machine text> : NeverQuasiHaltsSt`, axiom footprint
`functional_extensionality_dep` only, tracked in
`tools/counters_manifest.tsv`.  Status and the per-machine recipe:
the counters section of NEXT_SESSION.md.

### Counters track, session B (interleave / exp / bounce)

Seven more machines boarded by the parallel session-B sprint, own
files only (`ILCounter.v`, `ExpCounter.v`, `BounceCounter.v`,
`MeasureGlue.v`; `Machines/Counters/{Interleave,Exp,Bounce}_*.v`;
`Tests/CountersB_Corruption.v`): the full `interleave_counter`
family (#18 #35), the full `exp_counter` family (#2 #4 #12), and the
full `bounce_counter` family (#8 #33).  Bounce is the family whose
liveness needs a well-founded measure: `MeasureGlue.mrun` composes a
measure-decreasing recurrence of exact micro laps (the nested
working-area binary counter, measure = the complement value of the
digit word) into each macro lap D(k) -> D(k+1), and
`LapGlue.glue_neverqh` closes over the macro family as usual.  All
seven are `nqh_<machine text> : NeverQuasiHaltsSt`, axiom footprint
`functional_extensionality_dep` only, rows in
`tools/counters_manifest.tsv`, executors `tools/counters/lap{18,35,2,4,12,8,33}.py`.

<!-- --- irules mass-board --- -->

## IRules mass-board

The irules block is now largely landed: **250** of the 352
irules-typed holdouts are boarded in
`theories/Machines/IRules_Batch_00.v`..`IRules_Batch_08.v` (TM +
`IRCert` literal + one `vm_compute` through
`irules_check_neverqh_sound`, fuel 300000, plus a `_nonhalt`
corollary each; manifest `tools/irules_manifest.tsv`).  Negative
controls live in `theories/Tests/IRulesBatch_Corruption.v`.  The
remaining 102 irules certs use post-v1 format features (multi-step
decrements, v6 block rules, ...) the verified engine does not model
yet -- see `tools/irules_deferred.tsv` and the NEXT_SESSION
irules append.  Coq-proven coverage after this block: **3,402 /
3,713**.

### Fuel track (neverqh_fuel mass-board)

The full family of 62 upstream `neverqh_fuel` holdouts is boarded:
`nqh_<machine> : NeverQuasiHaltsSt` + `nonhalt_<machine>` corollaries
in `theories/Machines/Fuel_Batch_{01,02,03}.v`, axiom footprint
`functional_extensionality_dep` only, rows in
`tools/fuel_manifest.tsv`.

The boarding took an engine extension (two NEW checker files; the
merged Fuel.v/FuelClass.v/Closure.v are untouched):

- `theories/Checkers/FuelSCC.v` -- the per-SCC runner rule (c2)
  integrated into the lexicographic gate: every q-avoiding edge is
  lex-good OR internal to an untrusted "runner gate" whose nodes all
  move right with fuel, with every lex component non-increasing
  across it.  Soundness: the lex tuple never increases along a
  q-avoiding run, so by well-foundedness lex-good edges stop; the
  confined tail then drives the right window to zero against the
  fuel invariant (outer `Acc lexlt` induction + inner window-bound
  induction; `lexle` threads the bookkeeping).
- `theories/Checkers/FuelWide.v` -- the class-refined instance
  promised by Fuel.v's header: contexts `cconf * (fclass * fclass)`
  with the FuelClass lower-bound classes, deterministic per-step
  class updates (`finc` the write behind the move, `fdec` the
  crossed window cell), runner fuel read window-OR-class, exact
  capped seed classes from the anchor configuration, refined-key
  certificate tables.

The in-window checker alone provably boards NONE of the 62 (the
previous session's result, kept in `tools/fuel_deferred.tsv` history:
every residue was a uniform-direction runner SCC with blank
movement-side windows -- in-window fuel is subsumed by lex).  The
generator `tools/gen_fuel_certs.py` searches with the exact Python
mirror of the refined checker (classes, per-SCC kills, the
`fw_edge_ok` gate), differential-validates every state's certificate
out of Coq, and emits the batches; 62/62 land, 54 via the
`mirror_never_qh` transfer (left-runners), 8 direct.  Negative
controls: `theories/Tests/FuelBatch_Corruption.v` (both checkers:
transition mutants, wrong runner-state markings -- erased and swapped
gates -- gutted rank tables, starved budgets, all computing `false`).


### RepWL track (neverqh_rwlrank mass-board)

The full family of 106 upstream `neverqh_rwlrank` holdouts is
boarded: `nqh_<machine> : NeverQuasiHaltsSt` + `nonhalt_<machine>`
corollaries in `theories/Machines/RepWL_Batch_{01..04}.v`, rows in
`tools/repwl_manifest.tsv`, axiom footprint
`functional_extensionality_dep` only.

The checker is a NEW `Closure.v` engine instance,
`theories/Checkers/RepWL.v` (`rw_check_neverqh_sound`): whole-tape
repeated-word-list configurations -- a whole-block buffer around the
head plus run-length item lists with counts capped at a threshold T
("T or more") -- with a symmetric single-step relation (fold the
departed-end block on buffer overflow with a saturating merge, pop
the arrival side's nearest item with a cap branch), an item-list
denotation with existential counts for capped items, and the five
documented measures (N/A, N/L, N/R nonblank counts; 0/l, 0/r
interior blank counts) whose per-node deltas are proved exact: the
arrival cell and the "nonblank strictly beyond" witness bits are
determined by the node because well-formedness forces capped counts
>= 2 (hence the checker's 2 <= T gate).  No untrusted gram sets --
the abstraction is self-contained, so certificates are just per-state
lexicographic component tables over `rconf_enc` keys.

`tools/repwl_prover.py` is the exact Python mirror (seed, step,
encoding, component semantics); `tools/gen_repwl_certs.py` emits the
batches.  All 106 land at t=0 with the cert-declared (block,
threshold) parameters; largest closure 13,994 abstract
configurations.  Negative controls:
`theories/Tests/RepWLBatch_Corruption.v` (transition mutant, swapped
certificates, gutted rank tables, empty certificate, starved budget,
and the out-of-gate parameters L=0 / T=1, all computing `false`).
<!-- --- drift track --- -->
### Drift track (`neverqh_drift` mass-board)

All 17 upstream `neverqh_drift` holdouts are boarded:
`nqh_<machine> : NeverQuasiHaltsSt` + `nonhalt_<machine>` corollaries
in `theories/Machines/Drift_Batch_01.v`, rows in
`tools/drift_manifest.tsv`, axiom footprint
`functional_extensionality_dep` only.

The checker is `theories/Checkers/Drift.v`
(`ngram_check_neverqh_driftw_sound`): rule (c3) — a stuck SCC in
which every cycle has strictly positive net head displacement toward
one side, and every context moving TOWARD that side holds fuel there,
cannot confine a run — integrated into the FuelSCC-style lex gate on
the class-refined FuelWide contexts, which are reused unchanged.  The
runner gate becomes a DRIFT gate carrying untrusted per-node
potentials `phi` and a scale `W` (`phi a' + 1 <= phi a + W` on
toward-moving sources, `phi a' + W + 1 <= phi a` on away-moving ones:
telescoping forces `W * net >= cycle length`, i.e. net-positive
cycles; the generator finds `phi` by Bellman-Ford, the checker only
re-checks edges).  The descent replaces FuelSCC's window induction by
the natural measure `W * R + phi a` — a fueled toward-move shrinks
the Records.v window bound exactly, an away-move's potential pays for
the window growth — so fuel is only demanded of toward-moving gate
nodes, strictly weaker than the C rule's premise.

There are TWO disjoint gates per state (one per drift side), which is
load-bearing: `1RB1LC_1LC0RB_1RD0LC_0RD1LA` (q=B) and
`1RB1LD_1LC0RB_0LC1RA_1LA0LD` have single states whose stuck SCCs
drift opposite ways, so no machine-level mirror orientation works.
Disjointness collapses the two descent budgets into one selector
(`dbudget`), keeping the proof structurally FuelSCC's.

`tools/drift_prover.py` is the untrusted Python mirror (two-sided
per-SCC kill + `dw_state_check`, the faithful edge-by-edge mirror of
`drift_state_ok`); `tools/gen_drift_certs.py` emits the batch.  All
17 land at n=2 t=0, largest closure 195 refined contexts.  Negative
controls: `theories/Tests/DriftBatch_Corruption.v` (transition
mutant, erased gates, zeroed potentials, swapped gate sides, merged
gates — disjointness is checked — zeroed scale W, demotion to the
FuelWide rule-(c2) checker, empty certificate, starved budget, all
computing `false`).

<!-- --- irules multi-decrement track --- -->
### IRules multi-decrement track (general step-size decrements)

All 42 `certs_modclass` v3 irules holdouts whose blocker was the
decrement step size are boarded: `irk_<machine>_never_quasihalts :
NeverQuasiHaltsSt` + `irk_<machine>_nonhalt` corollaries in
`theories/Machines/IRulesK_Batch_{01..06}.v`, rows in
`tools/irulesk_manifest.tsv`, coverage 3587 -> 3629, axiom footprint
`functional_extensionality_dep` only.

The v1 rule applier (`theories/Checkers/IRules/Rules.v`,
`rule_apply` / `find_dec`) fires a rule whose one decrementing run
drains at step `d = -1` (`find_dec` hardcodes `d =? -1`).  The checker
`theories/Checkers/IRules/RulesK.v` (`ruleK_apply_sound`) +
`MetaK.v` (`irulesk_check_neverqh_sound`) generalises this to any
negative constant delta with the v3 binding-run semantics of
`../BBB/docs/irules2.md` "Multi-decrement rules, general step sizes":
the application count `R = (e_j - lb_j)/d_j + 1` is an exact affine
expression from a binding run `j` whose `d_j` divides `e_j - lb_j`,
and every decrementing run must survive `R` rounds.  The binding
search (`find_binding`) is UNTRUSTED — the guard `expr_ge lo Rex 1`
and `appK_side`'s per-run survival re-check (`e + d*Rex >= lb + d`,
the last-round minimum) carry soundness for ANY count, so the proof
never reasons about the division.  Output is uniform (`e -> e + d*Rex`,
drop a decrement reaching the constant 0); with a single `-1`
decrement it reduces to the v1 semantics.  The whole file reuses the
v1 rule type and denotation machinery (`vvals`, `rstart`/`rend`,
`rule_sem`, `scfg_eqb`) and edits none of
`Expr`/`RLE`/`Engine`/`Rules`/`Meta`.

Ten of the 42 also need **rule-in-rule application** (BBB
`docs/irules2.md` "Rule-in-rule application, one level"): a later
rule's proof applies an already-validated earlier rule.  Without it
that rule's replay ratchets over a symbolic-count run and never closes
(the head crosses it via a multi-step maneuver the engine peels
cell-by-cell).  This is NOT a new engine op — it reuses `ruleK_apply`.
`RulesK.check_rulesK` validates the rules in index order, threading the
already-validated ones (of lower index) into each rule's replay via
`ruleK_check`; `check_rulesK_sound` is a direct induction discharging
`replayK_sound`'s per-rule Reach obligation with `ruleK_apply_sound`.
`MetaK` runs `check_rulesK` (not `Meta.check_rules`); the anchor and
coverage checks are still reused from `Meta` unchanged.

`tools/irulesk_prover.py` is the untrusted Python mirror (a faithful
port of the symbolic engine + the binding-run applier + rule-in-rule
validation; it validates all 504 rules across the 428 v1 certs, and its
42 accepts equal the C verifier's accepts — no false positives).
`tools/gen_irulesk_certs.py` re-validates each machine through that
mirror before emitting the batch.  Negative controls:
`theories/Tests/IRulesKBatch_Corruption.v` (binding run at a
non-dividing run, `lb` below the step so the drain goes negative,
survive-R-rounds over-count, transition mutant, delta demoted to `-1`,
and rule-in-rule dependency reordered / dropped, all computing
`false`).

<!-- --- irules block-run track --- -->
## IRules block-run checker (Phase 1: 5 of 6 v3-blk boarded)

`theories/Checkers/IRules/EngineK.v` forks the v1 IRules engine so a
run's symbol may be a BLOCK id `>= 2` drawn from the certificate's
untrusted block table (`blk <id> <cells>`): a run `(B, e)` denotes `e`
copies of `B`'s cell sequence.  The block denotation `bdside tbl` is
parametric in the table (soundness holds for ANY table), reducing to
`RLE.dside` on raw-only sides.  `beng_step`/`beng_step_sound` prove one
engine op -- concrete head step + chain hops + block PEEL + block HOP --
is a `Reach` against `bdside tbl`, `functional_extensionality_dep` only.
The block-hop crux (`hop_sim`/`hop_one_reach`/`hop_copies`/`bhop_reach`)
replays one copy of a block as a zipper (each step one `cstep`), then
crosses all `e` copies by induction.  The design is mirrored (and
differentially validated vs `bin/verify` on 651 certs, no false
positives) by `tools/irulesblk_prover.py`.  The full vertical (EngineK -> RulesBlk -> MetaBlk) boards 5 of the 6
v3-blk holdouts through `irulesblk_check_neverqh` (`vm_compute`),
`functional_extensionality_dep` only; the 14-block monster (partial
absorb) and the 44 v6 blk+rulepfx holdouts are deferred -- see
`NEXT_SESSION.md`, "irules BLOCK-RUN track".
<!-- --- end irules block-run track --- -->
