# Next session: start here

State as of 2026-07-15 (branch `claude/coq-bbb4-formalize-machines-0wih4v`,
everything committed and pushed, full build green).

## Scoreboard

Of the 3,713 BBB(4) holdouts (`BBB4_holdouts_3713.txt` in the BBB repo):

- **2,692 machines have a Coq theorem** in this repo (72.5%):
  - 2,632 `neverqh_rank`/`neverqh_ngram` machines
    (`theories/Machines/Bulk/Bulk_001..053.v`),
  - 20 `neverqh_rwl`/`neverqh_rwlsilent` machines that fall to the
    n-gram engine directly (`Bulk_R01.v`),
  - 40 `tcycler` machines (`TCyc_01..05.v`; big anchors on the
    binary-fuel `TCyclerN` front end).
- 18 open upstream (no certificate of any kind).
- 1,003 have C certificates but no Coq checker yet, by type:
  - **`irules` 772** — the geometric-sweeper engine (SCOPING §5
    phase 4, the largest single block, 6-10k LOC estimate).
  - **`neverqh_rwlrank` 106** — RepWL block closure + the five exact
    measures (`N/A N/L N/R 0/l 0/r`).  The plain rwl/rwlsilent
    machines fell to n-gram, but the rank variants genuinely need
    the block abstraction (measured: 0/106 fall to the n-gram
    pipeline even with free t/n and relaxed pattern bounds).
  - **`neverqh_fuel` 62 / `neverqh_drift` 17** — rules (c2)/(c3);
    need the record/extent substrate ("cells beyond the all-time
    extent are blank"), which is also the natural next core lemma.
  - **wrap QH certs** (`wrapctl`+`wrapfar` 12, `wrapfar` 6,
    `bouncer` 6) — quiet-state QH with exact scores; the `M'_q`
    halt-redirect closure *reuses the existing engine with no
    liveness at all* (non-halting of `M'_q` = q never fires), so
    this is mostly statement plumbing.  NB: the 94+9 machines with
    both a never-QH cert and a `wrapngram` cert are already boarded
    at state level (the wrap cert is their transition-level QH).
  - **counter certs 22** (`double/mono/mono2/blockdbl/spacer/
    interleave/bounce/gray/fractal_counter`) — SCOPING §6.5
    recommends busycoq-style individual proofs over porting the six
    parametric verifiers.

## What was built this session

1. `theories/PattCount.v` + pattern measures in `Checkers/NGram.v`:
   the C verifier's full `rkv_delta` vocabulary (word patterns over
   {0,1} x regions A/L/R), exactness proof `pm_exact`, fail-closed
   `pm_ok` guard, encoded-key cert constructors `NgRankE`/`NgPattE`.
   Key proof ideas: `occ_update` (a cell rewrite only changes counts
   in the `2|p|-1` window around it), reversed patterns for the left
   half-tape (all edits become cons-level), blank-absorption lemmas
   for walking off the written region.
2. `tools/bulk_prover.py` — untrusted closure + rules-(a)/(b) prover
   whose deltas mirror Coq `pm_delta` EXACTLY (agreement by
   construction, not argument); per-state candidate measures come
   from the upstream cert's `rank_q` lines.  t-minimization: 2,631
   of 2,632 machines certify at t=0 (one at t=64), so no 500k-step
   prefixes are re-simulated.
3. `tools/gen_bulk_certs.py` / `gen_tcycler_certs.py` — generators;
   `tools/check_coverage.py` — manifest vs holdout-list cross-check;
   `tools/sweep_remaining.py` — the opportunistic re-probe that
   found the 20 rwl/rwlsilent hits.
4. `theories/Checkers/TCyclerN.v` — binary-fuel (`N.iter`) front end
   for the tcycler checker (unary-nat fuel materializes ~16 B/step
   under vm_compute; the 309M-anchor machine needed it).
5. `theories/Tests/Bulk_Corruption.v` — negative controls for the
   pattern measures (tampered pattern/region, all-blank + over-long
   patterns, retargeting, starved rounds).

## Gotchas discovered (do not re-learn these)

- **Coq's `ng_grow` is donation-gated**: a blocked context's
  successors are not explored until the *next* round, so it needs
  more rounds than the Python fixpoint loop.  Sound bound: each
  non-final round adds >= 1 gram and the Coq sets stay inside the
  Python fixpoint, so emit `rounds = |lset|+|rset|+4`.  (Python's
  own round count is NOT a valid bound - this cost a debugging
  session.)
- **`syms_app` has an `xO` end-of-list marker**: the Python mirror
  of `cconf_enc` must start its fold with `p = 2*p`.
- Emitted `nat` literals > 5000 are decomposed as `(k * 1000 + r)`
  by `fmt_nat` (parser warning); values are small (max phi 1,161,
  max K 578 across all 2,632 machines), so unary-nat cert values
  are safe.
- Machines with `---` transitions are fine at state level (the
  closure proves them unreachable); `------` silent states pass
  through the engine's visited-premise convention.
- Parallel `coqc` on the big tcycler files at 5 GB each OOM-killed
  each other on the 15 GB box; the N-fuel front end removed the
  pressure (~1 GB each).

## Next moves, by coverage-per-effort

1. **Wrap QH certs (~24 machines + the QH statement machinery)**:
   `M'_q` construction + halt-free closure via the existing engine;
   exact scores from the simulated prefix.  Opens the QH side of
   the census, which nothing currently exercises.
2. **Fuel/drift rules (79)**: build the record/extent substrate
   first (SCOPING §4 "prove once, early"); (c2) then adds capped
   sided counts to the context, (c3) the record argument.
3. **RepWL + rwlrank (106)**: new abstraction instance of the same
   engine; the five measures need exact per-step deltas (interior
   blanks are the subtle ones).
4. **irules (772)**: the big one; SCOPING §5 phase 4.  v1 subset
   first.
5. The 22 counter machines as busycoq-style individual proofs.

## Hard rules (unchanged)

- Everything emitted by tools/ is UNTRUSTED; only the Coq checkers
  carry soundness.  Never weaken a checker to make a cert pass.
- Every new certificate feature gets corruption tests that MUST
  fail.
- `make` stays green; axiom footprint stays
  `functional_extensionality_dep` only (check with
  `Print Assumptions`).
