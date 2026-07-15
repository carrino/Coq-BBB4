# Next session: start here

State as of 2026-07-15 (branch `claude/coq-bbb4-formalize-machines-0wih4v`,
everything committed and pushed, full build green).

## Scoreboard

Of the 3,713 BBB(4) holdouts (`BBB4_holdouts_3713.txt` in the BBB repo):

- **3,136 machines have a Coq theorem** in this repo (84.5%;
  3,118 never-QH + 18 QH with exact scores):
  - 2,632 `neverqh_rank`/`neverqh_ngram` machines
    (`theories/Machines/Bulk/Bulk_001..053.v`),
  - 446 machines from stronger upstream cert types that fall to the
    n-gram rank pipeline (`Bulk_R01..09.v`): all 20 rwl/rwlsilent,
    all 6 bouncers, 420 of 610 never-QH irules,
  - 40 `tcycler` machines (`TCyc_01..05.v`; big anchors on the
    binary-fuel `TCyclerN` front end; the 309M-step outlier
    verifies in ~16 min),
  - 18 wrap-QH machines (`Wrap_01.v`), the first quasihalting
    theorems, exact last-visit indices.
- 18 open upstream (no certificate of any kind).
- 559 have C certificates but no Coq checker yet, by type:
  - **`irules` 352** — the geometric-sweeper engine (SCOPING §5
    phase 4, the largest single block, 6-10k LOC estimate); the
    n-gram-tractable subset is already stripped out.
  - **`neverqh_rwlrank` 106** — RepWL block closure + the five exact
    measures (`N/A N/L N/R 0/l 0/r`).  The plain rwl/rwlsilent
    machines fell to n-gram, but the rank variants genuinely need
    the block abstraction (measured: 0/106 fall to the n-gram
    pipeline even with free t/n, relaxed pattern bounds, AND digram
    candidates -- same for fuel/drift).
  - **`neverqh_fuel` 62 / `neverqh_drift` 17** — rules (c2)/(c3);
    need the record/extent substrate ("cells beyond the all-time
    extent are blank"), which is also the natural next core lemma.
  - **wrap QH certs: DONE** (`Wrap.v` + `Wrap_01.v`, all 18).  NB:
    the 94+9 machines with both a never-QH cert and a `wrapngram`
    cert are already boarded at state level (the wrap cert is their
    transition-level QH).
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
5. `theories/Checkers/Wrap.v` + `Wrap_01.v` — the quiet-state QH
   construction (`tm_wrap` halt-redirect; halt-free closure of the
   wrapped machine from the real step-`t` config; `wrap_agree`
   transfers immortality and q-freeness back).  All 18 upstream
   wrapctl/wrapfar machines board at n=2, t=s+1 in ~1 s total.
6. `theories/Tests/Bulk_Corruption.v` / `Wrap_Corruption.v` —
   negative controls (tampered pattern/region, all-blank + over-long
   patterns, retargeting, starved rounds, wrong quiet state/index).

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

## Scope B: the full BBB(4) census, the Coq-BB5 way (AGREED PLAN)

The non-holdout complement (the "easy" machines) has NO upstream
certificates -- the holdout list is the output of external,
unformalized deciders -- so a genuine BBB(4) theorem re-decides the
whole (4,2) TNF space in Coq.  Do it exactly like Coq-BB5's census
(read `Coq-BB5/CoqBB5/BB5/README.md` "Proof structure" first):

- **Store nothing per machine.**  BB5 enumerates 181,385,789
  machines as ONE in-Coq computation: a `SearchQueue` over the TNF
  tree (`BB5_TNF_Enumeration.v`), each popped machine run through
  `decider_all` (verified decider FUNCTIONS with generic
  parameters, `BB5_Deciders_Pipeline.v`); nonhalt = leaf, halt =
  push children; the whole walk is `Eval native_compute in
  (Nat.iter 200 q_suc q_0)`.  The theorem is a queue invariant
  (`SearchQueue_WF`), so no machine is ever named or stored.  A
  separate OCaml extraction reproduces the list as CSV if wanted.
- **The economics**: 96.7% of BB5's machines fall to "Loops" (a
  bounded step-simulator with cycle detection), 6M to NGramCPS with
  small generic parameters; only 8,032 machines get hardcoded
  per-machine parameters, 30 get certificates, 13 get hand proofs.
  At OUR scale (BB4 = 858,909 TNF machines, no hardcoded params, no
  sporadics) the whole census compiles in ~30 s with coq-native.
- **The port**: lift `TNF.v` + `SearchQueue` from
  `Coq-BB5/CoqBB5/BB4/`; replace the halting decider contract with
  a quasihalting one (SCOPING §4 `BBBDecider`:
  `Result_NeverQH | Result_QH score | Result_Unknown`); pipeline =
  (1) bounded cycle/tcycler detection [Loops tier], (2) the n-gram
  closure with IN-COQ rank search [see below], (3) fallthrough to
  the holdout list, which is exactly the analogue of BB5's
  hardcoded+sporadic tail and is already 84.5% done here.
- **New lemmas needed**: the "don't-care completion" argument (TNF
  enumerates machines with undefined transitions once; a
  never-fired transition cannot affect QH status or score -- the
  quasihalting analogue of `CountHaltTrans_0_NonHalt`), and the QH
  score bookkeeping on the halting side of the tree.
- **First move next session (cheap, decisive)**: run the Python
  ladder (cycle -> tcycler -> ngram/rank) over the full (4,2)
  enumeration to measure what the generic tiers kill under
  QUASIHALTING (nobody has measured this; the standard censuses
  stop at halting).  That sizes the Coq sweep before any port work.

### Kill the million lines of tables while we're at it

99.3% of this repo's lines (1.50M of 1.52M) are generated
certificate tables (`Bulk_*.v`): per-context rank/potential/gate
data for 3,136 machines.  The hand-written development is ~11k
lines.  BB5 ships no such tables because its deciders SEARCH inside
Coq rather than check external data.  We can retrofit: the engine
already computes plain acyclicity ranks in-Coq (`compute_ranks` in
`Closure.v`); implementing the full rank PROCEDURE (SCC peeling,
measure candidate selection over the pattern vocabulary, Bellman
potentials -- exactly what `tools/bulk_prover.py` does in Python)
as an untrusted in-Coq function would shrink every bulk entry to a
one-line `(machine, n, t)` tuple and delete the tables.  Costs:
~1k lines of (untrusted, proof-free) search code + compile time for
the in-Coq search -- with coq-native at (4,2) scale, likely fine.
This is also a PREREQUISITE-quality piece for the census pipeline
(tier 2 above needs exactly this search as a decider function), so
build it once, use it in both places.

## Next moves, by coverage-per-effort

1. **Fuel/drift rules (79)**: build the record/extent substrate
   first (SCOPING §4 "prove once, early"); (c2) then adds capped
   sided counts to the context, (c3) the record argument.
2. **RepWL + rwlrank (106)**: new abstraction instance of the same
   engine; the five measures need exact per-step deltas (interior
   blanks are the subtle ones).
3. **irules (352 remaining)**: the big one; SCOPING §5 phase 4.
   v1 subset first.  The QH side of irules (163 machines with exact
   scores) also lives here.
4. The 22 counter machines as busycoq-style individual proofs.

## Hard rules (unchanged)

- Everything emitted by tools/ is UNTRUSTED; only the Coq checkers
  carry soundness.  Never weaken a checker to make a cert pass.
- Every new certificate feature gets corruption tests that MUST
  fail.
- `make` stays green; axiom footprint stays
  `functional_extensionality_dep` only (check with
  `Print Assumptions`).
