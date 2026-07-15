# Next session: start here

State as of 2026-07-15 (branch `claude/easy-machines-bb5-strategy-8pz2fn`).
This session built Scope B's skeleton end-to-end: the BB5-style TNF
census over the full (4,2) space, refounded on quasihalting, with the
generic tiers verified and measured.  The queue-emptying computation
is the only piece that may still be running/landing (see "The big
compute" below).

## Scoreboard

- **The census machinery is verified and compiles**
  (`theories/Census/`): TNF tree + SearchQueue with a quasihalting
  node invariant, the don't-care completion lemma, swap/mirror orbit
  transfer, the verified decider pipeline, and
  `census_from_empty : Nat.iter n q_suc q_0 = ([],[]) ->
   forall tm, QHBound 2000 tm \/ Deferred D_census tm`.
- **Measured over all 3,995,005 TNF nodes** (tools/census_ladder.c,
  gas 512, both A0=0RB/1RB subtrees, no cnt=1 pruning):
  halt 249,692 (max halting step 107 = BB(4), champion reproduced) /
  in-place cycles 1,029,749 (incl. 399,512 QH with exact scores) /
  translated cycles 2,286,534 (incl. 810,873 QH) /
  n-gram CPS ladder 196,595 / holdouts reached 3,708 of 3,713
  (the other 5 are ngram-easy and already have Bulk theorems here) /
  residue 228,726.
- **Deferred list** `D_census` = 3,713 holdouts + 228,726 residue =
  232,439 machines (generated tables `Census/Deferred_*.v`).
- Previous sessions' 3,136 holdout theorems stand unchanged.

## What was built this session

1. `tools/census_ladder.c` — the measurement harness
   (NEXT_SESSION's "first move"): enumerates the exact tree the Coq
   census walks and runs the QH tier ladder.  Validations: BB(4)=107
   with the right champion; 3,708/3,713 holdouts reached as leaves
   (tree normalization confirmed); the 5 ngram-killed holdouts match
   existing Bulk_011/019/021/024/035 theorems.
2. `theories/Census/TNF_QH.v` — the Coq-BB5 port, quasihalting
   contract: `QHBound B tm` (every eventually-quiet state's last
   visit < B) replaces `HaltTimeUpperBound`; `Deferred D` is the
   swap/mirror/completion orbit of an explicit list; `NodeDecided`,
   `node_expand_spec` (unused-state pointer + swap argument),
   `SearchQueue_*` specs.  KEY DIFFERENCES from the halting census,
   both forced (SCOPING §7): no cnt=1 pruning (full machines are
   enumerated and decided), and leaves discharge by trace equality of
   completions (`qhbound_le`,`nonhalt_le` = the don't-care lemma).
3. `theories/Census/Decide.v` — the pipeline: verified `find_halt`,
   `cycle_leaf_check`/`tcycler_leaf_check` (NonHalt + QHBound n1 via
   the lap induction, reusing `tcycler_laps/_fold`), untrusted
   searches (rolling-hash in-place scan; record-pair TC candidates,
   2/side, left side via `mirror_tm` on the same record log),
   deferred lookup through a `PositiveMap` of `tm_enc` keys (map
   stores the machine, one `tm_eqb` per hit — no injectivity proof
   needed), `decide_easy` + `decide_easy_WF`.
4. `theories/Census/Deferred_Defs.v` + generated `Deferred_00..07.v`
   + `Deferred_Data.v` (`tools/gen_deferred.py`).
5. `theories/Census/Run.v` — root + mirror symmetrization (the 4
   first-move-left children covered by `node_decided_mirror`),
   `q_iter_WF`, `census_from_empty`.
6. `theories/Tests/Census_Corruption.v` — negative controls: tampered
   cycle/TC parameters rejected, ngram must reject a quasihalter and
   a halting machine, deferred lookup misses, pipeline classification
   on knowns.

## The big compute (finish this first)

STATUS at session end: the pipeline is VALIDATED -- the 64k-pop probe
returns `(32, 0, [])` (zero Unknowns; earlier probes caught a
false-record bug in `scan_records0`, fixed by reading the move
direction off the transition).  The four per-subtree walks
(`Run_Split.v` / `q_sub`) were LAUNCHED in parallel at session end,
logging to `census_probes/sub_{0RA,1RA,0RB,1RB}.log` (gitignored);
each should print `sub_probe_X = (0, 0, [])`.  Measured pace: ~6.8
ms/pop native => ~5.9 h for the 1RB subtree, ~1.6 h for 0RB, seconds
for 0RA/1RA.

When the logs show (0, 0, []) for all four:

1. `theories/Census/Census_Compute_Split.v` is ready as written --
   compile it (each Qed replays its subtree through the kernel's
   native conversion, so budget the same hours again; split the four
   lemmas into four files for parallel make if desired).
2. `Print Assumptions census_decided` must show only
   functional_extensionality_dep.
3. Add Census_Compute_Split.v to _CoqProject (or keep it a manual
   `make census`-style target) and update this file.

If a log shows leftovers instead: decode the printed tm_enc keys
with `tools/dec_tm_enc.py`, classify them with
`tools/census_ladder.c --machines`, fix the tier divergence or add
them to the residue file, regenerate Deferred_*, recompile, relaunch
(this loop converged after one iteration this session -- the
false-record fix).

Environment: coq-native lives in the opam switch `census`
(`OPAMROOT=/root/.opam`, `eval $(opam env --switch=census)`); apt's
coqc has no native_compute.  Everything compiles under Coq 8.18.
The probe .v files are one-liners over `Run_Split.q_sub`; see
`census_probes/` logs for the exact form used.

## Then: shrink the deferred list (the measured path)

The 228k residue exists because plain-acyclicity ranks
(`compute_ranks`) are the only liveness rule in the generic n-gram
tier.  Measured on a 300-sample of the residue: **the rank rules
(a)/(b) with just the three count-of-1 measures kill 85.7% at n=3,
t<=1024** (bulk_prover.py `decide(m, n, {})`), 88.7% with the full
pattern vocabulary; of the rest, ~1/5 are QH-with-long-transient
machines, the rest RepWL/irules-class.  So:

1. **Implement the rank-rule search in-Coq** (untrusted, feeding the
   existing verified lex checkers -- exactly the NEXT_SESSION "kill
   the tables" item, now doubly motivated): D shrinks ~24k + holdouts.
2. The remaining ~24k join the holdouts as the census-hard tail and
   fall to the existing roadmap (rwlrank/fuel/drift/irules checkers).
3. Wrap-QH-style transient quasihalters need a QH-classification tier
   (cycle_check_qh/tcycler_check_qh already exist and are wired-ready;
   the pipeline currently returns R_Leaf without classifying).

## Gotchas discovered (do not re-learn these)

- **BB5's cnt=1 pruning is unsound for quasihalting** -- full machines
  can still quasihalt.  The tree expands them; the C tool counts
  3,995,005 nodes vs BB4's 858,909.
- **Coq list literals**: >~5k elements per Definition stack-overflow
  the parser and typecheck superlinearly; the deferred tables use
  500-row sub-definitions + concat.  ~30s-4min per 1.1MB file is
  normal with the native compiler on.
- **`simpl`/`cbn` vs the pipeline**: never let simpl touch `decider`
  applications (it contains a 232k-entry map); root lemmas
  use a hand-built `q_0` and `node_expand_spec` directly, plus
  `cbn [explicit constants]` (include `t_head`! an unreduced
  `t_head {|...|}` blocks rewrites).
- **`Section` hypotheses capture per-lemma**: swap lemmas take
  explicit `u <> StA` args now; don't guess closed signatures.
- **In-place scan keys must be padding-blind** (ceqb ignores blank
  padding): the rolling hash tracks 1-cells relative to the head;
  side LENGTHS are not invariant.
- `repeat split` proves `forall`-wrapped equalities by constructor --
  count your goals.
- The BBB enumerator's A0->xxA exclusion is unnecessary here: 0RA is
  an in-place cycle at (0,1), 1RA a translated cycle at (1,1); both
  die in the loop tier.

## Hard rules (unchanged)

- Everything emitted by tools/ is UNTRUSTED; only the Coq checkers
  carry soundness.  Never weaken a checker to make a cert pass.
- Every new certificate feature gets corruption tests that MUST fail.
- `make` stays green; axiom footprint stays
  `functional_extensionality_dep` only (check with
  `Print Assumptions`).
