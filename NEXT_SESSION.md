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
- **Deferred list** `D_census` = 3,713 holdouts + 52,326 residue =
  56,039 machines (generated tables `Census/Deferred_*.v`; the rank
  tier shrank the raw 228,726 tier residue by 77.1%).
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

STATUS: the v1 pipeline (no rank tier, D = 232,439) was validated at
zero Unknowns over 64k pops (earlier probes caught a false-record
bug in `scan_records0`, fixed by reading the move direction off the
transition; the 0RA/1RA subtrees closed `(0,0,[])`).  The session
then moved to v2 (rank tier + D = 56,039) rather than paying the v1
Qed: re-validate with the same 64k-pop probe (expect `(32, 0, [])`),
then launch the four per-subtree walks (`Run_Split.v` / `q_sub`)
logging to `census_probes/sub_{0RA,1RA,0RB,1RB}.log` (gitignored);
each should print `sub_probe_X = (0, 0, [])`.  v1 pace: ~6.8 ms/pop
native => ~5.9 h for the 1RB subtree, ~1.6 h for 0RB, seconds for
0RA/1RA; v2 adds the rank tier's cost on ngram-failing machines.

The certification layer is the generated
`theories/Census/Compute/` directory (tools/gen_gsplit.py): 24
per-grandchild Qed files (the two xRB subtrees split at B0 into 12
each, composed by Run_Split.child_from_grandchildren) compiled in
parallel, plus Census_Theorem.v assembling

    census_decided : forall tm, QHBound B_census tm \/ Deferred D_census tm

`Print Assumptions census_decided` must show only
functional_extensionality_dep.  The fleet was LAUNCHED at session
end (logs census_probes/G_*.log, progress qed_progress.txt); when
all 24 are OK, compile Census_Theorem.v (seconds for the two leaf
subtrees + assembly).

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

## The rank tier (BUILT this session) and what remains

`Census/RankSearch.v` implements the rules-(a)/(b) search in-Coq
(untrusted: SCC decomposition, condensation ranks, Bellman-Ford
potentials over the three count-of-1s measures) feeding the EXISTING
verified `ngram_check_neverqh_lex`; wired as the pipeline's last
tier (rungs n=3, t in {0,64,256,1024}).  Validated per-machine
against bulk_prover.py -- which surfaced a real overclaim in the
PYTHON side: `bulk_prover.decide` demands liveness only for states
present in the closure, so machines whose quiet states vanish from
it (visited once, never again -- genuine quasihalters like
`1RB---_1LC1LD_1RB1LD_1LC0LC`) were wrongly "killed".  The Coq
checker requires prefix-visited states too and rejects; the v2
deferred sweep (`tools/sweep_rank_residue.py`, `decide_strict`)
mirrors the checker's exact premise.

Measured on the full 228,726 residue: **rank kills 176,400
(77.1%)**; the loose rate was ~86.6%, so ~21.7k of the remainder are
prefix-quiet QUASIHALTERS (wrap-class).  v2 deferred list D_census =
3,713 holdouts + 52,326 residue = **56,039 machines**.

## Next session: shrink the deferred list (52,326 residue + holdouts)

Work items in measured coverage-per-effort order.  The loop for each
tier is mechanized: add the tier to `decide_easy` + its WF case,
mirror it in the residue sweep tool, regenerate `Deferred_*`
(`tools/gen_deferred.py`; the current residue = the committed
Deferred rows minus the holdout list, or re-derive with
census_ladder + the sweep), re-validate with the 64k-pop probe
(expect `(32, 0, [])`), then `make census` (~2-3 h wall at the
grandchild split).  Batch tiers into ONE regeneration + one
certification.

1. **Wrap tier -- MEASURED: 20,568 of the 52,326 residue (39%) are
   prefix-quiet quasihalters** (`tools/sweep_wrap_residue.py`;
   confirms the ~21.7k estimate).  Each is a genuine quasihalter with
   a Coq-checked `NonHalt /\ QuietAfter q s /\ QuasiHaltsSt` via the
   EXISTING verified `ngram_check_quiet` (Wrap.v) -- validated on 414
   random machines through `vm_compute`, 0 failures, and
   `tools/gen_residue_wrap.py` regenerates the theorems from
   `tools/wrap_residue_caught.tsv` (`theories/Tests/Residue_Wrap_Probe.v`
   is a committed 120-machine sample).  **The 31,758 survivors
   (`tools/wrap_residue_survivors.txt`) are the residue's hard never-QH
   core -- the meat.**
   **The QHBound tier is now BUILT and verified** (`ngram_check_qhbound`
   / `ngram_check_qhbound_sound` in `Checkers/Wrap.v`, axiom footprint
   `functional_extensionality_dep`): the wrapped closure PLUS the
   engine's plain-acyclicity rank liveness (`Closure.live_ok` /
   `rank_reach` / `live_appears_recur`, added to `Closure.v`) gives the
   full census decision `NonHalt /\ QHBound (S t) /\ QuasiHaltsSt`.
   Measured (`tools/sweep_qhbound_residue.py`): the plain-acyclicity
   gate decides **~24% of the 20,568** wrap machines now (`n<=6`);
   `theories/Tests/QHB_Probe.v` verifies 150 through `vm_compute`.
   **The lex-gated variant is ALSO built** (`ngram_check_qhbound_lex`
   + `_sound`; `Closure.v` gains `lex_reach` / `closure_invariant_c` /
   `live_lex_ok` / `live_appears_recur_lex`): each appearing state is
   discharged by plain acyclicity OR an `NgRankE`/`NgPattE` measure
   certificate over the wrapped closure.  Tools:
   `tools/gen_qhbound_wrap.py` (plain, from `qhbound_caught.tsv`),
   `tools/gen_qhbound_lex.py` (lex, from `qhbound_survivors`);
   committed probes `Tests/QHB_Probe.v` (150 plain) and
   `Tests/QHB_Lex_Probe.v` (lex-only machines).
   **FULL MEASUREMENT (committed artifacts): of the 20,568 wrap-QH
   machines, 5,307 are QHBound-decidable by the plain gate NOW
   (`tools/qhbound_caught.tsv`; a 100-machine RANDOM sample verified
   through Coq, 0 failures) and 15,261 need the measure gate
   (`tools/qhbound_survivors.txt`; a small-sample lex sweep with just
   the count-of-1s measures lifts ~13% -- offer the digram/pattern
   candidates as `Bulk_R` did to push further).**
   REMAINING:
   (a) run gen_qhbound_wrap over the full `tools/qhbound_caught.tsv`
   and check the tables in as `Machines/Bulk/QHBWrap_*.v` (~90 files
   at 60/file; each compiles in seconds);
   (b) strengthen the lex sweep (pattern vocabulary, larger n) over
   `tools/qhbound_survivors.txt` and emit via gen_qhbound_lex;
   (c) wire `ngram_check_qhbound(_lex)_sound` into the census
   `decide_easy` as an `R_QH` tier, regenerate `Deferred_*` over what
   remains, and re-`make census` (needs the native switch).
2. **Pattern-vocabulary rank (cheap add-on, ~3-6k):** generalize
   RankSearch's candidate measures from the three `ngmeas` counts to
   the `NgPattE` pattern measures (pm_delta is verified; the search
   loop is measure-agnostic -- add candidate enumeration with
   `pm_ok` coverage limits) and add n=4 rungs.  Mirror in
   sweep_rank_residue (bulk_prover already speaks patterns).
3. **RepWL tier (the remaining ~25-30k are mostly this class):**
   port Coq-BB5's `Decider_RepWL.v` closure construction as a second
   instance of the `Closure.v` engine (SCOPING phase 2's rwl block),
   plain-acyclicity liveness first (the engine's `compute_ranks`
   works for any instance), rwlrank measures later.  This is the
   biggest single block and also the prerequisite for the 106
   rwlrank holdout certs.
4. **Holdout absorption** (independent track): upstream is down to
   ONE open machine (`1RB0RB_1LC1RC_0RA1LD_1RC0LD`, the residue-3
   nested/mixed tower; `check_coverage.py`, 2026-07-16).  The
   checker gaps that absorb the remaining certificate types: irules
   (352), rwlrank (106 incl. 9 rwlrank+wrapngram), fuel (62), drift
   (17), and ~42 counter machines (the BBB residue-3 sprint boarded
   many more counters than the old 22) -- SCOPING phases 2b-5.
   **The fuel checker (rule c2) is now BUILT and verified**, axiom
   footprint `functional_extensionality_dep`:
   - `theories/Records.v` -- record/extent substrate (side windows,
     growth <=1/step, toward-move shrinks, `run_right_exhausts`).
   - `theories/Closure.v` -- `runner_find` (the record argument as a
     per-state liveness lemma) + `closure_check_neverqh_fuel`
     (`lex_ok || runner_ok` per visited state) + soundness.
   - `theories/Checkers/FuelClass.v` -- capped sided-count lower-bound
     classes with `finc_sound`/`fdec_sound` (the beyond-window
     upgrade's delta core).
   - `theories/Checkers/Fuel.v` -- `ngram_check_neverqh_fuel` on the
     n-gram abstraction (reuses the full measure vocabulary; runner
     fuel read from the window), `Tests/Fuel_Examples.v` validates it
     end-to-end (subsumes the lex checker on a real bulk machine).
   REMAINING to land the 62 machines: the untrusted prover must emit
   runner-mode certs -- adapt `tools/bulk_prover.py` to detect the
   runner SCCs (states the rank measures leave undischarged, whose
   nodes all move one direction with in-window fuel), emit them as
   the runner-gated states, and `tools/gen_bulk_certs.py` to write
   `apply (ngram_check_neverqh_fuel_sound ...)`.  For beyond-window
   fuel machines, swap `cconf` for the `cconf * fclass * fclass`
   refined context (FuelClass) and read `rfuel_ge1` off the tracked
   class; the Closure-side soundness path is unchanged.  Then rule
   (c3) drift rides the same substrate (+17).  Each holdout theorem
   also lets its machine leave the deferred list
   at the NEXT regeneration (deferred entries with Coq theorems can
   be dropped once a "proven machines" tier exists -- a
   PositiveMap of the Bulk/Wrap theorem machines returning
   R_NeverQH/R_QH, trivially WF from the existing per-machine
   theorems).

Nothing from the certification run itself needs checking in beyond
what is committed: the G_*.vo/logs are gitignored artifacts
(re-derivable by `make census`), and the residue list is recoverable
from the committed Deferred tables minus the holdout file.

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

---

# Counters track (individual proofs) -- session 2026-07-16

State of the SCOPING section 5 phase 5 "individual proofs" track
(branch `claude/coq-bbb4-counter-proofs-3yx9bj`).  Own files only:
`theories/Counters/`, `theories/Machines/Counters/`,
`theories/Tests/Counters_Corruption.v`, `tools/counters*`; the
`_CoqProject` block is marked `# --- counters track ---`.

## Boarded: 6 of 39 counter machines

| family | status |
|---|---|
| mono_counter (3) | **COMPLETE**: #10, #26, #31 (`Mono_10/26/31.v`) |
| spacer_counter (3) | **COMPLETE**: #16, #22, #23 (`Spacer_16/22/23.v`) |
| gray(1) double(4) blockdbl(3) mono2(2) interleave(2) exp(3) bounce(2) | not started, in that order (bounce needs the well-founded measure -- see its family notes upstream) |
| wave(6) wave4(1) tower(4) xd(3) fractal(2) | hard tail, budget separately |

Every theorem is `nqh_<bbchallenge text> : NeverQuasiHaltsSt tm_*`,
`Print Assumptions` = `functional_extensionality_dep` only, listed in
`tools/counters_manifest.tsv` (wired into `check_coverage.py`;
coverage now 3142/3713).

## The architecture that landed (native route -- decided over busycoq)

- `theories/Counters/WTape.v`: two-sided windowed runs (`wsteps`
  with per-side wall/blank-materialize modes), the transport lemma
  into `csteps`, repetition cycles `cycR`/`cycL`/`cycLW` (the last
  carries a fixed marker window -- spacer transcription), and the
  `rep` algebra (`rep_shift`, `rep_rot`, `rep_slide`, `rep_dbl`,
  `rep_add`).
- `theories/Counters/LapGlue.v`: `glue_neverqh` -- bootstrap +
  per-anchor lap (up to `lift`, for the overflow trailing blank) +
  per-anchor all-state visit witnesses => `NeverQuasiHaltsSt`.
- `theories/Counters/MonoCounter.v`: counter encodings over
  `positive` (`Wp` odd-cell, `Bp` contiguous), the carry view
  `cview` with decomposition lemmas for both encodings, and the
  mono-family comb-alignment/final-area rewrites.
- Per machine: ~15 unit runs (each `Proof. reflexivity. Qed.` on
  `wsteps`), transported phase lemmas in cons-normal form, and a
  linear `eapply csteps_chain` lap script with `rep`-algebra
  junction rewrites, split by `cview` case (interior carry j /
  overflow 2^j-1).

busycoq route rejected after the #10 prototype: it would add the
stream-world port PLUS a new quasihalting-aware translation (a fresh
trust surface) and the carry case analysis stays manual either way;
our unit runs are one-line reflexivity checks, so busycoq's Ltac
advantage evaporates.

## The per-machine recipe (tools/counters/, ~2-4h per machine)

1. `trace.py` the lap macro-structure (sweeps, turnarounds);
2. write `lapNN.py` against `executor.py` (combinators mirror the
   Coq lemmas 1:1; wall discipline asserted; units auto-derived);
3. `python3 lapNN.py 300` must print ALL OK (differential vs raw:
   step counts + configs + next-anchor, all carry shapes);
4. transcribe: unit dump -> unit lemmas; chain -> lap script; small
   probes give the bootstrap step count and visit offsets;
5. corruption tests (mutant machine breaks a unit, wall-discipline
   `= None` checks, wrong boot anchor `ceqb = false`);
6. manifest row + `_CoqProject` line + `make` + `Print Assumptions`.

## Next machine: #19 gray_counter (results/counter19.cert)

The only gray machine; read its cert + `verify_gray_counter` in
BBB/src/verify.c for the encoding, then run the recipe.  After it:
double_counter (#30 + 3 more per check_coverage), blockdbl, mono2,
interleave, exp, bounce (well-founded measure -- LapGlue may need a
second closer whose laps shrink a secondary quantity; design against
the C verifier's bounce obligations before coding).

Session-2 notes on the spacer twins (#22/#23, voff=-1): p0 = 1, the
lap runs from every positive (`Pos2Nat.is_pos` + one destruct level
instead of two); #23's separator rebuild is 8 steps exiting through
D and deposits its own spacer zero, so its final fold ends
`rewrite HBs, rep_slide` where #16/#22 use the [1]-shuttle +
`rep_add` fusion.  The twins CONVERGE after 8 steps -- a corruption
example claiming their 8-step runs differ is false (learned the
hard way); discriminate them at 7 steps.

## Trap catalog (do not re-learn)

- **Comb units are rotations**: the crossing consumes `[1;0;1]`
  even though the comb is written `(110)^a` -- pick the boundary
  where the 5-step excursion stays inside the unit and prove the
  `rot_*` fold by 3-line induction (`induction k; cbn [rep app];
  now rewrite IHk`).
- **Overflow laps may end one trailing blank long** (mono) or
  exactly (spacer #16): state the lap up to `lift` and use
  `lift_app_blank` only where the executor says so.
- **Evars vs case analysis**: `destruct j` must happen BEFORE
  `do 2 eexists` when the two carry branches produce different
  final configurations (Mono_31 lesson).
- **`cbn [rep app]` over-unfolds**: it will expand EVERY
  S-headed `rep` in the goal, wrecking later pattern matches; use
  definitional fold lemmas (`Proof. reflexivity. Qed.`) as targeted
  rewrites instead (`spacer_fold`, `ones_fold`, ... in Spacer_16).
- **`rewrite` needs app-forms**: a bare `rep [S1] j` tail won't
  match `... ++ X` patterns -- keep `_nil` fold variants around.
- **Anchor conventions**: the executor's `raw_lap` event detector
  IS the spec of `Cc` -- keep them in lockstep or the differential
  test lies to you.
- Step-count formulas are never needed in Coq (the lap `n` is an
  existential); do not waste time deriving them beyond executor
  sanity checks.
