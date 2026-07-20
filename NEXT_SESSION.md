# Next session: start here

State as of 2026-07-16 (branch `claude/easy-machines-bb5-strategy-8pz2fn`).
**THE CENSUS IS CERTIFIED**: `Census_Theorem.census_decided :
forall tm, QHBound B_census tm \/ Deferred D_census tm` is Qed through
the kernel, `Print Assumptions` = `functional_extensionality_dep`
only.  Scope B stands end-to-end: the BB5-style TNF census over the
full (4,2) space, refounded on quasihalting, generic tiers verified,
computation certified (see "The big compute" below for the layer
layout).  In parallel the holdout-porting session built + verified
the wrap/QHBound tiers and measured them over the census residue
(item 1 of the shrink plan below) -- the next census regeneration can
drop the 20,568 wrap-caught machines from `D_census`.

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

## The big compute (DONE -- certified 2026-07-16)

`census_decided` is Qed with the expected axiom footprint.  The
certification layer under `theories/Census/Compute/`:

- 24 per-grandchild Qed files `G_*.v` (tools/gen_gsplit.py; the two
  xRB subtrees split at B0 into 12 each, composed by
  `Run_Split.child_from_grandchildren`), each Qed one native queue
  walk (`Nat.iter 700 q_suc ... = ([],[])`).
- The A0=1RB, B0=1LC grandchild is the largest single walk (>2.5 h;
  it outlived the remote container's reclaim window repeatedly), so
  it is split ONCE MORE: `Census/Run_Split2.v` expands its machine at
  the undefined C1 slot (index 2, pointer StD, all 16 fills
  admissible) and `tools/gen_ggsplit.py` emits the 16 `GG_1LC_*.v`
  walk units plus the assembling `G_1RB_1LC.v` (same lemma names as
  the monolithic version, so Census_Theorem.v is untouched).  Every
  unit lands in <= ~10 min, making certification robust to compute
  interruptions.
- `make census` drives the whole layer order (Run_Split, Run_Split2,
  GG units, G units, theorem); ~2-3 h wall on 4 cores under the
  native switch.

Re-running from scratch re-derives everything; the per-unit
logs/progress live in `census_probes/` (gitignored).  If a future
regeneration's log shows leftovers: decode the printed tm_enc keys
with `tools/dec_tm_enc.py`, classify with `tools/census_ladder.c
--machines`, fix the tier divergence or extend the residue, and
regenerate (this loop converged after one iteration -- the
false-record fix in `scan_records0`).

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

## Counters track, session A (2026-07-16): gray + mono2 boarded

(Marked append; supersedes the table above.)  Boarded: **9 of 39**.

| family | status |
|---|---|
| mono_counter (3) | COMPLETE: #10, #26, #31 |
| spacer_counter (3) | COMPLETE: #16, #22, #23 |
| gray_counter (1) | **COMPLETE: #19 (`Gray_19.v`)** |
| mono2_counter (2) | **COMPLETE: #38, #39 (`Mono2_38/39.v`)** |
| double(4) blockdbl(3) interleave(2) exp(3) bounce(2) | not started; session A scoped double+blockdbl, session B interleave/exp/bounce |
| wave(6) wave4(1) tower(4) xd(3) fractal(2) | hard tail, budget separately |

Coverage after this session: 3145/3713.  All three new theorems are
`nqh_<text>` with `Print Assumptions` = `functional_extensionality_dep`
only; negative controls live in `theories/Tests/CountersA_Corruption.v`
(new file, session A's own -- session B uses its own test file).

### What landed (all in the MonoCounter session-A appendix)

- Gray encoding `Wg` (3-cell slots of G(p) = p xor p>>1): the increment
  flips slot j = fst (cview p), so `Wg_some`/`Wg_none` follow the
  `cview_some_W` pattern verbatim.  #19's lap: FIVE flows (even
  set/clear, interior set/clear, overflow), one turnaround each.
- Interleaved-marker encoding `Wm2` (mono2): `Wm2_some/none`, again
  same skeleton.  #39 = one sweep/lap, #38 = two sweeps/lap (comb_step
  2); the twins share A/B/D rows, so their unit tables coincide up to
  the C-row units.
- New rep algebra: `rep_dblu`, `rep_trip`, `rep_snoc2/3`, `rot_cross2/3`,
  `rot_ret`, `ones2_slide`, `cross_ret/cross_ret2`, `comb_even/odd`,
  `comb_refold`, and definitional `rep011/101/110_expose` (targeted
  substitutes for `cbn [rep]`, per the over-unfolding trap).

### New traps (session A)

- **rewrite needs concrete rotations**: `rep_rot`'s `u ++ [x]` pattern
  never matches literal `rep [S0;S1] j` -- state the machine's exact
  rotation as its own induction lemma (`rot_ret` etc.), 3 lines each.
- **Evars vs side conditions**: in `split; [| split; [| lia]]` the
  `lia`/`reflexivity` fire BEFORE the csteps chain instantiates the
  evars -- prove the chain first, side goals after (Mono_10 bullet
  order, not inline brackets).
- **`destruct (cview p) eqn:` rewrites the IH too**: apply the IH via
  `eq_refl` (the file's established `cview_some_W` pattern), not via
  the destructed hypothesis.
- `injection` recurses through `S` -- `(S j', o) = (S j, Some q)`
  yields `j' = j` directly; a second injection is "Nothing to inject".
- Head-exposure hypotheses (`Wm2_head q = S1 :: wq`): rewrite them
  globally BEFORE starting the chain; mid-chain `rewrite <- Hwq`
  fails once deposits shadow the head.

### Doubling families (double #9/#30/#32/#37, blockdbl #11/#13/#28):
### reconnaissance done, NOT started -- read before coding

`tools/counters/trace_dbl.py` probes all seven: synthetic anchors are
validated (each reaches the next anchor with the cert recurrences).
Anchor cconfs (head-side per cert `acc_side`):

- #30: `(B, 1^t ++ (011)^k-rev ++ [0;1], 0, [])`, k=2^j-1, t=3j+4;
- #9:  gen comb (10), no prefix, kg=2^j-1, acc 3j (unary, side R);
- #32: gen comb (110), prefix 1, kg=2^j, spacer-acc 0^(3+2j) then 1;
- #37: side L (acc left), legacy comb, t=1+3j;
- #11/#13: solid 1^m 0 1^t, m=3*2^(j-1)+{1,0}, t=2j-1;
- #28: side L, 1 0^z 1^m, m=4*2^(j-1)-1, z=2j.

These laps are O(k^2): a NESTED loop of per-unit mini-sweeps (#30
j=2,3,4: 431/1447/5207 steps).  The toolkit handles every inner phase
(the #30 wiggle-clear is a textbook `cycLW` unit
`(B,([1;1],1,[])) -> (B,([1],1,[0]))`, collapse/spread are 3-step
cycL/cycR with u=[1;1;0], w=[1;0;1] and back), BUT:

- the OUTER loop needs a new closer: `creach tm c c' := exists n,
  csteps tm n c = Some c'` with refl/trans/csteps lemmas and
  `creach_iter : (forall i, i < k -> creach (f i) (f (S i))) ->
  creach (f 0) (f k)`; the lap lemma then chains boundary phases
  around `creach_iter` and recovers `0 < n` from a nonempty prefix
  phase.  The mid-config family `f i` must be read off the executor,
  not derived by hand: my hand-derived #30 step model was 2x short --
  the acc is re-shuttled EVERY mini-lap (the per-lap fill triples are
  re-cleared by the next wiggle), so wiggle counts grow ~3/lap.
- the executor needs a `cycLW` combinator (lap16.py inlined one
  manually; a reusable `cycLW(ex, cfg, lwlen, ulen, P, k, name)`
  helper that mirrors `WTape.cycLW` -- unit `(q,(lw++u,h,[])) ->
  (q,(lw,h,w))` -- was drafted and works; put it in executor.py or
  per-lap files).
- derive the mini-lap phase list with a DbgExec subclass that prints
  the cfg after every combinator (see the mono2 session: two dumps at
  consecutive j pin down every list shape and count).

**Next machine: #30** (canonical double_counter).  Known #30 phase
inventory (validated against the raw trace, counts NOT yet final):
`UTe (B,([],0,[]))->3,br=F->(B,([1],1,[1]))` edge turn block;
wiggle `cycLW` as above (mini-lap 1 clears the whole acc, t reps);
junction `UJ (B,([1;0],1,[]))->2->(D,([],0,[1;0]))`;
collapse `UC (D,([1;1;0],0,[]))->3->(D,([],0,[1;0;1]))` + an edge
variant eating into the old prefix; prefix turns `UP` (3 steps
mini-lap 1, 4-5 steps steady, shapes differ); spread
`US (B,([],0,[1;1;0]))->3->(B,([1;0;1],0,[]))`; per-lap fill triples
`(B0 w1, C0 w1, D1 keep)` = cycR u=[0;1;0]-ish, and a final fill
pass ending in a br=F edge unit.  Seeds: each mini-lap's UJ keeps a
1 (spaced 3), UTe's third 1 is the top seed.  After #30: #9 (gen
comb (10), fewest turns/lap: 2 per mini-lap), then #37, #32, then
blockdbl #13/#11 (solid blocks, (B1,D1)-conversion cycles), #28
(side L).  Budget one machine per ~2-3h; the creach scaffolding is
shared after the first.
---

# Counters track, session B (interleave/exp/bounce) -- 2026-07-16

Parallel to session A (gray/double/blockdbl/mono2), own files only:
`theories/Counters/{ILCounter,ExpCounter,BounceCounter,MeasureGlue}.v`,
`theories/Machines/Counters/{Interleave_18,Interleave_35,Exp_2,Exp_4,
Exp_12,Bounce_8,Bounce_33}.v`, `theories/Tests/CountersB_Corruption.v`,
`tools/counters/lap{18,35,2,4,12,8,33}.py`; the `_CoqProject` block is
marked `# --- counters track: session B ---`.

## Boarded: 7 machines (16 of 39 total with session A's 9 -- see its section above)

| family | status |
|---|---|
| interleave_counter (2) | **COMPLETE**: #18, #35 (`Interleave_18/35.v`) |
| exp_counter (3) | **COMPLETE**: #2, #4, #12 (`Exp_2/4/12.v`) |
| bounce_counter (2) | **COMPLETE**: #8, #33 (`Bounce_8/33.v`, via MeasureGlue) |

All `nqh_<bbchallenge text> : NeverQuasiHaltsSt`, `Print Assumptions`
= `functional_extensionality_dep` only, manifest rows appended.

## What was built

- `ILCounter.v`: the interleaved counter encoding `Ip` (rev of E(n),
  LSB-first, one `S1` pad per bit), cview decomposition lemmas, and
  `pair_fold`.  #18/#35 share the anchor
  `D(n) = E(n) (110)^(2n) 1` and a two-sweep lap through the mid
  shape `E(n+1) 010 (110)^(2n) 1`; the increment carries on sweep 1,
  sweep 2 rewrites `010` locally.  Laps end exactly (no lift slack).
- `ExpCounter.v`: the stride-3 marker encodings -- zeros-first `Tp`
  and marker-first `Gp` -- with cview lemmas emitting the exact
  `rep`-block shapes the stride cycles and zeroing runs consume, plus
  `rep1_fold`/`ones_fold_S`/`rep_tpl`.  #2 (side R, moff 1: the two
  sides carry on ALTERNATE laps -- case over both cview's), #4
  (side L, moff 0: one cview drives both sides), #12 (sym: markers
  both sides).
- `MeasureGlue.v` -- THE NEW CLOSER (bounce): `mrun` composes a
  measure-decreasing abstract recurrence of EXACT micro laps
  (invariant-guarded; terminal up to lift) into one csteps run by
  strong induction on the measure.  The macro family then steps
  p -> succ p and plain LapGlue closes never-QH: unboundedness from
  the macro index, per-lap finiteness from the measure.
- `BounceCounter.v`: digit words `Dw` (00/11 pairs), carry view
  `bview`, measure `cval` (value of the complement, LSB-first;
  `cval_step`: each increment decrements it by EXACTLY 1),
  comb rotations `comb_rot0/1`, run folds.
- `Bounce_8/33.v`: macro anchors `D(k) = 1^m 0^z`; macro lap =
  boot-in half sweep + `mrun` over the double-sweeps + terminal
  settle from the all-ones word.  KEY DISCOVERY: the double-sweep is
  a CELL-UNIFORM binary increment
  `Sc a (1^j 0 x) -> Sc (a+1) (0^j 1 x)` -- the C verifier's
  interior/overflow split is pure decode (the flipped top digit
  merges with the accumulator AS CELLS), so a fixed-length bool word
  carries the whole macro lap with no case analysis, and the
  invariant is just the conservation law
  `S (fst x) + cval (snd x) = const(k)`.  Validated k=2..9 (#8, 510
  double-sweeps) and k=2..8 (#33) against raw.

## Trap catalog additions (session B)

- **The `apply`-unification unfolds double-`S` reps**: `apply phU1`
  against `S1 :: rep u (S (S a)) ++ X` leaves the residual evar in a
  half-unfolded `fix`-form that later `rewrite`s can't match.  Insert
  an explicit `change` exposing the cons cells
  (`S1 :: S0 :: S1 :: rep u (S a) ++ X`) BEFORE the apply; folds like
  `ones_fold3` also want their explicit instance (`rewrite
  (ones_fold3 a)`).
- **`rewrite <- rep_dbl` is ambiguous** when both `rep [S0] (2*t)`
  and `rep [S1] (2*P)` are present -- give the instance explicitly.
- **exp #2's two sides carry on alternate laps** (moff 1): destruct
  BOTH `cview p` and `cview (Pos.succ p)`; the impossible
  overflow+overflow branch still closes (the algebra composes, no
  contradiction needed).
- **Bounce sweep-B entry is comb-rotated**: the collapse absorbs the
  mid marker `0` + first block `1` as one more `[S0;S1]` unit
  (`comb_rot1`); the executor frames catch this automatically.

## Next machine

The counters residue after both sessions: session A's remaining
queue (double(4) starting at #30, then blockdbl(3) -- see its
section above) and then the hard tail wave(6) wave4(1) tower(4)
xd(3) fractal(2).  For the
tail, start with **wave**: read `results/counter*.cert` types `wave_counter`
and `verify_wave_counter` in BBB/src/verify.c; expect LapGlue to
suffice (parameter -> infinity liveness) with wider unit tables.  The
bounce-style MeasureGlue composition is now available for any family
whose macro lap chains an inner counter (tower is the likely
customer: its cert type suggests nested doubling).

<!-- --- irules mass-board --- -->

## IRules mass-board (this session)

Boarded **250** of the 352 irules-typed holdouts:
`theories/Machines/IRules_Batch_00.v` .. `IRules_Batch_08.v`, each
machine = TM + `IRCert` literal + `_never_quasihalts` (via
`irules_check_neverqh_sound`, fuel 300000, `vm_compute`) +
`_nonhalt` corollary.  Manifest: `tools/irules_manifest.tsv` (250
rows), wired into `tools/check_coverage.py`.  Negative controls:
`theories/Tests/IRulesBatch_Corruption.v` (mutant TM -> `false`;
perturbed meta map / wrong anchor -> `<> true`; meta-map control at
fuel 2000 with the genuine cert shown passing at that same fuel,
because a corrupted map burns unbounded memory at fuel 300000).
`Print Assumptions` on 5 sampled theorems across batches:
`functional_extensionality_dep` only.

**Coverage: 3152 -> 3402 Coq-proven (+250).**

### Deferred: 102 machines the v1 Coq engine cannot board

Full list with per-machine reasons: `tools/irules_deferred.tsv`.
None are the anticipated >10M-step-anchor cases -- all 352 anchors
fit the flat checker.  Instead these certs use post-v1 format
features the verified engine does not model:

- 44: v6 certs needing `blk`,`rulepfx` (block-encoded rules)
- 38: v3 certs with decrement delta -2 (v1 supports -1 only)
-  6: v7 certs needing `rulepfx`,`rulerunm`
-  6: v3 certs needing `blk`
-  4: v3 certs with decrement delta -3
-  3: v3, d=-1 only, but v1 bound reasoning fails (probed incl.
  kmin/lb bumps)
-  1: v4 cert needing `mmrow`,`nvar`,`tplrunmv`

Next session: extend the engine (multi-decrement first -- 42
machines for one feature) or port the v6 block-rule layer.
Machine strings:

```
1RB---_0LC0LB_1RC0RD_1LB1LA
1RB---_0RC0RB_1LD0LA_1LD1LB
1RB0LA_0RC0RB_1LC1LD_0RA0RB
1RB0LC_0LC0LB_1RC1RD_1LA0LB
1RB0LC_0LC0LB_1RC1RD_1LA0LD
1RB0LC_1LA0LD_1RC1RB_0LC0LD
1RB0LD_0LC0LB_0LD1LC_1RD1RA
1RB0LD_1LC0LB_0RA0LD_1RD1RB
1RB0LD_1LC0LB_0RA1LC_1RD1RB
1RB0RA_0RC1LD_1LC0LA_0RC0RD
1RB0RA_0RC1LD_1LC0LA_0RD0RB
1RB0RB_0RC1LD_1LC0LD_1RB0RA
1RB0RC_0LC0LB_0LD1LC_1RD1RA
1RB0RC_0RC0RB_1LC1LD_1RA0RB
1RB0RC_0RC1RB_0RD0RC_1LD1LA
1RB0RD_0LC0RC_1LC1LA_0RC0RD
1RB0RD_0RC0RB_1LC0LA_0RA0RB
1RB0RD_0RC0RB_1LC0LA_0RB---
1RB0RD_0RC0RB_1LC0LA_0RD0RB
1RB0RD_0RC0RB_1LC0LA_1RD1LB
1RB0RD_0RC0RC_1LC1LA_0RC0RD
1RB0RD_0RC1LA_1LC0LA_0RA0RB
1RB0RD_0RC1LA_1LC0LA_0RB0RB
1RB0RD_0RC1LA_1LC0LA_0RD0RB
1RB0RD_0RC1LA_1LC0LA_1LA0RB
1RB0RD_0RC1LA_1LC0LA_1RB0RB
1RB0RD_0RC1LD_1LC0LA_0RD0RB
1RB0RD_1LB0RC_1LC1LA_0RC0RD
1RB0RD_1LC0LB_1RA1LC_1LC0LC
1RB0RD_1RC0RB_0LA0RD_1LD1LB
1RB0RD_1RC0RB_0LA1RC_1LD1LB
1RB1LA_0LC0LB_1RC1RD_1LA0LB
1RB1LA_0LC0LB_1RC1RD_1LA0LD
1RB1LA_1LA0LC_0LD0LC_1RD1RB
1RB1LC_0RC0RB_1LD0LA_0RA1LB
1RB1LD_0RC1RB_1LC1LA_0RB0RD
1RB1RA_0RC0RB_1LC1LD_1RA0RB
1RB1RA_0RC0RB_1LD0RA_1LD1LB
1RB1RA_0RC1LD_1LC0LA_0RD0RB
1RB1RB_0LC0LB_0LD1LC_1RD1RA
1RB1RD_0RC0RB_1LC0LA_1LA1LB
1RB1RD_0RC0RB_1LC0LA_1LB---
1RB1RD_0RC0RB_1LC0LA_1LD0RB
1RB1RD_0RC0RD_1LC0LA_0RB1LD
1RB1RD_0RC1LD_1LC0LA_0RD0RB
1RB---_1RC1RA_1LD0RB_1LB0LC
1RB0LC_0LA1RA_1LA0RD_1LD1RC
1RB0LC_1LA1RA_1LA0RD_1LD1RC
1RB0LC_1RC0RA_1LA1LD_1LC---
1RB0LD_0LC1RA_1LC1RD_1LA0RC
1RB0LD_0LC1RD_0RD1LC_1RB1LA
1RB0LD_0LC1RD_1LA1LC_1RB1LA
1RB0LD_0LC1RD_1LD1LC_1RB1LA
1RB0LD_0LC1RD_1RA1LC_1RB1LA
1RB0LD_0LC1RD_1RB1LC_1RB1LA
1RB0LD_0RC1RA_1LC1RD_1LA0RC
1RB0LD_1LC0RA_0LD1LB_1RD1LA
1RB0LD_1LC0RA_0RA0LB_1RD1RC
1RB0LD_1LC0RA_0RB1LB_1RD1LA
1RB0LD_1LC0RA_0RD1LB_1RD1LA
1RB0LD_1LC0RA_1RB1LB_1RD1LA
1RB0LD_1LC0RA_1RD1LB_1RD1LA
1RB0LD_1LC1RA_1LC1RD_1LA0RC
1RB0LD_1LC1RD_0RD1LC_1RB1LA
1RB0LD_1LC1RD_1LA1LC_1RB1LA
1RB0LD_1LC1RD_1LD1LC_1RB1LA
1RB0LD_1LC1RD_1RA1LC_1RB1LA
1RB0LD_1LC1RD_1RB1LC_1RB1LA
1RB0RC_1LC1LD_1RA0LB_1LB---
1RB0RD_1LC1LB_1RD0LB_0RD1RA
1RB1LA_0LA1RC_1RB1LD_1RB0LC
1RB1LA_1LA1RC_1RB1LD_1RB0LC
1RB1LA_1RC0LD_0LA1RD_1RC1LB
1RB1LA_1RC0LD_1LA1RD_1RC1LB
1RB1LB_1LA0RC_1RB0LD_1RD1LC
1RB1LC_0LC1RB_1LA1RD_1LA0RC
1RB1LC_1LA1RB_1LA1RD_1LA0RC
1RB1LC_1RC1RB_1LA1RD_1LA0RC
1RB1LD_0LC1RA_0RA1LC_1RB0LA
1RB1LD_0LC1RA_1LA1LC_1RB0LA
1RB1LD_0LC1RA_1LD1LC_1RB0LA
1RB1LD_0LC1RA_1RB1LC_1RB0LA
1RB1LD_0LC1RA_1RD1LC_1RB0LA
1RB1LD_1LC1RA_0RA1LC_1RB0LA
1RB1LD_1LC1RA_1LA1LC_1RB0LA
1RB1LD_1LC1RA_1LD1LC_1RB0LA
1RB1LD_1LC1RA_1RB1LC_1RB0LA
1RB1LD_1LC1RA_1RD1LC_1RB0LA
1RB1LD_1LC1RB_1LA0RD_1LA1RC
1RB1LD_1RC1RB_1LA0RD_1LA1RC
1RB1RA_0RC0RB_1LC1LD_0RA0LA
1RB1RA_1LC0RB_1LB1LD_0RA1RB
1RB1RA_1LC0RB_1LB1LD_1RA1RB
1RB1RA_1LC0RD_0RA1LD_1LC1RB
1RB1RA_1LC0RD_1RA1LD_1LC1RB
1RB1RA_1LC1RD_0RA1LB_1LC0RB
1RB1RA_1LC1RD_1RA1LB_1LC0RB
1RB1RC_0LA1RB_1LD0RC_1LC1LA
1RB1RC_1RC1RB_1LD0RC_1LC1LA
1RB1RD_1LC0RA_1LA0LB_1RA---
1RB1RD_1LC1RB_1LD1LA_1LC0RD
1RB1RD_1RC1RB_1LD1LA_1LC0RD
```

## Fuel track: DONE (62/62 boarded)

The scoping above was executed in the follow-up session: the class
refinement AND the per-SCC gate both landed as new files
(`Checkers/FuelSCC.v`, `Checkers/FuelWide.v`; Fuel.v / FuelClass.v /
Closure.v untouched), and all 62 `neverqh_fuel` holdouts are proved
(`Machines/Fuel_Batch_{01,02,03}.v`, manifest
`tools/fuel_manifest.tsv`, coverage 3152 -> 3214).  Key design notes
for reuse:

- **The runner rule as a lex disjunct, not a peeling stage.**
  [fscc_edge_ok] = lex-good OR gate-internal-with-every-component-
  non-increasing.  The emitted certificates keep gate edges
  "equal" at every component (rank components are computed over the
  peeling graph PLUS gate edges; rule-(a) components have delta <= 0
  on residue edges by construction; later measure gates never touch
  gate nodes since a gate is a full SCC).  The descent proof then
  needs no peeling-sequence induction: outer well-founded induction
  on the lex tuple, inner induction on the right-window bound.
- **Lower-bound classes suffice.**  The C verifier's exact capped
  counts (with the disjunctive cap split) were not needed: FuelClass
  F0/F1/F2 lower bounds with deterministic finc/fdec transitions
  catch all 62, because the runner SCCs cross only window-blank
  cells (classes constant around the cycles).
- **The refined instance is plumbing, not proofs.**  fw_succs pairs
  the base ng_succs branches with ONE class update read off the
  window; finc_sound/fdec_sound close the covering obligations.
  Anyone adding another context refinement should copy that shape.

Possible next customer of FuelSCC: the 17 `neverqh_drift` holdouts
(rule (c3), net-drift SCCs with fuel on the drift side, verify.c
~4300).  The gate check would swap "every node moves right" for a
per-SCC Bellman-Ford drift certificate; the record argument changes
(records via strictly-positive net displacement instead of monotone
motion), so [runner_find]'s window induction needs a drift variant,
but the FuelSCC edge-gate/descent skeleton and the FuelWide class
plumbing should carry over.

## RepWL session 1: DONE (106/106 boarded)

`Checkers/RepWL.v` is complete and sound (`rw_check_neverqh_sound`,
functional_extensionality_dep only) and all 106 `neverqh_rwlrank`
holdouts are proved (`Machines/RepWL_Batch_{01..04}.v`,
`tools/repwl_manifest.tsv`; coverage 3464 -> 3570 of 3713, the
rwlrank family cleared).  What remains of the original two-session
plan is SESSION 2 ONLY: wire `rw_check_neverqh` into the census
`decide_easy` as a tier (plus the wrap/QHBound tier), sweep the
31,758 wrap-survivor residue with `tools/repwl_prover.py` to measure
the kill rate, regenerate `Deferred_*`, and re-run `make census`
once for both tiers.  Remaining holdout families after this board:
102 irules-deferred, 17 neverqh_drift (FuelSCC gate + a (c3) drift
descent variant), the counters tail (wave 6, tower 4, xd 3, ...),
and the 1 upstream-open machine.

## Next: the RepWL port (two sessions)

Highest-leverage block left, paying on both ledgers: the 106
`neverqh_rwlrank` holdouts AND the ~25-30k RepWL-class machines that
dominate the 52,326-machine census residue.  Derisked by three
existing artifacts: Coq-BB5 ships a BB4-flavored `Decider_RepWL.v`
(1,320 lines, `../Coq-BB5/CoqBB5/BB4/Deciders/`, with the
`RepW_match`/`RepWL_match` concretization relations and the closed-set
construction proved); the `Closure.v` engine is generic over the
abstraction (plug in context type + injective enc + `succs`/`covers`
and ranks, the lex gate, and the FuelSCC runner gate all come free);
and the rwlrank measure vocabulary is small and documented
(`../BBB/docs/neverqh.md`: `N/A,N/L,N/R` block counts + `0/l,0/r`
interior blank counts, with exact per-node deltas -- the `comp_exact`
contract).

- **Session 1** (fuel-session shape): `Checkers/RepWL.v` instance +
  measure vocabulary + exactness lemmas, Python mirror forked from
  the fuel generator, differential-validate the 106 certs
  (`../BBB/results/certs_rwlrank`, params `block`/`threshold` per
  cert), board as `Machines/RepWL_Batch_*.v` with corruption tests.
  Two design risks to settle on day one: the tape-model impedance
  (Coq-BB5 is directional head-between-cells; BBB4 is head-on-cell
  `nat -> Sym` sides -- re-derive `covers`/`succs_sound` locally, do
  not transcribe), and the single-step contract (`succs_sound` is one
  concrete step to one covered successor, so the RepWL step relation
  must peel the front word at symbol granularity, no macro-jumps).

  **SESSION 1 STARTED -- design validated, prover built, 106/106
  catch-rate measured.**  `tools/repwl_prover.py` is the executable
  design spec for `Checkers/RepWL.v` (its docstring pins the context
  shape, step, and normalization): head-on-cell configs
  `(q, hp, buf, litems, ritems)` with whole-block buffers
  (|buf| in {L, 2L, 3L}), symmetric nearest-first item lists (left
  words stored mirror-image so both sides run one code path),
  fold-on-|buf|=3L with RLE merge saturating at T, cap-branch on pop
  (mirror of verify.c `wg_succ`, re-expressed symmetrically), the
  five documented measures with per-node deltas (`rdelta` /
  `arrival_info` implement the exactness argument's witness bits).
  Rules (a)/(b) with the cert measures discharge EVERY state of all
  106 rwlrank holdouts at t=0; largest closure 13,994 abstract
  configs (fine for vm_compute).  Coq progress (all Qed, committed): denotation
  (items_den/side_den), the symmetric step, rw_succs_sound,
  injective encoding (rconf_enc_inj), seed (chunk/rle +
  rw_seed_covers), and the wf layer (item_wf, rw_covers',
  rw_succs_sound').  REMAINING, with the design pinned:

  1. STRENGTHEN item_wf to [w <> [] /\ 1 <= c /\ (cap -> 2 <= c)]
     with [2 <= T] threaded through the checker (certs all have
     T in {2,3}).  Reason: the interior measures' "nonblank beyond"
     bit counts a first item's word when [2 <= c || cap]; a
     c=1-capped item admits k=1 vs k>=2 expansions that differ in
     the bit, so no per-node delta is exact -- cap must imply >= 2.
     Preservation: merge gives c1 = min (S c0) T >= 2 when c1 = T
     or cap0 (c0 >= 2); new items are (w,1,false) since T >= 2.
  2. Measures: values on cconf -- countnb (1s) and ibc (interior
     blanks: cell = S0 with a nonblank strictly farther in the
     list); rwmeas := RwNA|RwNL|RwNR|RwZL|RwZR.  Deltas on the node
     via arr_s2 (arrival cell: buffer head, else first item word's
     head, else S0), arr_nbb (beyond-arrival bit: rest-of-buffer ||
     items_nb, else tl w0 || (2<=c||cap)&&nonblank w0 || items_nb
     rest), dep_nbb (departed side: whole old side).  Exactness
     correspondences: arr_s2 = chd of the concrete side (wf: k >= 1
     and w0 nonempty make expansions start with w0); blankness of a
     side <-> word_blank buffer && ~items_nb items (wf makes every
     item contribute >= 1 copy, so items_nb is exact both ways);
     ibc equations ibc(w::l) and ibc(ctl l) are definitional.
  3. Checker: rwcomp := RwRankE (phi : list (positive*nat)) |
     RwMeasE (m : rwmeas) (K : nat) phi (gate : list positive),
     denote to LexMeas rconf (rw_mval m) (fun a _ => rw_delta tm m a)
     with rconf_enc keys; instantiate closure_check_neverqh_lex with
     rw_succs/rw_covers'/rconf_enc/rw_state, seed rw_seed L T at
     csteps t; params (L T t fuel).  Gate 1 <= L, 2 <= T.
  4. Python: align repwl_prover.py's seed to the Coq chunk/rle of
     the CTAPE lists (sim with explicit (l,h,r) lists, not a tape
     dict), mirror rw_delta/arr_* exactly, re-run the 106 survey,
     then fork the emitter (gen_repwl_certs.py) emitting
     RwRankE/RwMeasE tables keyed by rconf_enc + the
     `apply (rw_check_neverqh_sound ...)` theorems, batch as
     Machines/RepWL_Batch_*.v, corruption tests, manifest
     repwl_manifest.tsv wired into check_coverage.
- **Session 2**: wire the checker into the census `decide_easy` as a
  tier, sweep the 31,758 wrap-survivor residue with the Python
  mirror to measure the kill rate, regenerate `Deferred_*`, re-run
  `make census` (native switch, 2-3h wall).  Kept separate so
  session 1 never blocks on the census rebuild loop.

<!-- --- census verified-tiers wiring session (2026-07-18) --- -->

# Census verified-tiers session: D_census 56,039 -> 19,735

**CERTIFIED 2026-07-18**: `census_decided : forall tm, QHBound B_census
tm \/ Deferred D_census tm` is Qed through the kernel with the new
tiers and the 19,735-machine deferred list; `Print Assumptions` =
`functional_extensionality_dep` only.  Merged with main (disjoint
drift/irules tracks; only NEXT_SESSION needed a keep-both resolve).

Wired the two new verified tiers into the census `decide_easy` and
regenerated the deferred list.  Branch `claude/census-verified-tiers-
wire-e51w4e` (PR #11).

## What shrank the deferred list

The 52,326-machine residue was cut by 36,304 at census-walk time by
three parameter-closed tiers (no per-machine certs in the walk):

- **wrapped QHBound, plain acyclicity** (`ngram_check_qhbound`, tier Q):
  5,307 prefix-quiet quasihalters -> R_QH.
- **wrapped QHBound, lex gate** (`ngram_check_qhbound_lex` + in-Coq
  RankSearch certs): 5,486 more -> R_QH.
- **RepWL** (`rw_tier` in `Census/RepWLSearch.v` -> the verified
  `rw_check_neverqh`, tier W): 25,511 never-QH core machines -> R_NeverQH.
  Ladder (`rw_rungs_census`) is t=0 only, (L,T) in {(2,2),(3,2),(4,2),
  (2,3)}, `rw_fuel` 8192 (the 16-rung grid measured ZERO catches at t>0;
  closure sizes p50 185 / p99 1,010 / max 3,963, all under the fuel).

New residue 16,022 = 9,775 wrap-QH survivors (need a stronger measure/
pattern QHBound gate) + 6,247 never-QH survivors (need rwlrank measures
or bigger rungs).  D_census = 3,713 holdouts + 16,022 = **19,735**.

Sweep mirrors / artifacts (untrusted): `tools/sweep_qhbound_lex.py`,
`tools/sweep_repwl_residue.py`, `tools/finish_repwl_sweep.py`,
`tools/regen_residue.py` (reproduces Deferred_* from the committed
`*_caught.tsv` + `wrap_residue_survivors.txt`); validation probes
`tools/gen_tier_probe.py` (94/94 qhb + 40/40 rw machines pass through
the Coq checkers via vm_compute); corruption tests in
`Tests/Census_Corruption.v`.

## GOTCHA: the tiers made the census walk ~100x slower per machine

Newly-undeferred machines now run the full ngram->rank->qhb->rw ladder
(~46ms/pop vs ~0.1ms with the old fat deferred list).  The residue-heavy
1RB/0RB grandchild subtrees became **>2.5h single native_compute walks**
-- longer than the remote container's ~2h preemption window, so they
never certified monolithically (watched it restart 5x).

FIX (this session): generalize Run_Split2 to a **great-grandchild
split** of the 7 heavy grandchildren (1RB_0LC/0RC/1LA/1LB/1RC,
0RB_1LC/1RC).  `tools/gen_gsplit_heavy.py` expands each grandchild's
first undefined transition into its 12/16 fills (node_expand_spec),
emitting `Census/Run_Split_<tag>.v` + 104 `Compute/GGH_<tag>_*.v`
sub-walks (few min each) + replacement `Compute/G_<tag>.v`.  `make
census` order updated.  Result: every walk unit fits the window and is
resumable (skips done .vo), so restarts cost only in-flight sub-walks.

If splitting a future regeneration's heavies: add rows to
`gen_gsplit_heavy.HEAVY` (the (A0,B0,w,w2,d2,nx2) tuples), regenerate,
wire the Makefile globs.  If a sub-walk itself exceeds the window, split
it again (same tool, one level deeper).
<!-- --- drift track --- -->
## Drift track (this session): the 17 neverqh_drift holdouts are boarded

Rule (c3) is formalized (`theories/Checkers/Drift.v`,
`ngram_check_neverqh_driftw_sound`) and all 17 upstream
`neverqh_drift` machines have theorems in
`theories/Machines/Drift_Batch_01.v` (coverage 3,570 -> 3,587; the
`neverqh_drift` line is gone from `check_coverage.py`'s remaining
table).  Key facts for future sessions:

- The descent generalizes FuelSCC's window induction to the measure
  `W * R + phi a` with untrusted Bellman-Ford potentials; fuel is
  needed only at TOWARD-moving gate nodes (weaker than verify.c's
  all-intra-active premise), and the record argument is not used
  directly -- the window bound of Records.v already carries it.
- Two disjoint per-state gates (R and L drift) are REQUIRED: two of
  the 17 have a single state with opposite-drifting stuck SCCs, so
  the FuelSCC mirror-orientation trick cannot work.  Disjointness
  makes at most one budget live per node (`dbudget`), keeping the
  descent one nat induction.
- `tools/drift_prover.py` mirrors the checker (dw_procedure +
  dw_state_check); `tools/gen_drift_certs.py --dry-run` re-measures
  the catch.  All 17 land at n=2 t=0 in seconds; deferral mechanism
  (tools/drift_deferred.tsv) exists but is empty.
- The drift gate strictly subsumes the (c2) runner gate (a uniform
  fueled right-mover SCC has trivially feasible potentials), so new
  fuel-shaped SCCs can also be discharged by this checker if a
  future track wants one engine instead of two.

<!-- --- irules multi-decrement track --- -->
## IRules multi-decrement track (general step-size decrements)

Boarded ALL 42 of the `certs_modclass` v3 irules holdouts tagged
"decrement delta(s) [-2]/[-3] (v1 engine supports -1 only)"
(`tools/irules_deferred.tsv`).  Coverage 3587 -> 3629
(`irulesk_manifest.tsv` wired into `check_coverage.py`).  Checker
`theories/Checkers/IRules/RulesK.v` + `MetaK.v`, both
`functional_extensionality_dep` only; the v1 `Engine`/`RLE`/`Expr`/
`Rules`/`Meta` are untouched.  Build the batches at `-j1`/`-j2` (this
container OOMs compiling IRules batches at `-j4`); each machine's
`vm_compute` runs a ~1-2.8M-step concrete anchor re-simulation (~4 s).

Two mechanisms, both reusing the same applier:

1. General step-size decrements.  `find_binding` (the binding-run
   selection) is UNTRUSTED.  Soundness comes only from the guard
   `expr_ge lo Rex 1` plus `appK_side`'s per-decrement survival re-check
   `e + d*Rex >= lb + d` (the run's minimum over the R rounds is its
   last-round value).  So the R-fold application is sound for ANY `Rex`;
   the division/binding search only has to produce the `Rex` that lands
   the drained run exactly, and the proof never mentions it.  This kept
   `ruleK_apply_sound` a line-for-line generalisation of
   `Rules.rule_apply_sound` (same induction on R, reusing `vvals` /
   `rstart` / `rend` / `rule_sem`).

2. Rule-in-rule application (one level).  Ten of the 42 have a rule
   whose proof applies an already-validated lower-index rule; without it
   the replay ratchets over a symbolic-count run (the head crosses it
   via a multi-step maneuver the engine peels cell-by-cell -- verified
   by instrumenting the C verifier: rule 2 of
   `1RB0RA_0RC1LD_1LC0LA_0RD0RB` applies rule 1 at op 5).  This is NOT a
   new engine op: `check_rulesK` validates rules in index order and
   threads the already-validated ones into each rule's replay via
   `ruleK_check`, reusing `ruleK_apply`; `check_rulesK_sound` discharges
   `replayK_sound`'s per-rule Reach obligation with `ruleK_apply_sound`,
   so the dependency (strictly lower index) is well-founded.  The
   corruption tests show it is load-bearing (a dependent rule validated
   before/without its dependency fails).

Differentially confirmed against the C verifier: `bin/verify` accepts
all 42; `tools/irulesk_prover.py` (faithful mirror: engine port +
binding-run applier + rule-in-rule) accepts the same 42 and validates
all 504 rules across the 428 v1 certs -- no false positives.

UPDATE (this session): the 3 `d=-1 only, but v1 engine bound reasoning
fails` rows are NOT actually out of scope -- that note was about the v1
`Rules`/`Meta` engine.  The general-delta `RulesK` engine's per-decrement
survival re-check discharges all three (`1RB1RD_0RC0RD_1LC0LA_0RB1LD`,
`1RB1RD_0RC1LD_1LC0LA_0RD0RB`, `1RB1RA_0RC1LD_1LC0LA_0RD0RB`); the mirror
passes them and the Coq checker closes each by `vm_compute` (~24 s anchor
re-sim).  Boarded as `Machines/IRulesK_Batch_07.v` (no checker change --
same `irulesk_check_neverqh_sound`), manifest rows appended.  Coverage
3635 -> 3638.  The only remaining irules blockers are the 44 v6 `rulepfx`
+ 6 v7 (`rulepfx`,`rulerunm`) and the 1 v4 `certs_geom` machine.

<!-- --- irules block-run track (added by the block/rule-prefix session) --- -->
## irules BLOCK-RUN track -- Phase 1 LANDED (6 boarded, 3629 -> 3634)

Target: the 50 irules holdouts whose certs use block runs -- the 6 tagged
`v3 cert, needs blk` (Phase 1) and the 44 tagged `v6 cert, needs
blk,rulepfx` (Phase 2).  A run's symbol may be a BLOCK id `>= 2`
(`blk <id> <cells>`); a run `(B, e)` denotes `e` copies of `B`'s cell
sequence, not `e` copies of one symbol -- the CRUX.

### Landed this session (all green, `functional_extensionality_dep` only)

The full block checker vertical is built, sound, and BOARDS 5 of the 6
v3-blk holdouts through the actual Coq checker (`vm_compute`):

- **`theories/Checkers/IRules/EngineK.v`** -- the block symbolic engine
  against `bdside tbl` (parametric in the UNTRUSTED table): `bdside` /
  push / merge / trim; `beng_step` = concrete step + chain hops + block
  PEEL + block HOP, `beng_step_sound` a `Reach`.  Block-HOP crux:
  `hop_sim` (one-copy zipper replay, each step one `cstep`) ->
  `hop_one_reach` -> `hop_copies` -> `bhop_result` (replay + primitive-
  root reduce + table lookup + re-verify) -> `bhop_reach`.
- **`theories/Checkers/IRules/RulesBlk.v`** -- `ruleBlk_apply` +
  `ruleBlk_apply_sound`, rule-in-rule `check_rulesBlk`, driver
  `breplayK`, sound cell-stream end-equality `bstreams_eq` (expand
  constant block runs + `merge_adj` + structural compare -> exact
  `bdside` equality), and the driver canonicalization `bcanon` =
  re-block (`breblock_side`, untrusted greedy re-encode VERIFIED by
  `bstreams_eq`) + whole-copy `babsorb` (proven denotation-preserving).
- **`theories/Checkers/IRules/MetaBlk.v`** -- `irulesblk_check_neverqh`
  (block table via `mk_tbl`, `raw_ok` by construction; templates,
  anchor re-sim, state coverage; end-match strict-or-`bstreams_eq`) and
  `irulesblk_check_neverqh_sound : ... -> NeverQuasiHaltsSt`.
- **`theories/Machines/IRulesBlk_Batch_01.v`** -- 5 boarded machines;
  **`theories/Tests/IRulesBlkBatch_Corruption.v`** -- negative controls
  (honest true; transition / block-table / rule-delta / meta-a / meta-b
  mutants all `false`).  `tools/gen_irulesblk_certs.py`,
  `tools/irulesblk_manifest.tsv`, one `check_coverage.py` tuple,
  marked `_CoqProject` block.  (`tools/irulesblk_prover.py` was the
  de-risking scaffold: it measured the minimal mechanism set and diffed
  against `bin/verify`; the ground truth is `bin/verify` + the Coq
  checker.)

### LANDED: the 6th v3-blk (partial absorb) -- 3633 -> 3634

`1RB0RD_1LC1LB_1RD0LB_0RD1RA` (14 blocks, 6 rules, anchor 9,999,528) is
now boarded.  Its `iv_absorb_side` does PARTIAL (symbolic-remainder)
absorbs -- a single-cell run contributes only PART of its cells (`need+1`)
to complete a block copy and stays, decremented, rather than the whole
copy sitting as separate count-1 runs.  Instrumenting `bin/verify`
(`DBG_ABSORB`) showed this machine's partials are on CONST runs
(e.g. block 7 `10111`: a `1x3` run gives 1 leading cell, leaving `1x2`).

Formalized in `RulesBlk.v` with an UNTRUSTED-candidate + re-verify design
(same philosophy as `breblock_side`), so the peel logic never enters the
trust surface:

- `bpeel_rev tbl budget rrs` -- untrusted: peel `budget = length (tbl s)`
  concrete cells off the RIGHT of `acc` (= FRONT of `rev acc`), consuming
  single-cell const runs, decrementing the leftmost touched run.
- `babsorb_partial lo tbl acc s e rest` -- proposes `new_acc := rev (bpeel_rev ...)`,
  then GATES on `expr_ge lo e 0 && bstreams_eq tbl lo acc (new_acc ++ peel_cells tbl s)`
  (i.e. `acc` denotes `new_acc` followed by exactly one block copy), and
  returns `new_acc ++ (s, e+1) :: rest`.
- `babsorb_partial_den` -- soundness: `bstreams_eq_sound` gives
  `bdside acc = bdside new_acc ++ tbl s`; the symbolic block-run `+1`
  rides the same `cnt_succ` + `nreps_S` fold as the whole-copy case.
  A wrong peel just fails the `bstreams_eq` re-check -> no absorb (sound).
- Wired as the `else` branch of `babsorb_go` at a block run (whole-copy
  fast path unchanged, so the other 5 machines are untouched); `bcanon`,
  `babsorb_iter`, the driver, and `MetaBlk` need no change.

Negative control: `theories/Tests/IRulesBlkPartial_Corruption.v` (block-7
cells mutated -> checker `= false` at rule validation, 1.3 s).  Axiom
footprint `functional_extensionality_dep` only; `check_coverage` now 3634.
All 6 v3-blk holdouts boarded; Phase 2 (44 v6 `rulepfx`) is the next block.

### Phase 2 (rulepfx, the 44 v6) -- deferred, on top of Phase 1

Add prefix matching to the applier (a `rulepfx` side matches only the
first `r->nl` near-head runs and splices the untouched rest back; a
non-prefix side keeps exact-count matching and must not be a sentinel
side) + sentinel sides to the engine (a prefix rule's OWN validation
treats its prefix sides as opaque; `beng_step`'s `[] ->` branch must fail
when `sent[side]`, so the proof reads only the declared runs).  Check
whether the 44 need v6 `rmdok` (a binding drain leaving remainder
`rmd = (e-lb) mod d`, ending at `lb+rmd-d`); the survival check already
covers it, only the drop-to-0 condition changes in a forked
`find_binding`/`appBlk_side`.  Fork `RulesBlkPfx.v` / `MetaBlkPfx.v` +
`IRulesBlkPfx_Batch_*.v` + corruption tests; differential-validate the 44
vs `bin/verify` first.  Machines whose certs ALSO need
`rulerunm`/`mmrow`/`nvar` are out of scope (re-check per cert).
<!-- --- end irules block-run track --- -->

<!-- --- census D-shrink session (2026-07-19/20): proven tier + B/C grind post-mortem --- -->

# Census D_census shrink (2026-07-19/20): proven tier LANDED; B/C in-walk grind ABANDONED

## TL;DR / the one lesson
**Shrink D_census by PROVING machines (they drop out via the zero-cost proven
tier), NOT by un-deferring machines into expensive in-walk tiers.** The latter
makes the census native_compute walk hours-long per subtree, which CANNOT
certify in a container that preempts every few min-30min. Measure the per-unit
walk time BEFORE committing to any lever that un-defers into an in-walk tier.

## What worked and is banked (committed + pushed)
- **Proven-machines tier (lever A): -3,620, ZERO walk cost.** `Census/Proven_00..07.v`
  + `Proven_Data.v` (tools/gen_proven.py), `proven_lookup` in Decide.v before the
  deferred tier, WF via `Forall NeverQuasiHaltsSt` over the batch theorems. This is
  the compounding conveyor belt: any machine that ever gets an individual Coq
  theorem drops out of D_census for free at the next regen.
- **Measurement of all three levers** (parallel opus sweeps): A proven audit
  (3,620 usable), B qhb-lex over 9,775 wrap-QH survivors (2,533 catch, larger
  prefix rungs), C RepWL over 6,247 never-QH survivors (592 catch, (5/6/7,2,0)).
- **Recon roadmap** (tools/recon_20260719/): FAR post-mortem (SKIP -- safety-only,
  liveness-dead despite 100% nonhalt coverage), re-root normalization bridge
  (~1,300 more via one small lemma; residue is 9,917 distinct upstream-solved
  machines), irules Phase 2 differentially validated (-50 holdouts).
- **Deep-split tooling** (tools/gen_gsplit_deeper.py, tools/census_grind.sh):
  recursive great-great-grandchild splitter + self-splitting resumable grinder.
  Correct and reusable IF a STABLE long-lived compute env is ever available.

## The wild goose chase -- DO NOT REPEAT here
Levers B (qhb-lex, +2,533) and C (RepWL, +592) un-defer machines that then run the
full ngram->rank->qhb->rw ladder DURING the census walk (~46ms+/pop, vs ~0.1ms for
a deferred-lookup skip). This made the residue-heavy grandchild subtrees
(1RB_1LC, 0RB_1LC, ...) into MULTI-HOUR single native_compute walks. Deep-splitting
them (recursive node_expand) makes units smaller, but those subtrees are so large
(GG_1LC_0LB alone: 331+ sub-walks, not done after 8h; est. 6,000-10,000 total
sub-walks) that the full 12,974 grind is **1-2 WEEKS**. And the container preempts
every few min-30min, so hours-long units NEVER complete -- confirmed stalled
(+5 .vo in 1.5h). Structurally impossible in this environment.
The SCOPING instructions warned exactly this ("a lever that recovers few machines
at high walk-cost may not be worth the cert-time tax"). B/C were that.

## THE RIGHT WAY to shrink D_census (do this going forward)
1. **Keep the census walk LIGHT.** Deferred list stays fat enough that every
   subtree walk is "few min" and fits a container window (the 19,735 cert had this;
   it certified in 2-3h with the great-grandchild split, units "few min each").
2. **Shrink only via per-machine PROOFS + the proven tier.** Prove a machine
   (holdout cert or residue cert), add it to the proven table, regen Deferred to
   drop it. Walk cost unchanged (fast proven lookup). This is the sustainable loop.
3. **Next levers, all proof-producing (proven-tier-cheap):**
   - Re-root bridge (~1,300): `neverqh_reroot`/`qhbound_reroot` (~20-30 line
     StA-variant of visits_swap/quiet_swap) + a reroot table. tools/recon_20260719/
     BRIDGE.md + reroot_mapping.tsv. Also gives free de-dup (12,897 rows = 9,917
     distinct) and ~1,295 <=3-state-core reductions.
   - irules Phase 2 (-50 holdouts): fork RulesBlkPfx/MetaBlkPfx. PHASE2_DESIGN.md.
   - Bouncer/segment checker (residue mass lever): verified checker over upstream
     certs_bouncer period_records+segments -> per-machine certs -> proven tier.
     (Bouncers are common here; reference in bbchallenge-deciders + BB5 project.)
4. **Do NOT re-enable the qhb-lex/RepWL in-walk tiers (B/C)** unless a stable,
   long-lived native_compute environment is available. Their tables (Deferred at
   12,974, sweeps, gen_gsplit_deeper) are committed for that scenario only.

## This session's actual deliverable: proven-only cert (D_census 16,115)
Pivoted from 12,974 (abandoned) to proven-only: **D_census = 16,115 = 93 holdouts
+ 16,022 residue** -- drop ONLY the 3,620 proven-nqh machines; B/C residue and the
16 provenQH stay deferred. Walk is LIGHT (B/C deferred, monolith units "few min
each"), so it certifies within container windows via .vo-skip resume. The B/C
rungs stay wired in Run.v but are dead code (their machines are deferred, caught
before the rungs fire). [status filled at cert completion]

## Env note (container instability, 2026-07-20)
The container preempted every few min to ~30min during this session (vs stable
1.5h+ earlier). Any long native_compute (the census walk, or heavy grind units)
must be resumable and window-sized. The census `all`/`census-resume` path with
monolith units is resumable (.vo-skip). Native switch: OPAMROOT=/root/.opam,
eval $(opam env --switch=census) -- rebuild from apt if the switch is missing
(~1h; the switch survived this session's restarts on /home persistent disk).
<!-- --- end census D-shrink session --- -->
