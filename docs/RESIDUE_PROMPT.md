# Residue prompt — the nested front is spent down to its measured blockers

_Refreshed 2026-07-28 at the end of the wave-24 CASCADE track (branch
`claude/residue-reduction-cascade-yhqvj4`), which closed the cascade gate and
built the route end to end -- extractor, level induction, emitter, 57 of 87
machines compiling -- but boarded NOTHING: an overflow branch is not a board,
so `D_remaining` is unchanged.  `docs/WAVE24_FINDINGS.md`.  Before it, the
wave-23 RESIDUE track (branch `claude/residue-list-refinement-cxzdax`) boarded
the whole
15-machine "no visit witness (`StA`)" bucket by the state-AVOIDANCE route:
the kernel recomputes from the SAME lap chains that no window step is ever
in `StA` (`Checkers/LapAvoid.v`, axiom-free), and
`Counters/LapGlueQuiet.v` turns that plus a checked bootstrap window into
the R_QH triple with the exact last-visit bound.  `D_remaining` is **496**
and 4,660 of the frozen 5,156 are settled (90.4%).  Wave-22 before it
landed 110 boards (the "no shift chain" 8 and 102 of "no inner family at
`pow2 j`" via the OFFSET-family route).  Full assessments:
`docs/WAVE23_FINDINGS.md`, `docs/WAVE22_FINDINGS.md`; the wave-18 story is
`docs/WAVE18_FINDINGS.md`._

_**Scope: the RESIDUE, which is now everything.**  The (4,2) HOLDOUT list was
closed on 2026-07-28 when tower #20 was boarded (`NEXT_SESSION.md` §2l), so
these 496 rows are the entire remaining problem.  `docs/RESIDUE_MAP.md` maps
them by shape and blocker._

**Before pasting, check:** substitute the branch the session should develop
on, and name any files a concurrent session owns.

---

```
Continue the (4,2) residue reduction in carrino/Coq-BBB4, on a new branch off
main.

READ FIRST, in this order:
  docs/WAVE24_FINDINGS.md   -- THE TASK's state, all of it; it is short.  The
                               cascade gate is CLOSED and the route is BUILT:
                               all three per-level chains derive, the level
                               induction is theories/Counters/
                               NestedLapCascade.v, and cascade_emit.py turns
                               57 of the 87 into a Coq overflow branch the
                               kernel accepts.  Section 6 says what is left
                               (boarding), section 7 the new do-not-retries.
  docs/CASCADE_EXIT.md      -- the design brief behind it.  Read section 4d
                               (the gate closed, and the two structural
                               corrections: the cascade descends to level 0,
                               and the main count IS the level-j second
                               count).  Sections 1-4c are history and are
                               marked as such where 4d supersedes them.
  docs/WAVE18_FINDINGS.md   -- all of it; it is short.  Section 4b is the
                               wave's most useful result and it is a NEGATIVE:
                               the two remaining nested-lap chain buckets are
                               EXPONENTIAL, so they are not search gaps and no
                               derive_chain widening can touch them.  Section 6
                               is the lesson (when a fix lands as a defaulted
                               FLAG, grep every caller, not just the one that
                               motivated it).
  docs/NESTED_LAP_PLAN.md   -- the design that produced the 225 boards.  The
                               status banner at the top says what is confirmed
                               and what is superseded.  Its index-shift and
                               `rep u j ++ post` warnings BOTH still stand at 0.
  docs/WAVE16_FINDINGS.md   -- sections 5 and 6.  Section 5 is the
                               do-not-retry list for derive_chain widenings
                               (five, all measured at 0).  Section 6b is why
                               the 15 "no visit witness" machines are NOT
                               visit-witness machines.
  docs/LAPDECIDER.md        -- the checker's design.
  docs/CLOSEOUT_ROUTE_A.md  -- how boards become D_remaining shrinkage.

ENV: apt coq 8.18.0 -- `apt-get install -y coq`, then
`coqc -native-compiler no -Q theories BBB4 <file>`.  No opam bootstrap.
`coq_makefile -f _CoqProject -o Makefile.coq` first; the Counters+Checkers
closure builds in ~30 s.  Do NOT run `make all` -- it pulls in the census.

CI IS RED AND IT IS NOT YOURS: GitHub Actions is out of billing quota, so
every ci.yml run -- on main too, unbroken since 2026-07-26 -- is reclaimed
mid-job with "The runner has received a shutdown signal" / "operation was
canceled" ~8 min in, while compiling whatever heavy file it happened to reach
(usually IRules_Batch_*/Bulk/TCyc_05), with NO Coq error above it.  Do not
diagnose it, do not tune ci.yml parallelism (a `-j4 -> -j2` theory was
suspected on #48 and is WRONG), and do not read a red check as your diff
being broken.  Verify locally instead: coq_makefile, then build only the
files you touched, plus census_cache --check.

NON-NEGOTIABLE: never touch theories/Census/; `python3 tools/census_cache.py
--check` must stay MATCH.  A board counts only when its file compiles and
`Print Assumptions` shows functional_extensionality_dep only (LapDecider,
LapCertGlue, LapGlueAbs, NestedLap and NestedLapLift are axiom-FREE or
funext-only -- keep them that way).  Everything under tools/ is UNTRUSTED;
the kernel re-checks every board.

STATE: 4,660 of the frozen 5,156 settled (90.4%); D_remaining = 496.
THE HOLDOUT LIST IS CLOSED.  Everything left is RESIDUE and all of it is
yours.  docs/RESIDUE_MAP.md + tools/closeout/residue_map.tsv give every
remaining machine's measured lap shape and the exact blocker.

Failure profile at D_remaining = 496 (residue_map.tsv, wave-23):

  211  no overflow phase           -- ALL of them the no-anchor bucket
  105  no interior chain           -- QUAD 41, HIGHER 13, PARITY-AFFINE 13,
                                      EXP3 10, EXP4 6, AFFINE/AFFINE 14, EXP2 8
   65  no exit chain               -- MEASURED EXPONENTIAL; identification,
                                      not chains (re-measured wave-22: the
                                      N-count route buys 0 of these)
   60  no inner family at pow2 j   -- what SURVIVED the offset/split/refill
                                      routes; 32 have no family under any
                                      route, the rest fail an offset chain
   24  no anchor
   20  no boot chain               -- same population as "no exit", other side
    5  no second exit chain        -- the SCycR-entry-offset checker gap,
                                      measured precisely (WAVE22 section 2b)
    4  no inner interior chain
(the 15 "no visit witness (StA)" rows were boarded in wave-23 -- the AVOID
route, LAPQ_* -- and are gone from the map)
ovfshape over the 496 for shape rather than blocker:
  235 no-anchor, 132 AFFINE/EXP2, 37 AFFINE/AFFINE, 41 QUAD,
  13 PARITY-AFFINE, 13 HIGHER, 10 EXP3, 9 AFFINE/HIGHER, 6 EXP4.
Per-machine cost is a vm_compute:
  python3 tools/counters/emit_lapcert.py --list FILE --emit   (25 alphabets)
After a wave, inventory.py + gen_stages.py + audit.py shrink D_remaining by
exactly what you boarded, in minutes.

THE TASK (re-ranked 2026-07-28 after wave-24 BUILT the cascade route; the
  theory and the emitter are done and the remaining work is BOARDING):

  (0) BOARD THE CASCADE.  The theory is DONE and nothing here is open
      research -- this is wiring.  57 of the 87 "no exit chain"/"no boot
      chain" machines already have a kernel-checked exponential overflow
      branch; what they do not have is a BOARD, so D_remaining has not moved.

      WHAT ALREADY EXISTS (do not rebuild any of it):
        nestcert.cascade_endpoints  the law, the per-level word check down to
                                    level 0, the peel x split framing search,
                                    boot + inner lap + all three chains
        nestcert.cascade_validate   the whole cascade replayed against the raw
                                    simulator at j = 2..8
        NestedLapCascade.v          fill_hop, level_hop, cascade_down,
                                    cascade_down_all, cascade_overflow,
                                    cascade_vis_at / cascade_vis (funext only)
        cascade_emit.py             renders the ENTIRE overflow branch per
                                    machine; 57 of 57 gated machines compile
        theories/Tests/CASC_0RB1LA_0LC1RD_1LA1LD_1RB0LA.v   one pinned example
      Reproduce: cascade_probe.py --gate            (all 87, gates 57)
                 cascade_probe.py --endpoints SPEC -K 7
                 cascade_emit.py --proto SPEC -K 7 -o FILE

      THE BUILD -- a third route in emit_lapcert, beside `nested` and
      `offset`.  The exact hooks, all in tools/counters/emit_lapcert.py:
        derive():   the try/except ladder that calls NC.derive_nested then
                    NC.derive_offset -- add NC.cascade_endpoints as a third
                    arm.  Mind the two lines after it: `offset` swaps in
                    B0R/B1R, and `cho = nest['che']` / `ro = srun(.., BE0)`
                    assume a single exit chain.  The cascade's exit is the
                    CLOSE chain, so cho = the CL chain and ro = srun from CL0;
                    D['B1'] is then ro[0], which is CL1, NOT the anchor B1 --
                    that is exactly what gcx_ bridges.
        render():   `offset = bool(N and N.get('route') == 'offset')` needs a
                    cascade sibling, and then four holes switch on it:
                    @OVFDEFS@ (nest_defs*), @OVFCASE@ (NEST_OVFCASE),
                    @NESTGLUE@ (nest_glue*), and the reps.update() at the end
                    (nest_reps*).  cascade_emit.PROTO is ALREADY the whole
                    branch -- SPLIT it into cascade_defs / cascade_glue /
                    cascade_reps in that shape rather than writing new Coq.

      THE ONE PIECE WITH A NEW SHAPE: the VISIT witnesses.  A board must show
      every state fires.  viso_ covers the boot unchanged; for the rest the
      analogue of visx_ is NestedLapCascade.cascade_vis, and the catch is that
      it is sound at an arbitrary level but only LEVEL 0 is available at every
      outer index (the obligation is universally quantified in j, and the
      cascade at j reaches down to level 0 only).  So a state that fires
      nowhere in the boot has to fire in the CLOSING SWEEP -- which is a long
      full-tape sweep, so expect it to cover what is left, but MEASURE that
      per machine before assuming it.  If some state fires only in a per-level
      A/B transition, cascade_vis_at at a fixed level does NOT discharge it.

      GOTCHAS ALREADY PAID FOR (all of these cost time in wave-24):
        * landing bridges need a pad on BOTH sides.  A chain accepted up to
          lift can stop PAST the anchor or one cell SHORT of it (when the
          anchor's own tail ends in a blank lift cannot see).  Both occur in
          this bucket; cascade_emit._pads/_nest handle it.
        * re-SPLIT trailing blanks before rewriting them away.  After the
          normalisation the side is one fused literal and there is no
          `_ ++ [S0]` left for lbl_ to match.
        * define lbl_ BEFORE its first use.  `rewrite ?lbl_X` with lbl_X
          unbound silently does nothing (the `?` swallows it) and the failure
          surfaces as an unrelated `reflexivity` error much later.
        * the boot lands on B(j), not on some entry anchor: tail_main IS
          extraB ++ rep unit (M - j) (law['main_is_B']).

      AFTER THE BOARDS: inventory.py + gen_stages.py + audit.py shrink
      D_remaining by exactly what you boarded.  A board counts only when the
      file compiles and Print Assumptions shows functional_extensionality_dep
      only.

      THEN the 30 that do not gate: 12 report a main count one octave down
      (families() already carries an `oct` for that shape -- emitter work, not
      theory), 17 report one or two counts in the phase (the `no boot chain`
      mirror half plus the 15 odd-shaped rows), 1 a main count at 4..7.
      Also point cascade_probe at the 60 "no inner family" survivors and the
      EXP3/EXP4/HIGHER interiors (a deeper cascade is exactly what a
      Theta(3^j) lap smells of) -- both untouched by wave-24.

  (0b) The 60 "no inner family" survivors: 32 have no decodable family under
      any route (alphabet work -- alphabet_infer.py -- or ASK JOHN with a
      CLASS tape dump); the rest fail one of the offset chains and nothing
      measured says they are close.  Run cascade_probe over them FIRST --
      the negative-octave/deep-tail window sees families families() cannot.

  DO NOT RETRY (measured wave-24): framing the cascade's B->A transition with
  the opaque split where A->B's sits (no chain at any peel); framing it at
  peel 0 (no chain at any split); reindexing the cascade's overflow branch at
  j = S j' the way the offset route does (unnecessary -- the peel absorbs the
  shift, and the reindex buys a concrete j = 0 case for nothing).
  DO NOT RETRY (measured wave-18/22): a wider inner-key tail (MAXTAIL);
  octave-only families (pow2 (j+oct), 0 of 162); the N-count route on the
  65 "no exit chain" / 20 "no boot chain" (0 of 87 -- identification, not
  chains); more search budget on the 5 "no second exit chain" (a checker
  gap: SCycR has no entry offset -- boarding them means extending
  LapDecider.v with soundness + corruption tests, or hand boards).

THEN, in ranked order (all independent of the above):

  (1) 105 "no interior chain" -- the second-largest bucket and the most
      shape-diverse: QUAD 41, AFFINE/AFFINE 14, HIGHER 13, PARITY-AFFINE 13,
      EXP3 10, EXP2 8, EXP4 6.  The 41 QUAD/QUAD are the largest population in
      the whole residue that has never had a design pass -- a quadratic
      interior AND overflow, outside the affine certificate model.
      Bounce_8.v's MeasureGlue nesting is the precedent.  The 13
      PARITY-AFFINE are IN model after the m=2 re-index (j = 2i+r), but
      wave-14 measured only ~3 of the 13 derive both branches naively, so do
      not oversize it.

  [(2) the 15 no-visit-witness machines: DONE, wave-23.  The build was NOT
      the symbol-aware invariant WAVE16 6b predicted -- the lap chains
      already model the forward behavior exactly, so "StA never fires after
      the boot" is recomputed from them by vm_compute (Checkers/LapAvoid.v +
      Counters/LapGlueQuiet.v, emitter route `avoid`, boards LAPQ_*).  If a
      future bucket has quiet-StB/C/D lap families, the same route takes
      them with emitter work only.]

  (3) The 239 no-anchor machines.  alphabet_infer.py + gen_alphabet.py INFER a
      counter's word family from its own tape as a triple (A,B,C) and generate
      a PROVED Coq module; 21 families are wired.  They may or may not be
      EXP2 once decodable -- and if they are, the wave-18 machinery takes them
      with no new theory.

DO NOT RETRY (measured; grids in COUNTER_CLOSEOUT.md section 5, WAVE12 section
8, WAVE13 sections 4 and 8, WAVE14 section 7, WAVE15 section 5, WAVE16 section
5, WAVE18 section 5):
  * mxdys' Inductive and RWLAcc deciders on this residue.  Inductive decides
    12 of 1,176 at default config; RWLAcc 0 of 7; RRBA fails all 40 of our own
    IXP_* boards at mxdys' own parameters.  And their top-level theorem is
    `~halts`, which moves D_remaining by ZERO without the Stage 1-3 liveness
    bridge.  Harness kept in tools/mxdys/ if you need it.  THE ONE LIVE LEAD
    IS UNCHANGED and is now much less urgent than it was: config_SBC (the
    sync bouncer counter) with the state pairs taken from our two laps rather
    than swept 4x4 blind.  Wave-18 boarded 225 of the class it targets with
    our own machinery, so run it as a MEASUREMENT if at all.
  * Building BB42.v / Individual42.v to run their deciders.
  * The "states visited" variant of wsteps_frame/cycL/cycR for the quiet-state
    bucket (WAVE13 section 6).
  * emit_graycert.py for new boards; NGramHist/NGramCPS liveness over this
    residue at any (k,n,t); RepWL over the counter core; more per-machine lap
    emitters; ripple ulen widening.
  * Maximal-only window cuts in the chain search -- must be target-aware.
  * Reaching an anchor's syntactic form by rotations alone -- impossible in
    principle; the constant offset needs SFold.
  * Widening the ENCODING table hoping for boards.  Wave-14 INFERRED 18
    alphabets from tapes and it bought 9 boards against 234 machines decoded.
  * Peeling the overflow block to fix the wall -- tried, 0 of 385.
  * enc_src/enc_dst from two ENCDATA rows to break the overflow wall.
  * A HEAD-RELATIVE frame decode as a test of a frame hypothesis -- use
    absolute column parity (frame_probe.py, spacetime.py).
  * Believing a negative from an emitter run that RAISED.  Survey with
    wall_survey.py, which keeps the best outcome per machine, first.

TWO STANDING LESSONS, both earned by a wave that spent itself relearning them:
  * When a population is "in model but the search cannot find it", check what
    the search is being asked to PROVE before widening it (wave-16).
  * When that fix lands as a defaulted FLAG, grep every caller of the function
    -- not just the one that motivated it (wave-18).  nestboot.py was written
    one wave before the flag existed, in the same tree, by the same track, and
    two waves of "the boot is not a search problem" were spent on it.

WHEN STUCK ON A CLASS: print a few machine strings WITH AN ABSOLUTE-COORDINATE
TAPE DUMP (tools/counters/spacetime.py) and ask John.  Hand-inspection is
22-for-22 across waves 8-14.  ASK EARLY, ask with a TAPE, and ask about a
CLASS not a machine.

DEFERRED TO STABLE HARDWARE: census fold-in (gen_proven.py + Deferred regen +
make census-verify + census_cache --update) -- batch once, it is the only step
that lowers D_census.  Also CloseoutFinal.v, which loads the committed census
.vo and so cannot be built in a container (OCaml 4.14.2 vs 4.14.1 -- see
WAVE16 section 4b; it is not a proof failure).  Also the champion
1RB1LD_1RC1RB_1LC1LA_0RC0RD and the carry-shifted one-off
0RB1LC_1LC0LC_0RD1LA_1RD1RB.

Commit + push per validated batch.  Name new files so they cannot clash with a
concurrent session's (waves 10-18 used ILS1_*/ILS4_*/ILS4F_*, ILS1M_*/ILS4M_*/
ILS4FM_*, IXP_*/IXPM_*, WLS_*/WLSM_*, WLJ_*, LAPC_*, LAPG_*, NLAP_*, Alph_*;
wave-23 LAPQ_*; wave-24 CASC_*).
```
