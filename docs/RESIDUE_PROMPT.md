# Residue prompt — the nested front is spent down to its measured blockers

_Refreshed 2026-07-29 at the end of the wave-26 track (branch
`claude/residue-reduction-4-2-dpb65q`), which boarded the LAST 4 octave-down
rows -- the ones whose closing count enters one value in, at `xI (pow2 j)` --
and so **spent the cascade route**: all 69 machines that gate are boarded.
`D_remaining` **431 -> 427**.  `docs/WAVE26_FINDINGS.md`; section 3 is the
re-measurement of the 17 rows the bucket has left and section 4 the one thing
still untried on the largest of them.  Before it, wave-25
(branch `claude/cascade-counter-merge-issue-ki8ulc`) boarded ALL 57
gated cascade machines (`CASB_*`, every one accepted on the first render,
funext-only) AND 8 of the 12 octave-down rows (the whole cascade sits one
octave down; the close is one more ASCENDING count at octave j+1 between
two affine chains -- WAVE25 section 7): `D_remaining` **496 -> 431**.  `docs/WAVE25_FINDINGS.md`.  Before it,
wave-24 (branch `claude/residue-reduction-cascade-yhqvj4`, PR #54) closed
the cascade gate and built the route end to end -- extractor, level
induction, emitter -- but boarded nothing (`docs/WAVE24_FINDINGS.md`); and
the wave-23 RESIDUE track (branch `claude/residue-list-refinement-cxzdax`)
boarded the whole
15-machine "no visit witness (`StA`)" bucket by the state-AVOIDANCE route:
the kernel recomputes from the SAME lap chains that no window step is ever
in `StA` (`Checkers/LapAvoid.v`, axiom-free), and
`Counters/LapGlueQuiet.v` turns that plus a checked bootstrap window into
the R_QH triple with the exact last-visit bound.  `D_remaining` is **427**
and 4,729 of the frozen 5,156 are settled (91.7%).  Full assessments:
`docs/WAVE26_FINDINGS.md`, `docs/WAVE25_FINDINGS.md`, `docs/WAVE23_FINDINGS.md`,
`docs/WAVE22_FINDINGS.md`; the wave-18 story is
`docs/WAVE18_FINDINGS.md`._

_**Scope: the RESIDUE, which is now everything.**  The (4,2) HOLDOUT list was
closed on 2026-07-28 when tower #20 was boarded (`NEXT_SESSION.md` §2l), so
these 431 rows are the entire remaining problem.  `docs/RESIDUE_MAP.md` maps
them by shape and blocker._

**Before pasting, check:** substitute the branch the session should develop
on, and name any files a concurrent session owns.

---

```
Continue the (4,2) residue reduction in carrino/Coq-BBB4, on a new branch off
main.

READ FIRST, in this order:
  docs/WAVE26_FINDINGS.md   -- THE TASK's state, all of it; it is short.  The
                               CASCADE ROUTE IS SPENT: all 69 machines that
                               gate are boarded (CASB_*).  Section 3 is the
                               re-measurement of the 18 rows the bucket has
                               left, in three named sub-families; section 4
                               is the one thing still untried on the largest
                               of them (10 rows) and section 6 is what this
                               wave measured NEGATIVE.  Section 5 answers
                               "are the halting-transition machines easier"
                               with numbers: yes, and already spent.
  docs/WAVE25_FINDINGS.md   -- the boarding wave behind it.  The 57 gated
                               cascade machines AND 8 of the 12 octave-down
                               rows; the route is a full third route in
                               emit_lapcert/cascade_emit.  Section 7 is the
                               octave-down shape, which wave-26 finished.
  docs/WAVE24_FINDINGS.md   -- the build behind it: the gate, the level
                               induction (theories/Counters/
                               NestedLapCascade.v), the framing search.
                               Section 7 has the cascade do-not-retries.
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

NON-NEGOTIABLE: never touch theories/Census/; `python3 tools/census_cache.py
--check` must stay MATCH.  A board counts only when its file compiles and
`Print Assumptions` shows functional_extensionality_dep only (LapDecider,
LapCertGlue, LapGlueAbs, NestedLap and NestedLapLift are axiom-FREE or
funext-only -- keep them that way).  Everything under tools/ is UNTRUSTED;
the kernel re-checks every board.

STATE: 4,729 of the frozen 5,156 settled (91.7%); D_remaining = 427.
THE HOLDOUT LIST IS CLOSED.  Everything left is RESIDUE and all of it is
yours.  docs/RESIDUE_MAP.md + tools/closeout/residue_map.tsv give every
remaining machine's measured lap shape and the exact blocker (the tsv is
wave-23's measurement; subtract the 69 CASB_* boards from its
no-exit/no-boot rows).

Failure profile at D_remaining = 427 (residue_map.tsv minus waves 25-26):

  211  no overflow phase           -- ALL of them the no-anchor bucket
  105  no interior chain           -- QUAD 41, HIGHER 13, PARITY-AFFINE 13,
                                      EXP3 10, EXP4 6, AFFINE/AFFINE 14, EXP2 8
   60  no inner family at pow2 j   -- what SURVIVED the offset/split/refill
                                      routes; 32 have no family under any
                                      route, the rest fail an offset chain
   18  the CASCADE's non-gated     -- was "65 no exit chain + 22 no boot
                                      chain"; the route is SPENT, all 69 that
                                      gate are boarded (CASB_*).  Of the 18:
                                      17 one/two-count phases -- re-measured
                                      in WAVE26 section 3 as three sub-
                                      families, 10 + 4 + 3, ALL of them
                                      `no boot chain` -- and 1 main count
                                      at 4..7
   24  no anchor
    5  no second exit chain        -- the SCycR-entry-offset checker gap,
                                      measured precisely (WAVE22 section 2b)
    4  no inner interior chain
(211+105+60+18+24+5+4 = 427, and this profile is now regenerated: it is the
427 rows of tools/closeout/frozen_unproven.txt joined against residue_map.tsv,
not the wave-23 numbers with boards subtracted by hand.  The 15 "no visit
witness (StA)" rows were boarded in wave-23 -- the AVOID route, LAPQ_*; the
69 cascade rows in waves 25-26 -- CASB_*)
Per-machine cost is a vm_compute:
  python3 tools/counters/emit_lapcert.py --list FILE --emit   (25 alphabets)
After a wave, inventory.py + gen_stages.py + audit.py shrink D_remaining by
exactly what you boarded, in minutes.

THE TASK (re-ranked 2026-07-29 after wave-26 SPENT the cascade route --
  all 69 gating machines boarded, CASB_*, docs/WAVE26_FINDINGS.md; the route
  is a full third route in the emitter, tried automatically after
  flat/nested/offset):

  (0) THE CASCADE's 18 NON-GATED, re-measured (WAVE26 section 3).  All 17 of
      the one/two-count rows are `no boot chain`, in three sub-families:
        * 10  TWO counts one octave apart, under TWO DIFFERENT alphabets
              (Alph_01_11_011 tail 11, then Alph_10_11_1 = Ip tail 1).  The
              FIRST count sits one octave DOWN, which is why families() --
              floored at oct >= 0 -- never offers it and the boot is searched
              into the second count instead.  THIS IS THE BEST LEAD IN THE
              BUCKET and wave-26 took it two steps: with the floor lifted the
              octave-down family is found on all 10, and the BOOT CHAIN INTO
              IT DERIVES ON ALL 10 under _frame_pair -- identically, at
              peel (1,0) post 6, cost 4*i+6, EXACT.  So they are neither an
              identification nor a boot failure.  WHAT IS LEFT is the SHIFT
              chain (octave-down fill -> the octave-0 count's start), and it
              is NOT a search-budget problem: 0 at peel <= 3 / split <= 14
              AND 0 at peel <= 8 / split <= 30 (378 framings each).  It has
              to RE-ENCODE a j-length word from one digit alphabet into
              another (Alph_01_11_011 -> Ip) across ~66 configurations -- a
              pass over the whole word, which a single-index window chain
              cannot be at any framing.  Naming that piece is the design
              question; do NOT widen further and do NOT go back to
              alphabets.  Note that when it lands, the octave-down count is
              j-1 blocks and needs the j = S j' reindex, which the low
              cascade route already builds (cview_none_shape + lapz_/visz_).
        *  4  one 5-value count (12..16) spanning the whole phase with a
              GROWING far side -- a distinct unsolved shape.
        *  3  one span decoded at five octaves (nested SHADOWS, not five
              counts); two of the three measure overflow HIGHER, so they are
              not in the exponential-counter model at all.
      Plus 1 main count at 4..7.  `cascade_probe.py --gate` re-gates the
      bucket; `cascade_emit.py --boards FILE` boards whatever newly gates.
      Also point cascade_probe at the 60 "no inner family" survivors and the
      EXP3/EXP4/HIGHER interiors (a deeper cascade is exactly what a
      Theta(3^j) lap smells of) -- both still untouched.

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
  * The MACHINES WITH A HALTING TRANSITION as a batch (wave-26 section 5).
    One fewer reachable transition IS easier for this machinery -- 97.1% of
    the 1,537 frozen `---` machines are settled against 89.4% of the rest --
    but that is exactly why only 45 are left, 10.5% of the residue against
    29.8% of the frozen set, spread over the same buckets with no sub-route.

THREE STANDING LESSONS, each earned by a wave that spent itself relearning it:
  * WHEN A TRANSITION TRACES BUT DOES NOT DERIVE, PEEL BEFORE ANYTHING ELSE.
    (peel, split) is the search space, and ONE peeled unit copy has now been
    the whole difference three times running: B->A in wave-24, the
    octave-down boot in wave-25, and the 10 two-count rows' boot in wave-26
    (0 of 10 unframed, 10 of 10 at peel (1,0)).  Do not reach for alphabets,
    octaves or new theory until _frame_pair has been run.
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
wave-23 LAPQ_*; wave-24 CASC_*; wave-25 CASB_*).
```
