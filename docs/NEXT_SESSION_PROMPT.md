# Next-session prompt — THE TASK is half done; the other half is a MEASUREMENT

_Rewritten 2026-07-27 at the end of the wave-18 RESIDUE track (branch
`claude/coq-bbb4-residude-oy73r4`), which took THE TASK — the exponential
overflow, the `AFFINE`/`EXP2` bucket, 500 of the 883 — and **boarded 258 of
them**.  With the concurrent HOLDOUTS track merged (which CLOSED the (4,2)
holdout list: wave4 #15, fractal #3/#5, tower #20), `D_remaining` is **622**
and 4,534 of the frozen 5,156 are settled (87.9%).  Full assessment: `docs/WAVE18_FINDINGS.md` — §2 is why it took
three waves, §4b is the measurement that names the next 130 machines, §5 is
the one do-not-retry, §6 is the lesson._

_**Scope: the RESIDUE only** — and as of this merge that is not a restriction
but a description: the (4,2) HOLDOUT list is CLOSED, so the residue is all
that is left._

**Before pasting, check:** substitute the branch the session should develop
on, and name any files a concurrent session owns.

---

```
Continue the (4,2) residue reduction in carrino/Coq-BBB4, on a new branch off
main.

READ FIRST, in this order:
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

STATE: 4,534 of the frozen 5,156 settled (87.9%); D_remaining = 622.
THE HOLDOUTS ARE DONE -- the (4,2) holdout list CLOSED on 2026-07-27 (wave4
#15, fractal #3/#5, tower #20).  Everything left is RESIDUE, and it is all
yours.

Failure profile, measured at D_remaining = 625 (i.e. before the 3 holdout
boards merged in; they are not residue rows and change none of it) by running
  python3 tools/counters/emit_lapcert.py --list tools/closeout/frozen_unproven.txt --json OUT
(3 shards, ~20 min; the run also tells you the nested route's verdict per
machine).  Cross-referenced against ovfshape.py over the same list:

  185  no inner family at pow2 j   -- 162 AFFINE/EXP2, 23 AFFINE/AFFINE
  211  no overflow phase           -- ALL of them the no-anchor bucket
  105  no interior chain           -- QUAD 41, HIGHER 13, PARITY-AFFINE 13,
                                      EXP3 10, EXP4 6, AFFINE/AFFINE 14, EXP2 8
   65  no exit chain               -- MEASURED EXPONENTIAL, and the two-count
                                      route did NOT reach these
   28  no anchor
   22  no boot chain               -- MEASURED EXPONENTIAL on 14 of 16
   15  no visit witness (StA)
    8  no shift chain              -- has a second family, no chain into it
    5  no second exit chain
    4  no inner interior chain
ovfshape over the whole 625-machine list, for shape rather than blocker:
  242 AFFINE/EXP2, 239 no-anchor, 52 AFFINE/AFFINE, 41 QUAD, 13 PARITY-AFFINE,
  13 HIGHER, 10 EXP3, 9 AFFINE/HIGHER, 6 EXP4.
Per-machine cost is a vm_compute:
  python3 tools/counters/emit_lapcert.py --list FILE --emit   (25 alphabets)
After a wave, inventory.py + gen_stages.py + audit.py shrink D_remaining by
exactly what you boarded, in minutes.

THE TASK -- FINISH THE NESTED LAP, AND IT IS AN IDENTIFICATION PROBLEM.

  258 of the 500 AFFINE/EXP2 machines are boarded -- 225 with ONE inner count
  and 33 with TWO (the sync-bouncer shift; Counters/NestedLap2.v).  Of the
  242 that are not:

     65  "no exit chain"  -- the exit is EXPONENTIAL (0 AFFINE of 24 sampled)
                             AND the second-count search does not reach them
    134  "no inner family at pow2 j"
     22  "no boot chain"  -- the boot is EXPONENTIAL (14 EXP of 16 with a key)
      8  "no shift chain" / 5 "no second exit chain" -- these DO have the
                             second family; only a chain is missing, so they
                             are the cheapest 13 on the board

  An sside carries a*j + b, so an exponential half is UNREPRESENTABLE as one
  chain.  Do NOT widen derive_chain for these; that is now measured twice over
  (WAVE16 section 5, and this).  What is wrong is the INNER FAMILY'S
  IDENTIFICATION -- and WAVE18 section 4c already found what it is:

    SPLIT ONE OVERFLOW PHASE AT THE FIRST INNER ALL-ONES FILL AND SEARCH THE
    SECOND HALF ON ITS OWN.  11 OF 16 SAMPLED CARRY A SECOND CONSECUTIVE
    2^(K-1)..2^K-1 FAMILY THERE -- same state, same alphabet, SHIFTED TAIL
    (e.g. Jp@B tail=[S1;S1;S0], then Jp@B tail=[S0;S0;S1]).

  That is John's reading of mxdys' sync bouncer counter, verbatim: "count
  8->15, shift, count 8->15 again".  The overflow phase is

      boot -> count -> SHIFT -> count -> exit

  five affine chains and TWO exponential inner runs, not three and one.

  THAT IS BUILT (Counters/NestedLap2.boot_via_fill, 12 lines, and it boarded
  33).  IT NEEDED NO NEW COMPOSITION THEOREM.  NestedLapLift.nested_overflow_lift's Hboot is an
  ARBITRARY csteps run into Cin v0 -- it does not have to be one chain.  So
  instantiate the theorem at the SECOND inner family and build its boot as
  boot1 ++ inner_to_fill_lift(Cin1) ++ mid.  The emitter work is one more
  family search and one more chain; nestcert.py already returns the phase's
  `mid` list, so the split costs nothing to reproduce.  Worth ~76 of the 111
  at the sampled rate, and the same construction should absorb part of the 22
  exponential boots (a count BEFORE the identified one is the mirror image of
  a count after it).

  If a machine has NEITHER (5 of the 16 had nothing after the fill): dump the
  phase in absolute coordinates (tools/counters/spacetime.py) and ASK JOHN
  with the tape.  Hand-inspection is 22-for-22 across waves 8-14.  Cluster
  first (wall_survey.py / alphabet_infer.py) so one reading covers many.

  The 134 "no inner family" are the same population seen from the other side,
  and Stage A already sized them: 21% of inner counters run at another octave
  or offset.  Both the search and the glue (epow2_, gbo_) hard-wire
  v0 = pow2 j.

  DO NOT RETRY (measured in wave-18): a wider inner-key tail.  maxtail = 6
  FINDS families -- 13 of 40 machines that report "no inner family" at 3 --
  and boards ZERO of them; the 33 it unlocks all fail on the boot or exit
  chain.  Key counts are 0-4, so maxkeys was never binding either.
  tools/counters/nestcert.py MAXTAIL records this.

THEN, in ranked order (all independent of the above):

  (1) 105 "no interior chain" -- now the second-largest bucket and the most
      shape-diverse: QUAD 41, AFFINE/AFFINE 14, HIGHER 13, PARITY-AFFINE 13,
      EXP3 10, EXP2 8, EXP4 6.  The 41 QUAD/QUAD are the largest population in
      the whole residue that has never had a design pass -- a quadratic
      interior AND overflow, outside the affine certificate model.
      Bounce_8.v's MeasureGlue nesting is the precedent.  The 13
      PARITY-AFFINE are IN model after the m=2 re-index (j = 2i+r), but
      wave-14 measured only ~3 of the 13 derive both branches naively, so do
      not oversize it.

  (2) The 15 no-visit-witness machines.  WAVE16 section 6b is still the
      analysis and it is still right: these are quasi-halters whose quiet
      state is StA (last visit at step 4-11, simulated), they miss glue_qh
      (StA IS targeted) and glue_qh_abs (closed_b is a DIGRAPH fact, so any
      set holding StD holds StA), and what is actually true is symbol-aware --
      StD never READS S1 after the boot.  That is a real build, the bound is
      tiny (QHBound 12 covers all 15), and vis_via_int_lift is NOT it (built,
      fires on none).

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
ILS4FM_*, IXP_*/IXPM_*, WLS_*/WLSM_*, WLJ_*, LAPC_*, LAPG_*, NLAP_*, Alph_*).
```
