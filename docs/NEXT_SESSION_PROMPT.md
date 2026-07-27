# Next-session prompt — THE TASK is half done; the other half is a MEASUREMENT

_Rewritten 2026-07-27 at the end of the wave-18 RESIDUE track (branch
`claude/coq-bbb4-residude-oy73r4`), which took THE TASK — the exponential
overflow, the `AFFINE`/`EXP2` bucket, 500 of the 883 — and **boarded 225 of
them**.  `D_remaining` is **658**; 4,498 of the frozen 5,156 are settled
(87.2%).  Full assessment: `docs/WAVE18_FINDINGS.md` — §2 is why it took
three waves, §4b is the measurement that names the next 130 machines, §5 is
the one do-not-retry, §6 is the lesson._

_**Scope: the RESIDUE only.**  John runs the 4 remaining (4,2) holdouts in
dedicated sessions — that front is out of scope, and the residue is the whole
job._

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

STATE: 4,498 of the frozen 5,156 settled (87.2%); D_remaining = 658.
THE HOLDOUTS ARE NOT YOURS.  Do not open that front, do not sweep
tools/census_holdouts_kept.txt.

Failure profile, measured at D_remaining = 658 by running
  python3 tools/counters/emit_lapcert.py --list tools/closeout/frozen_unproven.txt --json OUT
(3 shards, ~20 min; the run also tells you the nested route's verdict per
machine).  Cross-referenced against ovfshape.py over the same list:

  265  no inner family at pow2 j   -- 162 AFFINE/EXP2, 23 AFFINE/AFFINE
  211  no overflow phase           -- ALL of them the no-anchor bucket
  111  no exit chain               -- AFFINE/EXP2; MEASURED EXPONENTIAL
  105  no interior chain           -- QUAD 41, HIGHER 13, PARITY-AFFINE 13,
                                      EXP3 10, EXP4 6, AFFINE/AFFINE 14, EXP2 8
   28  no anchor
   22  no boot chain               -- MEASURED EXPONENTIAL on 14 of 16
   15  no visit witness (StA)
    4  no inner interior chain
ovfshape over the whole 658-machine list, for shape rather than blocker:
  275 AFFINE/EXP2, 239 no-anchor, 52 AFFINE/AFFINE, 41 QUAD, 13 PARITY-AFFINE,
  13 HIGHER, 10 EXP3, 9 AFFINE/HIGHER, 6 EXP4.
Per-machine cost is a vm_compute:
  python3 tools/counters/emit_lapcert.py --list FILE --emit   (25 alphabets)
After a wave, inventory.py + gen_stages.py + audit.py shrink D_remaining by
exactly what you boarded, in minutes.

THE TASK -- FINISH THE NESTED LAP, AND IT IS AN IDENTIFICATION PROBLEM.

  225 of the 500 AFFINE/EXP2 machines are boarded.  Of the 275 that are not,
  ~275 - 8 - 2 = 265 fail for exactly three reasons, and WAVE18 section 4b
  measured what is behind two of them:

    111  "no exit chain"  -- the exit is EXPONENTIAL (0 AFFINE of 24 sampled)
     22  "no boot chain"  -- the boot is EXPONENTIAL (14 EXP of 16 with a key)
    134  "no inner family at pow2 j"

  An sside carries a*j + b, so an exponential half is UNREPRESENTABLE as one
  chain.  Do NOT widen derive_chain for these; that is now measured twice over
  (WAVE16 section 5, and this).  What is wrong is the INNER FAMILY'S
  IDENTIFICATION, and NESTED_LAP_PLAN section 3 predicted the mechanism:

      innerfam requires the decoded values to be exactly 2^(K-1)..2^K-1, and
      a SUBSEQUENCE of a longer count satisfies that too.

  An exponential EXIT says the inner counting does not STOP at fill(pow2 j) --
  there is more after it.  An exponential BOOT says it did not START at
  pow2 j.  So the concrete next move, in order:

    1. Dump one overflow phase in absolute coordinates
       (tools/counters/spacetime.py) for three or four of the "no exit chain"
       machines and read where the inner count actually begins and ends.
       ASK JOHN with the tape -- hand-inspection is 22-for-22 across waves
       8-14, and this is exactly the kind of question it answers.  Cluster
       first (wall_survey.py / alphabet_infer.py) so one reading covers many.
    2. If the inner run really is longer than one octave, the fix may be free:
       NestedLapLift.nested_overflow_lift is stated GENERICALLY in Cin and
       should compose with itself, i.e. a THIRD level costs no new theory.
       Measure before building -- that is what section 4b is for.
    3. The 134 "no inner family" are the same population seen from the other
       side, and Stage A already sized them: 21% of inner counters run at
       another octave or offset.  Both the search and the glue (epow2_, gbo_)
       hard-wire v0 = pow2 j.

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
