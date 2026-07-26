# Next-session prompt — burn down the residue with an EXACT LAP DECIDER

_Rewritten 2026-07-26 at the end of wave-12 (branch
`claude/residue-reduction-4-2-cont-29bbkn`).  Wave-12 boarded 205 machines with
per-machine emitters and then measured that the approach has the wrong
exponent; the full record is `docs/WAVE12_FINDINGS.md`.  Paste-ready below._

**Before pasting, check:** substitute the branch the session should develop on,
and name any files a concurrent session owns.

---

```
Continue the (4,2) residue reduction in carrino/Coq-BBB4, on a new branch off
main.

READ FIRST, in this order:
  docs/WAVE12_FINDINGS.md   -- what landed, and the four things wave-12 got
                               WRONG (section 4).  Do not repeat them.
  docs/WHY_NO_HAMMER.md     -- the measurement that decides the architecture.
  docs/COUNTER_CLOSEOUT.md sections 0 and 5 -- why counters resist lossy
                               deciders, and the measured do-not-retry grids.
  docs/CLOSEOUT_ROUTE_A.md  -- how boards become D_remaining shrinkage.

ENV: apt coq 8.18.0 -- `apt-get install -y coq`, then
`coqc -native-compiler no -Q theories BBB4 <file>`.  No opam bootstrap.  Build
a checker's dependency closure by coqdep-ordering its deps and compiling them
individually; `make all` pulls in the census.

NON-NEGOTIABLE: never touch theories/Census/; `python3 tools/census_cache.py
--check` must stay MATCH.  A board counts only when its file compiles and
`Print Assumptions` shows functional_extensionality_dep only (LapDecider
itself is currently axiom-FREE -- keep it that way).  Everything under tools/
is UNTRUSTED; the kernel re-checks every board.

STATE: 3,771 of the frozen 5,156 settled (73.1%); D_remaining = 1,385.
The route-A closeout is built and kernel-verified: after a wave of boards,
run `make closeout` (inventory -> gen_stages -> audit -> compile) and
D_remaining shrinks by exactly what you boarded.

WATCH OUT -- a build trap wave-12 hit: `gen_stages.py` syncs only the
theories/Closeout/ section of _CoqProject.  New board files must be added to
_CoqProject separately or `make closeout` dies with "No rule to make target".
Wave-12 found 533 boards unlisted, including all of wave 10/11.  FIRST TASK
(10 minutes): make gen_stages.py add every board file it references to
_CoqProject automatically, so this never recurs.

THE TASK -- finish theories/Checkers/LapDecider.v, the exact lap decider.

  WHY THIS AND NOT ANOTHER EMITTER.  Measured in WHY_NO_HAMMER.md: the
  NGramHist closure ALWAYS closes but the q-avoiding subgraph the liveness
  certificate needs stays CYCLIC at every precision (k=2..6, n=2..3), because
  a counter's carry after ~2^k steps is invisible to any finite window.  So
  exactness is required -- but waves 8-12 paid one hand-authored theorem per
  machine (five emitters, ~500 boards against a 1,385 residue) and that is the
  wrong exponent.  mxdys proves one soundness theorem and every machine costs
  a run; we must do the same.

  WHAT IS ALREADY THERE (compiles, closed under the global context):
    - sside := (pre, u, (a,b), post) denoting pre ++ rep u (a*j+b) ++ post,
      with sden;  this shape covers EVERY lap chain the five emitters derive
    - sconf + cden
    - lstep: SWin (framed window) | SCycL | SCycR
    - scycL_sound / scycR_sound  (WTape.cycL/cycR at affine counts)
    - LapStep -- the obligation glue_neverqh already consumes
    - ChainSound + ChainSound_trans/refl

  WHAT TO BUILD, in order:
    1. SWin soundness: the window entry must be concrete, so it frames
       against wsteps_frame / wsteps_frame_l / wsteps_frame_r off the
       PREFIXES of both sides.  This is the fiddly one -- do it first.
    2. A boolean checker `lap_check : TM -> lapcert -> bool` that runs the
       chain symbolically on both cview branches and verifies it lands on the
       successor anchor.
    3. The single soundness theorem
       `lap_check tm c = true -> LapStep tm (Cf c)`, then compose with boot +
       visits through glue_neverqh.
    4. Per-machine cost is then a vm_compute.  Port the five emitters to EMIT
       CERTIFICATES instead of proof scripts (they already derive exactly this
       data -- emit_shape1/shape4/ixp/wall/wallj).

  ENCODINGS ARE DIGIT ALPHABETS, NOT EMITTER FORKS.  Ip/Jp (marker before),
  Kp (none), Dp (doubled), Mp (marker AFTER -- new in wave-12,
  theories/Counters/MpCounter.v, 202 residue machines with affine slope-4
  interiors).  Mp differs from Ip by a ONE-CELL FRAME SHIFT, which is why Ip
  recognizers half-fire on it.  SEARCH encoding x frame offset x tail at
  derive time; wave-12 hard-coded them and discovered five encodings one at a
  time, two of them only because a human read the tape.

CHECKPOINT: SWin soundness proved and one existing board (pick an ILS4_* --
the simplest chain) re-derived as a certificate that lap_check accepts.  That
proves the architecture end to end before any bulk work.

THEN, in order:
  (2) port emit_shape4 + emit_ixp to certificate emission; re-run over
      tools/closeout/frozen_unproven.txt and `make closeout`.
  (3) the widening-counter family (docs/UNCERTAIN_MACHINES.md section 1):
      counters that skip values (2^K-1 -> 2^(K+1)), so Pos.succ is the wrong
      successor.  glue_neverqh is ALREADY generic in Cf, so this needs only a
      reindexed anchor family -- either an enumeration of the odd-bit-length
      values (reuses every Ip lemma) or a word fixpoint in the ILCounter
      style.  Default to the enumeration unless the human says otherwise.
  (4) the 673 machines with NO anchor family at all -- the largest unknown.
      Triage (triage.py fingerprint + lapshape) before assuming anything;
      wave-12's section 4.1 mistake was concluding structure from a failing
      search.
  (5) the 27 genuine mxdys holdouts (tools/census_holdouts_kept.txt) -- the
      real endgame, once per-machine cost is a vm_compute.

DO NOT RETRY (measured; grids in COUNTER_CLOSEOUT.md section 5 and WAVE12
section 8): NGramHist/NGramCPS liveness over this residue at any (k,n,t);
RepWL over the counter core; more per-machine lap emitters; emitter
anchor-search widenings; Ip-encoding-alone; ripple ulen widening; assuming the
lapshape signature gates templates; assuming affine-vs-exponential overflow is
uniform within a shape.

DO NOT BUILD ON: docs/NGHIST_WAVE7.md section 0 (the "<=7 vs all-8
transitions, outside mxdys' enumeration" story).  The human says it is bad
info; there is no separate list of machines mxdys skipped, just the complement
of the 3,713 holdouts.  Re-derive before relying on it.

DEFERRED TO STABLE HARDWARE: census fold-in (gen_proven.py + Deferred regen +
make census-verify + census_cache --update) -- batch it once, it is the only
step that lowers D_census.  Also the champion 1RB1LD_1RC1RB_1LC1LA_0RC0RD
(needs `exists B, QHBound B` plus a 32.8M-step prefix) and the carry-shifted
one-off 0RB1LC_1LC0LC_0RD1LA_1RD1RB (anchor Cc (p, k) with a frame offset).

WHEN STUCK ON A CLASS: print a few machine strings and ask the human.
Hand-inspection is now 15-for-15 across waves 8-12 -- in wave-12 the human
correctly diagnosed a mis-set anchor, identified a whole new encoding (Mp)
from one tape reading, and rejected two of my framings that the measurements
then confirmed were wrong.  Ask EARLY; it is the highest-yield move available.

ALSO WORTH DOING ONCE: WAVE9_FINDINGS.md section 7 says "ask mxdys for the
implementation before rebuilding it".  If mxdys' inductive decider already
covers bouncers and counters, that is this same checker written and debugged.
Ask before spending sessions reconstructing it.

Commit + push per validated batch.  Name new files so they cannot clash with a
concurrent session's (waves 10-12 used ILS1_*/ILS4_*/ILS4F_*, ILS1M_*/ILS4M_*/
ILS4FM_*, IXP_*/IXPM_*, WLS_*/WLSM_*, WLJ_*).
```
