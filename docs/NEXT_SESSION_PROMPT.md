# Next-session prompt — the exponential overflow is the endgame

_Rewritten 2026-07-26 at the end of wave-15 (branch
`claude/coq-residue-inductive-deciders-bzz3ae`).  Wave-15 ran the mxdys Stage-0
gate and got a clear NO (12 of 1,176, and `~halts` boards nothing), then took
the quasi-halting bucket with a much smaller theorem than planned — 141 boards,
`D_remaining` 1,176 → 1,035.  Full assessment: `docs/WAVE15_FINDINGS.md`.
Paste-ready below._

**Before pasting, check:** substitute the branch the session should develop on,
and name any files a concurrent session owns.

---

```
Continue the (4,2) residue reduction in carrino/Coq-BBB4, on a new branch off
main.

READ FIRST, in this order:
  docs/WAVE15_FINDINGS.md   -- sections 2, 3 and 4.  Section 2 is why mxdys'
                               deciders are now do-not-retry (measured, not
                               assumed).  Section 3 is the absorbing-set
                               closer, which retired a planned multi-day
                               build.  Section 4 is THE TASK: ~750 of the
                               remaining 1,035 are one problem.
  docs/WAVE14_FINDINGS.md   -- section 3 only: the overflow wall is
                               EXPONENTIAL, measured three ways.
  docs/LAPDECIDER.md        -- our checker's design, and why the model is
                               AFFINE in the carry index.  That affineness is
                               the binding constraint -- read it as a limit.
  docs/CLOSEOUT_ROUTE_A.md  -- how boards become D_remaining shrinkage.

ENV: apt coq 8.18.0 -- `apt-get install -y coq`, then
`coqc -native-compiler no -Q theories BBB4 <file>`.  No opam bootstrap.  The
Counters+Checkers .vo closure is 44 files and builds in ~30 s; `make all`
pulls in the census, so don't.

NON-NEGOTIABLE: never touch theories/Census/; `python3 tools/census_cache.py
--check` must stay MATCH.  A board counts only when its file compiles and
`Print Assumptions` shows functional_extensionality_dep only (LapDecider,
LapCertGlue and LapGlueAbs are axiom-FREE -- keep them that way).  Everything
under tools/ is UNTRUSTED; the kernel re-checks every board.

STATE: 4,121 of the frozen 5,156 settled (79.9%); D_remaining = 1,035.
Failure profile over the residue (tools/counters/wall_survey.py):
  510  anchor + interior derive, OVERFLOW fails
  354  anchor derives, INTERIOR fails
   21  no anchor family at all
    6  complete lap, no visit witness
Per-machine cost is a vm_compute:
  python3 tools/counters/emit_lapcert.py --list FILE --emit   (24 alphabets)
After a wave, inventory.py + gen_stages.py + audit.py shrink D_remaining by
exactly what you boarded, in minutes.

THE TASK -- THE EXPONENTIAL OVERFLOW, AND MEASURE BEFORE TEMPLATING.

  The two big buckets are ONE problem.  WAVE15 section 4 ran ovfshape.py over
  all 354 "no-interior" machines: 134 are AFFINE interior / EXP2 overflow, so
  they are not really blocked on the interior at all -- fixing the interior
  search moves them into the no-overflow bucket, not into a board.  Net,
  ~750 of 1,035 are gated on an overflow that costs Theta(2^j), which `sside`
  (a*j+b) and `srun` (ca*j+cb) cannot represent BY CONSTRUCTION.

  The build is WAVE14 section 6 route (1), unchanged and now unavoidable:
  teach LapDecider a NESTED LAP -- an inner anchor family run 2^j times, which
  is what the overflow physically does (WAVE14 section 2: it counts the whole
  range again in the shifted frame).  theories/Counters/IXPGadgets.v already
  carries the positive-arithmetic gadgets a hand-built instance needed
  (pow2, fill, cview_none_shape), and wave-12 boarded 163 machines of exactly
  this family BY HAND through it -- so the target shape is known-good, and the
  job is to make it a checked step rather than a per-machine proof.

  Run ovfshape.py on your candidate set before templating anything.  The
  interior version of that measurement was missing for five waves and hid a
  quadratic family; the overflow version was missing for six and hid this one.

THEN, in ranked order (all independent of the above):

  (1) The 99 AFFINE/AFFINE machines inside the no-interior bucket.  These are
      IN MODEL and the search simply fails to find the interior chain, which
      is the same shape of gap as WAVE13 section 4.1 -- where making the
      window search target-aware turned 0 chains into all of them.
      Instrument derive_chain on a few and find out why.  Best
      boards-per-hour in the residue if it is a real gap.

  (2) The 6 remaining no-visit-witness machines.  Their missing state is
      genuinely LIVE, but fires only in the INTERIOR lap, where
      LapCertGlue.vis_via_ovf cannot see it.  A vis_via_int dual -- from any
      anchor, run to an INTERIOR anchor rather than an overflow one -- would
      catch them.  Small, one theorem, and it is the honest completion of
      wave-15.

  (3) 13 PARITY-AFFINE machines are IN model -- affine on each parity class
      of j.  They need the m=2 re-index (j = 2i+r, block unit u^2).
      MEASURED in wave-14: only ~3 of the 13 derive both parity branches with
      the naive re-index, so this is worth ~3 boards.  Do not oversize it.

  (4) The 21 with NO anchor family at all.  alphabet_infer.py +
      gen_alphabet.py INFER a counter's word family from its own tape as a
      triple (A,B,C) and generate the Coq module; 18 families are wired.

  (5) The 27 genuine mxdys holdouts (tools/census_holdouts_kept.txt, of which
      22 are still in D_remaining) -- the real endgame, and what John actually
      wants to be working on.

DO NOT RETRY (measured; grids in COUNTER_CLOSEOUT.md section 5, WAVE12 section
8, WAVE13 sections 4 and 8, WAVE14 section 7, WAVE15 section 5):
  * mxdys' Inductive and RWLAcc deciders on this residue.  MEASURED in
    wave-15: Inductive decides 12 of 1,176 at default config and ~1 more per
    150 under six further configs; RWLAcc 0 of 7.  ZERO of the decided
    machines used nat_powsum -- the count language we went there for is never
    exercised, because their search never reaches a generalisable repeater on
    our machines.  And their top-level theorem is `~halts`, which moves
    D_remaining by ZERO: even a 100% sweep boards nothing without the Stage
    1-3 liveness bridge.  Harness kept in tools/mxdys/ if you need it.
    (RRBA is the one honest GAP -- its extraction stack-overflows coqc and
    vm_compute does not finish a machine in 9.5 min, so it was never run.  Do
    not record it as a negative.  If you want the number, use the Rust
    beaver/ tree or native_compute under an opam switch.)
  * Building BB42.v / Individual42.v to run their deciders.  Inductive_inf.v
    instantiates at BBinf (Q := N, Sym := N) and parses our (4,2) strings AS
    IS.  Also: BBinf.v has two Admitted lemmas, so it is a SEARCH ORACLE and
    can never be proof-grade.
  * The "states visited" variant of wsteps_frame/cycL/cycR (WAVE13 section 6)
    for the quiet-state bucket.  The absorbing-set closure in
    Counters/LapGlueAbs.v gets 141 of 149 with ONE induction.
  * emit_graycert.py for new boards -- a full run over the 1,035 reports "no
    Gray anchor" on every machine; wave-14 took all 11 there are.
  * NGramHist/NGramCPS liveness over this residue at any (k,n,t); RepWL over
    the counter core; more per-machine lap emitters; ripple ulen widening.
  * Maximal-only window cuts in the chain search -- must be target-aware.
  * Reaching an anchor's syntactic form by rotations alone -- impossible in
    principle; the constant offset needs SFold.
  * Widening the ENCODING table hoping for boards.  Wave-14 INFERRED 18
    alphabets from the tapes and it bought 9 boards against 234 machines
    decoded.  The alphabet has never been the binding constraint.
  * Peeling the overflow block to fix the wall -- tried, 0 of 385.
  * enc_src/enc_dst from two ENCDATA rows to break the overflow wall (WAVE13
    section 10c).  The wall is the overflow's COST, not its target word.
  * A HEAD-RELATIVE frame decode as a test of a frame hypothesis:
    MB(m) ++ [S1] = [S1] ++ MA(m) identically, so the verdict is an artifact of
    head position.  Use absolute column parity (frame_probe.py, spacetime.py).
  * Believing a negative from an emitter run that RAISED.  A crash in
    emit_lapcert's reporting path once cost 46 finished certificates and
    looked exactly like "the search finds nothing".  Survey with
    wall_survey.py, which keeps the best outcome per machine, before
    concluding anything.

A LESSON WORTH CARRYING (wave-15).  The quiet-state bucket had a planned
multi-day build attached to it for two waves.  What it actually needed was to
ask a DIFFERENT question: not "does the lap avoid this state" (a trajectory
fact, expensive) but "is this state still reachable at all" (a digraph fact,
one induction).  Before building a soundness layer, check whether the property
is syntactic.

WHEN STUCK ON A CLASS: print a few machine strings WITH AN ABSOLUTE-COORDINATE
TAPE DUMP (tools/counters/spacetime.py) and ask John.  Hand-inspection is
22-for-22 across waves 8-14.  In wave-14 he corrected the frame measurement
(which turned out to BE the overflow mechanism) and read a blank-separated
counter off a tape that no recognizer could see, which became a seventh
alphabet and 24 boards.  ASK EARLY, ask with a TAPE, and ask about a CLASS not
a machine: cluster with wall_survey.py or alphabet_infer.py first so one
reading covers many machines.

DEFERRED TO STABLE HARDWARE: census fold-in (gen_proven.py + Deferred regen +
make census-verify + census_cache --update) -- batch once, it is the only step
that lowers D_census.  Also the champion 1RB1LD_1RC1RB_1LC1LA_0RC0RD (needs
`exists B, QHBound B` plus a 32.8M-step prefix) and the carry-shifted one-off
0RB1LC_1LC0LC_0RD1LA_1RD1RB.  The Closeout.vo COMPILE needs the ~719-file
board .vo closure (~85 min in a fresh container); inventory.py, gen_stages.py
and audit.py all run in minutes and produce the numbers above.

Commit + push per validated batch.  Name new files so they cannot clash with a
concurrent session's (waves 10-15 used ILS1_*/ILS4_*/ILS4F_*, ILS1M_*/ILS4M_*/
ILS4FM_*, IXP_*/IXPM_*, WLS_*/WLSM_*, WLJ_*, LAPC_*, LAPG_*, Alph_*).
```
