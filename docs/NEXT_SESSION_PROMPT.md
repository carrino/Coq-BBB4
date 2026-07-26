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
  docs/NESTED_LAP_PLAN.md   -- THE TASK.  Why the count language does NOT
                               need extending, and the staged build with a
                               measure-first gate.
  docs/LAPDECIDER.md        -- our checker's design, and why the model is
                               AFFINE in the carry index.  Read the affineness
                               as a fact about one srun, NOT as the binding
                               constraint -- NESTED_LAP_PLAN section 0
                               corrects that reading.
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

  READ docs/NESTED_LAP_PLAN.md FIRST -- it retires the premise that the count
  language must be extended.  In one line: LapStep only asks for `exists n`,
  so an exponential lap needs a PROOF that some n works, never a formula for
  it -- and the 163 existing IXP_* boards already do exactly that, composing
  an affine boot chain, a well-founded induction to the all-ones fill, and an
  affine exit chain.  `2^j` is never written down.  So this is ONE NEW CHAIN
  STEP (chain to a second anchor family), not a new count language, and
  LapDecider.v is not touched.

  STAGES A AND B ARE DONE.  Wave-15 left this half-built, and the remaining
  work is NAMED:

    Stage A (DONE) -- tools/counters/innerfam.py dumps one overflow phase and
      finds the inner counter inside it.  Measured on 150 machines: 96% have
      an inner consecutive family; 79% run exactly 2^(K-1)..2^K-1.  The inner
      ALPHABET differs from the outer on 37% (Alph_10_11_11 -> Ip on 51 of
      144), which is the real reason emit_ixp.py -- Ip at both levels --
      derives 0 of this bucket.

    Stage B (DONE) -- theories/Counters/NestedLap.v, 63 lines, and BOTH its
      lemmas are "Closed under the global context" (zero axioms).
      Checkers/LapDecider.v is untouched.  theories/Tests/NestedLapRegression.v
      re-derives the hand-authored IXP_0RB0RB_0LC1RD_1RB1LC_0LA0RB board's
      overflow branch through the generic theorem -- a regression test against
      a known-good board.

    Stage C (THE WORK) -- the emitter.  Prototyped in
      tools/counters/nestboot.py, and the blocker is MEASURED: the EXIT chain
      derives readily with the existing derive_chain, the BOOT chain does not
      (1 of 12).  It is NOT a search budget -- (24,64) -> (48,256) -> (64,512)
      changes nothing.  It is KEY SELECTION: innerfam reports the best-scoring
      inner key, a machine has 16-27 keys that decode consecutively, and only
      a particular one is the family the boot can land on.  Enumerating every
      key instead of ranking takes boot chains from 1 of 5 to 3 of 5, and the
      keys that work are NEVER the best-scoring one -- they are consistently
      Ip at a state different from the outer with a short tail, exactly the
      reference's Cin v = (StC, (Ip v ++ [S1], S0, [S0;S0])).

      AND the boot has its OWN SHAPE, which must be measured like the
      overflow was.  tools/counters/bootshape.py runs the ovfshape question on
      the boot itself: over 41 machines, 31 (76%) have an AFFINE boot and 10
      (24%) an EXPONENTIAL one (ratio -> 2).  An exponential boot cannot be
      one chain, by the same affineness limit that put these machines in the
      residue -- so the EXP2 bucket splits again:
        affine boot (76%)  -> two-level nested lap is right, failures are a
                              SEARCH gap;
        exp boot (24%)     -> either a THREE-level nest, or the inner start is
                              mis-identified.  innerfam requires the decoded
                              values to be exactly 2^(K-1)..2^K-1, and a
                              SUBSEQUENCE of a longer count satisfies that too
                              -- so a counter running 1..2^K-1 is reported
                              EXACT with its start exponentially far in.
                              CHECK THAT before assuming a third level.

      START HERE, on the affine-boot machines.  The symbolic inner target is
      wrong, and the tape says how.  For 0RB1LA_1RC0LA_0LD1RB_1LB1LD (outer
      Jp@B, affine boot 4K+8):
        REAL phase start   st=B L=10101010110 R=e   SYMB B0out matches exactly
        REAL inner anchor  st=B L=11111111100 R=0   SYMB CinS = rep [1,1] 4 ++
                                                    [1] -- 9 cells, real is 11
      The opaque tail X must be the SAME at both ends of a chain; B0out forces
      X=[] and the inner anchor needs X=[S0;S0].  innerfam reports its key
      after rstrip0, so those cells are gone.

      DO NOT REPEAT: reading u and post off the real tape at two consecutive
      outer indices and using rep u j ++ post gave 0 of 18, DOWN from 3.  The
      inner anchor is not of that form with the count equal to the outer j --
      the decomposition assumption is wrong, not just the trailing cells.
      Dump tapes (spacetime.py) at two indices and read the inner anchor's
      actual shape before templating again.

  Full design, measurements and open questions: docs/NESTED_LAP_PLAN.md.

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
