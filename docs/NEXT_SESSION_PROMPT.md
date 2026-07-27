# Next-session prompt — the exponential overflow is the endgame

_Amended 2026-07-27 at the end of the wave-16 RESIDUE track (branch
`claude/coq-bbb4-next-session-ctox52`), which took ranked item (1) below — the
`AFFINE/AFFINE` bucket, filed as a "CONFIRMED search gap" — and found the gap
was in the MATCHER, not the search: the lap closes one trailing blank past the
anchor, which `lift` cannot see and which `LapDecider`/`LapGlue` never asked
about.  **126 boards.**  With the concurrent holdout waves merged,
`D_remaining` is **883**.  Item (1) is DONE and the ranked list is renumbered.
Full assessment: `docs/WAVE16_FINDINGS.md` — §5 is a do-not-retry list for
`derive_chain` widenings, §6 is the lesson, §6b corrects the old ranked item
(2).  THE TASK (the exponential overflow) is untouched and unchanged._

_**Scope: the RESIDUE only.**  John runs the 4 remaining (4,2) holdouts in
dedicated sessions — that front is out of scope for this prompt, and the
residue is now the whole job._

_Written 2026-07-26 at the end of wave-15 (branch
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
  docs/WAVE16_FINDINGS.md   -- sections 5 and 6 at minimum.  Section 5 is the
                               do-not-retry list for derive_chain widenings
                               (five of them, all measured at 0, including
                               "more budget").  Section 6 is the lesson:
                               check what the search is being asked to PROVE
                               before widening it -- LapGlue's premises are
                               the specification, the emitter's templates are
                               one implementation of them.
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

STATE: 4,273 of the frozen 5,156 settled (82.9%); D_remaining = 883.
THE HOLDOUTS ARE NOT YOURS.  John runs the 4 remaining (4,2) holdouts in
dedicated sessions -- do not open that front, do not "sweep the holdouts with
every engine", and do not spend a wave on tools/census_holdouts_kept.txt.
This prompt is the RESIDUE, and the residue is now the whole job.
(Wave-16 boarded 126; wave-15 boarded 141 before that, and PR #37 19 more.
The rest of the drop from 900 is the concurrent HOLDOUT waves, not the
residue.)
Failure profile, measured at the end of wave-16 with D_remaining = 890, so it
is a few rows stale but the proportions hold:
  735  no overflow chain
  105  no interior chain
   35  no anchor family at all
   15  no visit witness (StA is targeted)  -- see WAVE16 section 6b
Cross-referenced against ovfshape, which is what makes the list actionable:
  no overflow chain  ->  492 AFFINE/EXP2 (THE TASK), 211 no-anchor,
                         23 AFFINE/AFFINE (in model, still unboarded)
  no interior chain  ->  41 QUAD, 14 AFFINE/AFFINE, 13 PARITY-AFFINE,
                         13 HIGHER
ovfshape over the whole list: 500 AFFINE/EXP2, 246 no-anchor, 175
AFFINE/AFFINE, 41 QUAD, 13 PARITY-AFFINE, 13 HIGHER, 28 EXP3/EXP4/other.
(The AFFINE/AFFINE count is 175, NOT the 141 in WAVE15_FINDINGS section 5b --
that number no longer reproduces.)
Per-machine cost is a vm_compute:
  python3 tools/counters/emit_lapcert.py --list FILE --emit   (24 alphabets)
After a wave, inventory.py + gen_stages.py + audit.py shrink D_remaining by
exactly what you boarded, in minutes.

FROM PR #40 (branch claude/coq-bbb4-residue-removal-lt5yac), which ran Stage 0
independently and agrees with wave-15 on every number.  THESE ARE SIDE ITEMS,
NOT THE WAVE -- "THE TASK" below (the exponential overflow, 492 machines) is
the wave, and nothing here competes with it.  (a) is worth doing first only
because it is measured in HOURS and is a strict prerequisite for (b); (c) is
the highest-VARIANCE item on the whole board, not the highest-yield, and
should wait until THE TASK stalls.  Three things wave-15 does not have:

  (a) SOME MACHINES ARE BLOCKED BY THE CENSUS CONSTANT, NOT BY DIFFICULTY.
      QHBound 2000 is FALSE for any machine that genuinely quasi-halts after
      step 2000, so no liveness strength can ever take it through that tier.
      B_census = 2000 is an arbitrary bookkeeping value.  John's fix, and it
      is free: raise the TARGET predicate to QHBound 32779478 (the champion's
      score) and prove it only on the DEFERRED machines -- the census itself
      never changes.  TNF_QH.v already has qhbound_mono and neverqh_qhbound,
      so it is a three-line corollary over the untouched census_decided;
      B_census/D_census stay put, CENSUS_VO_HASH stays MATCH, and the walk
      never re-runs.  NOT YET WRITTEN.  Do this first -- it is small and it
      unblocks (b).

      SIZE THIS BUCKET BEFORE ASSUMING IT IS FOUR.  A machine is
      constant-blocked iff its true score exceeds 2000, and PR #40 found five
      (2332, 2512, 2568, 2819, 66349) -- but only inside a 400k-step window,
      so anything scoring between 400k and 32.8M was classified RECUR and
      never seen.  If the bucket is 5, the corollary is worth 5 boards; if it
      is 150, it is worth 150, and it is still three lines.  That makes this
      the cheapest unknown on the board.  The scan is
      /tmp/.../deepscan.py in the PR #40 session (35M steps/machine, ~1.5 h
      at 4 workers, paused at 325/1157); it is pure simulation, no Coq.
      WARNING, and this bit is load-bearing: a single-window "quiet" verdict
      is UNSOUND -- a state visited at exponentially spaced times looks quiet
      at every finite window.  Confirm every candidate with the two-window
      test (tools/counters/visit_gaps.py --confirm) before counting it.  That
      trap cost PR #40 a retraction from 538 quasi-halters to 217.

  (b) FOUR BOARDS ALREADY PROVED, ALL STILL UNPROVEN ON MAIN, ALL
      CONSTANT-BLOCKED.  theories/Counters/BlankTail.v: if after a finite
      prefix the machine sits in state q with the half-tape AHEAD blank and
      tm q S0 self-loops to q, it marches across virgin tape forever in one
      state, so every other state is quiet.  Two-line induction; per machine a
      TM table plus one vm_compute.
        QHBound 2512  1RB1RA_0RC1LA_1LC1LD_0RB0RD
        QHBound 2568  1RB1RA_0RC0RB_0RD1RA_1LD1LB
        QHBound 2819  1RB1RC_1LC1RD_1RA1LD_0RD0LB   (previous BBB(4) champion)
        QHBound 66349 1RB0LD_1LC0LA_1LA0LC_1RD1RC   (previous BBB(4) champion)
      All four compile, functional_extensionality_dep only.  They are PROVED
      but NOT BOARDED: they need (a), then the closeout wiring.
      The CHAMPION 1RB1LD_1RC1RB_1LC1LA_0RC0RD is the same shape -- at step
      32,779,478 its tape is COMPLETELY BLANK and it spins out in state C
      (C0 -> 1,L,C), which is why it is also the BLB(4) champion: the blanking
      event and the quiet point are the same event.  It wants the same closer
      via cstepsN (nat is unary; a 32.8M literal is catastrophic).
      blanktail_scan.py proves this closer is EXHAUSTED at exactly these five;
      the period-k generalisation buys nothing (every hit has period 1).

  (c) THE HINT PATH IS BUILT AND VALIDATED.  Wave-15 names this its lead
      item; PR #40 does NOT agree it should be run first, and the reason is a
      number.  Inductive's measured ceiling on our residue is ~20 of 1,176
      (under 2%) -- but that was measured UNHINTED, and the counter
      representations are hint-gated, so hints could lift it a lot or not at
      all.  Nobody knows.  THE TASK below targets ~340 machines with our own
      machinery and no such uncertainty, so it is the wave.
      The disagreement is about SIZING, not about doing it: run the hint path
      as a MEASUREMENT, not as a wave.  30 machines with derived hints, look
      at the fire rate, THEN decide.  That is cheap (wave-15 costs the whole
      thing at half a day) and it converts the largest unknown on the board
      into a number.  What would be wrong is committing a wave to it on the
      strength of the shape argument alone -- which is exactly the mistake
      wave-15's own standing lesson, a few lines below, warns about.
      busycoq mirror branch claude/coq-bbb4-residue-removal-lt5yac:
      verify/InductiveDump.v adds --bec/--becpos/--dec/--ov0/--ov1 (words as
      digit strings, "." = empty; states as letters) plus --initial-steps and
      --mnc, and a --dump that prints the rule chain and the states each
      config_expr carries.  VALIDATED by reproducing mxdys' own IndSBCv1.v
      nonhalt3: hint-free budget-exhausted at 9.15 s, hinted nonhalting in
      0.067 s with flags = nat_mul + nat_powsum + a counter-side constructor.
      tools/counters/exrules_check.py is a SOUND rejection filter for the
      ExtraRules obligation (~2 ms/candidate), validated against two rules
      mxdys proved with Qed and against a one-state perturbation.
      exrules_search.py derives candidates from alphabet_infer's (A,B,C) --
      which IS his (d0,d1,d1a); the bbchallenge wiki's Inductive_Proof_System
      page documents the same triple as C(d0,d1,dh,n).
      NOTE the obligations carry NO step count -- they are bare -[tm]->+
      progress facts, and the powsum cost is synthesised by the ENGINE when it
      nests them.  Our LapDecider conflates shape and cost (sside carries
      a*j+b), which is why a Theta(2^j) lap is unstateable for us and not for
      him.  That is a design lesson, not a bolt-on.

MXDYS THREAD: CLOSED except for one live lead.  Do not re-open it blind.

  mxdys told John "see Inductive and RRBA deciders in
  github.com/ccz181078/busycoq/tree/BB6/", which is why wave-15 exists.
  Both are now measured, and the wave's real finding is that NEITHER had been
  tested in the configuration that matters:

    RRBA  -- RULED OUT.  Extraction is solved (Unset Extraction AutoInline;
             recipe in tools/mxdys/README.md).  Run against
             tools/mxdys/control/D_ixp_family.txt -- 40 of our own IXP_*
             boards, machines we have PROVED are exponential-overflow
             interleaved counters, i.e. the residue's exact species -- it
             FAILS every one, at parameters taken from mxdys' own RRBAv*.v
             proofs.  Its class is "sync BI-counter"; ours is a SINGLE
             counter whose overflow re-runs the interior lap.  Different
             species.  Do not spend more time here.

    Inductive -- THE LIVE LEAD, and the wave-15 hint attempt used the WRONG
             REPRESENTATION, so its 0-of-6 is worthless, not weak.

             Our residue is the SYNC BOUNCER COUNTER class, formalised on
             wiki.bbchallenge.org/wiki/Inductive_Proof_System:

               C'(2a,2b+1,0) = d0 C'(a,b,0)   C'(2a+1,2b,0) = d1 C'(a,b,0)
               well-formed when a + b + 1 = 2^n
               increment: C'(a+1,b,n) -> C'(a,b+1,n)
               overflow:  C'(0,b,n)   -> C'(2b+1,0,n+1)

             Two complementary counts summing to 2^n - 1, so ONE OVERFLOW
             COSTS 2^n INCREMENTS -- that is our measured Theta(2^j) overflow
             and John's "count 8->15, shift, count 8->15 again" in mxdys'
             notation.  Inductive.v has it as side_binary_dec (THREE nat_exprs
             = C'(a,b,n)), wired by config_SBC = Sync Bouncer Counter, which
             supplies an INCREMENT rule AND an OVERFLOW rule plus two state
             pairs.  wave-15's hint used side_binary_Pos_inc_rule -- a plain
             binary counter with NO overflow rule.

             DO THIS FIRST.  config_SBC's arguments map onto data
             emit_lapcert already derives per machine:
               d0,d1 <- ENCDATA uD/uS ; d1a <- soD ; QL,QR <- interior-lap
               states ; QL',QR' <- OVERFLOW-lap states ; T0 <- boot_probe.
             tools/mxdys/hint.ml needs one edit: swap the constructor for the
             side_binary_dec_inc_rule + side_binary_dec_ov1_rule PAIR and take
             the state pairs from the two laps instead of sweeping 4x4 blind.
             Half a day, and it is the only thing that could still make this
             trove pay.

             (Bell_eats_counter is a DIFFERENT class -- its overflow HALVES
             the counter -- so do not chase it.)

    Inductive, background -- still untested properly.  It decides 48%
             of the machines we boarded and 0% of the residue, but EVERY
             wave-15 sweep ran with ex_rules = [].  Its counter
             representations (side_binary, side_binary_Pos, side_BL) are
             HINT-GATED -- the README's "Others (requires some hints from
             human)" -- and our residue is exactly those.  A hint IS an
             ENCDATA row:

               side_binary_Pos_inc_rule d0 d1 d1a qL qR QL QR
                 where d1^^n is our rep uS j, d0 is our uD, d1a the edge word

             We compute all of it already.  The one attempt guessed blind
             (T0 in {0,50,200,1000}, 2-cell digits, block size 2) against
             mxdys' real parameters (T0=7450, 4-cell digits, block size 5) and
             got 0 of 6 -- a WEAK negative.  The block-size mismatch is the
             interesting part: our alphabets are 1-3 cells and his are 4-5,
             which suggests these machines want a coarser macro-block than our
             anchor search uses.  tools/mxdys/hint.ml is built and takes
             <spec> d0 d1 d1a.  Half a day, and it is the only thing that
             could still make this trove pay.

  A STANDING LESSON from this wave, worth more than the deciders: I twice
  argued from README prose about which tool was "the" right one, in opposite
  directions within a day, and both times was over-narrow.  When the expert
  has named the tools, MEASURE them.  And build the control FIRST -- the
  positive control (48% on boarded machines) is what proved the harness sound
  and made every later negative worth believing.

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
      the boot itself: over 139 machines, 105 (76%) have an AFFINE boot and
      34 (24%) an EXPONENTIAL one (ratio -> 2).  THE EXP BOOT IS AN Mp
      PHENOMENON -- Mp is 2 affine / 31 exp, while Jp is 63/3,
      Alph_10_11_11 is 36/0 and Ip is 4/0.  So target Jp + Alph_10_11_11 + Ip
      first, and give Mp its own tape reading (spacetime.py) before
      templating it at all.  An exponential boot cannot be
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

  (1) DONE IN WAVE-16 -- do not re-run it.  The AFFINE/AFFINE bucket was NOT
      a search gap.  derive_chain finds the chains; the emitter's matcher
      rejected them for landing one trailing blank past the anchor, which
      lift cannot see and which LapDecider.lap_of_run / LapGlue's Hlap never
      asked about.  116 boards.  docs/WAVE16_FINDINGS.md section 5 lists the
      five derive_chain widenings measured at 0 -- INCLUDING more search
      budget, since maxdepth=24 is never reached on this population.  Do not
      spend another wave widening that search.

      The small leftovers, both named and both mechanical:
        * 7 machines with MULTI-CELL far slack -- generalise the close from a
          fixed number of lift_app_blank rewrites to ExactClosure.strip_lift.
        * 3 wanting the lift interior route under glue_qh / glue_qh_abs --
          each needs the same premise weakening glue_neverqh_lift got, in
          Counters/LapCertGlueLift.v.

  (2) THE 37 STILL-IN-MODEL MACHINES -- the smallest named population left,
      and the cheapest.  ovfshape says AFFINE interior AND AFFINE overflow,
      so no new theory is needed, yet the emitter still fails: 23 with
      "no overflow chain" and 14 with "no interior chain".  Wave-16 took this
      bucket from 0 to 126 by asking what the search was being asked to
      PROVE rather than widening it (WAVE16 section 6); ask the same question
      of these 37 before touching derive_chain.  Regenerate with
        python3 tools/counters/ovfshape.py --list tools/closeout/frozen_unproven.txt
      and cross-reference against an emit_lapcert --json run.

  (3) The 15 no-visit-witness machines.  READ WAVE16 SECTION 6b FIRST: the
      wave-15 prompt said their missing state "is genuinely LIVE, but fires
      only in the INTERIOR lap", and asked for a vis_via_int dual.  That dual
      is BUILT (LapCertGlueLift.vis_via_int_lift) and it fires on NONE of
      them, because the premise is false -- simulated, StA's last visit is at
      step 4 to 11, so they are quasi-halters.  They miss glue_qh (StA IS
      targeted) and glue_qh_abs (closed_b is a DIGRAPH fact, so any set
      holding StD holds StA).  What is actually true is symbol-aware: StD
      never READS S1 after the boot.  That is the build, and the bound is
      tiny -- QHBound 12 covers all 15.

  (4) 41 QUAD/QUAD -- a quadratic interior AND overflow.  Outside the affine
      certificate model, and the one bucket of real size that has never had a
      design pass.  Bounce_8.v's MeasureGlue nesting is the precedent.

  (5) 13 PARITY-AFFINE machines are IN model -- affine on each parity class
      of j.  They need the m=2 re-index (j = 2i+r, block unit u^2).
      MEASURED in wave-14: only ~3 of the 13 derive both parity branches with
      the naive re-index, so this is worth ~3 boards.  Do not oversize it.

  (6) The 35 with NO anchor family at all.  alphabet_infer.py +
      gen_alphabet.py INFER a counter's word family from its own tape as a
      triple (A,B,C) and generate the Coq module; 18 families are wired.

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
