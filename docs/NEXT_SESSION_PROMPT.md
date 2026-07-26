# Next-session prompt — the NESTED LAP

_Rewritten 2026-07-26 at the end of wave-14 (branch
`claude/residue-reduction-4-2-5syxph`).  Wave-14 tested wave-13's
alternating-frame hypothesis, found what the overflow wall actually is
(a second counting round, so `Θ(2^j)` — measured, not inferred), built the
Gray-code family, and boarded 57.  Full record: `docs/WAVE14_FINDINGS.md`;
checker design in `docs/LAPDECIDER.md`.  Paste-ready below._

**Before pasting, check:** substitute the branch the session should develop on,
and name any files a concurrent session owns.

---

```
Continue the (4,2) residue reduction in carrino/Coq-BBB4, on a new branch off
main.

READ FIRST, in this order:
  docs/WAVE14_FINDINGS.md   -- sections 2, 3 and 4 are the whole brief: what the
                               overflow wall actually is (EXPONENTIAL, measured
                               three ways), why wave-13's section 10c build is
                               retired, and the three tooling bugs that were
                               holding 46 finished certificates.
  docs/LAPDECIDER.md        -- the checker's design: what each step kind is,
                               where its soundness comes from, and why the model
                               is AFFINE in the carry index.  That affineness is
                               now the binding constraint -- read it as a limit.
  docs/WAVE10_SHAPES.md     -- section 3 named the exponential-overflow family
                               back in wave-10 and said what it needs: an INNER
                               induction, not a window chain.  Still the answer.
  docs/WHY_NO_HAMMER.md     -- why exactness is required at all.
  docs/CLOSEOUT_ROUTE_A.md  -- how boards become D_remaining shrinkage.

ENV: apt coq 8.18.0 -- `apt-get install -y coq`, then
`coqc -native-compiler no -Q theories BBB4 <file>`.  No opam bootstrap.  Build
a checker's dependency closure by coqdep-ordering its deps and compiling them
individually; `make all` pulls in the census.

NON-NEGOTIABLE: never touch theories/Census/; `python3 tools/census_cache.py
--check` must stay MATCH.  A board counts only when its file compiles and
`Print Assumptions` shows functional_extensionality_dep only (LapDecider and
LapCertGlue are axiom-FREE -- keep them that way).  Everything under tools/ is
UNTRUSTED; the kernel re-checks every board.

STATE: 3,980 of the frozen 5,156 settled (77.2%); D_remaining = 1,176.
Per-machine cost is a vm_compute:
  python3 tools/counters/emit_lapcert.py --list FILE --emit    (Ip/Jp/Kp/Dp/Mp)
  python3 tools/counters/emit_graycert.py --list FILE --emit   (Gray)
derives, differentially validates and compiles a board unattended.  After a
wave, inventory.py + gen_stages.py + audit.py shrink D_remaining by exactly
what you boarded (the Closeout.vo compile needs the ~719-file board .vo
closure, ~85 min once).

THE TASK -- the nested lap.

  MEASURED (WAVE14 section 3).  The overflow lap of the residue's dominant
  class is Theta(2^j), not affine.  The machine counts the whole range a
  SECOND time, in a frame shifted one cell, and only then bumps the msb --
  which is exactly John's reading ("count 8->15, then shift over one with a 1
  in position 2 and count 8->15 again, then shift back"), confirmed in
  absolute tape coordinates.  Flagship 0RB---_0RC0LD_1LD1RC_0LA1LB: interior
  4j+4, overflow 16*2^j+4j+4.  Over the whole residue ovfshape.py reads 496
  AFFINE/EXP2 against 304 AFFINE/AFFINE, 392 with no decodable anchor, 49
  HIGHER and 25 QUAD.  The exponential class is bigger than everything the
  affine checker can still reach.

  sside carries its count as a*j+b and srun returns ca*j+cb.  Both are affine
  by construction, so this is not a search problem: no chain search, no step
  language widening, and no encoding row reaches it.

  TWO ROUTES.  Give this a DESIGN pass before an implementation pass.  It is
  the second thing (after section 9c's quadratic interior) that the existing
  theory genuinely cannot express, and both want the same answer.

  1. A NESTED LAP in LapDecider -- an inner anchor family run 2^j times, which
     is what the overflow physically does.  Keeps the per-machine cost a
     vm_compute.  Counters/IXPGadgets.v already carries the positive gadgets a
     hand-built instance needed (pow2, fill, cview_none_shape, Ip_pow2), and
     LapCertGlue.reach_ovf is the well-founded induction.
  2. Route the class to wave-12's emit_ixp.py / IXPGadgets.v, which boarded
     163 of exactly this family by hand.  THE CHEAP VERSION WAS TRIED AND
     FAILS: 0 of 12 sampled EXP2 machines derive, because that template is
     hard-wired to Ip with anchor tail [S1;S0] and the EXP2 bucket is 224 Jp /
     168 Ip / 104 Mp.  Widening its alphabet is on do-not-retry.

THEN, in ranked order (all independent of the above):

  (1) The 157 QUASI-HALTING machines (WAVE13 section 6).  John: "qh is fine, we
      just need to know it qh before 32M."  Still the cleanest one-theorem win,
      and one of its two blockers is now gone -- mirrorize learned the QH
      closing shape (WAVE14 section 4.2), so the mirror route works.  The 96
      with StA targeted need ONE new fact: "the lap visits only states in S".
      That is computable from the chain (collect the states of every window
      sub-step and cycle unit run) but needs a states-visited variant of
      wsteps_frame / cycL / cycR, which today state only their ENDPOINTS.  One
      theorem, not one per machine.

  (1b) TWO SMALL, CONCRETE LEADS, both already localized (WAVE14 section 3):
      * 13 PARITY-AFFINE machines are IN model -- affine on each parity class
        of j, which is WAVE13 section 9b's two-pass carry.  They need only the
        m=2 re-index (j = 2i+r, block unit u^2) wired into the emitter.  No new
        theory; section 9b's own exemplar is in the set.
      * 8 machines whose EXP4-at-a-binary-anchor marks them as GRAY (11 of the
        19 EXP4 are exactly this wave's Gray boards).  On
        0RB0LA_1LA1RC_0RD1RD_1LB0LB the Gp anchor family is present and closes
        affinely at 4j+8, yet all five symbolic branches fail in derive_chain.
        Not the tail depth (a 4-way x,y peel does not help) and not the search
        budget.  Instrument _win_candidates on that configuration.

  (2) The QUAD (25) and remaining HIGHER (17, mostly ~3^j -- never read) machines -- WAVE13 section 9c's round-trip
      family, lap(j) = (j+1)(j+2).  Same design question as the nested lap: a
      count that is not affine in j.  Solve them together, not separately.

  (3) The 47 (was 185) with NO anchor family at all.  alphabet_infer.py +
      gen_alphabet.py INFER a counter's word family from its own tape as a
      triple (A,B,C) and generate the Coq module; 18 families are already
      wired.  Run those on the 47 before assuming anything.

  The residue's whole failure profile is now: 532 no overflow chain, 433 no
  interior chain, 164 no visit witness, 47 no anchor.

  (4) The 27 genuine mxdys holdouts (tools/census_holdouts_kept.txt) -- the
      real endgame, and what John actually wants to be working on.

DO NOT RETRY (measured; grids in COUNTER_CLOSEOUT.md section 5, WAVE12 section
8, WAVE13 sections 4 and 8, WAVE14 section 7):
  * NGramHist/NGramCPS liveness over this residue at any (k,n,t); RepWL over
    the counter core; more per-machine lap emitters; emitter anchor-search
    widenings; Ip-encoding-alone; ripple ulen widening.
  * Maximal-only window cuts in the chain search -- the search must be
    target-aware.
  * Reaching an anchor's syntactic form by rotations alone -- impossible in
    principle; the constant offset needs SFold.
  * Widening the ENCODING table hoping for boards.  Kp/Dp/Mp bought 7 total and
    Gray bought 11.  The alphabet has never been the binding constraint.
  * Peeling the overflow block to fix the wall -- tried, 0 of 385.
  * enc_src/enc_dst from two ENCDATA rows to break the overflow wall (WAVE13
    section 10c).  The wall is the overflow's COST, not its target word.
  * A HEAD-RELATIVE frame decode as a test of a frame hypothesis:
    MB(m) ++ [S1] = [S1] ++ MA(m) identically, so the verdict is an artifact of
    head position.  Use absolute column parity (frame_probe.py, spacetime.py).
  * Believing a negative from an emitter run that RAISED.  A crash in
    emit_lapcert's reporting path cost 46 finished certificates and looked
    exactly like "the search finds nothing".  Survey with wall_survey.py, which
    keeps the best outcome per machine, before concluding anything is hard.
  * (RETIRED) "mxdys' implementation is not available" -- it IS:
    github.com/ccz181078/busycoq tree BB6, verify/Inductive.v and
    verify/RRBA.v.  See docs/MXDYS_DECIDERS_PLAN.md; START THERE.

ALSO: ovfshape.py measures cost-vs-j on BOTH branches and classifies
AFFINE / QUAD / EXP2.  Run it before templating anything.  The interior version
of that measurement was missing for five waves and hid a quadratic family; the
overflow version was missing for six and hid this one.

DEFERRED TO STABLE HARDWARE: census fold-in (gen_proven.py + Deferred regen +
make census-verify + census_cache --update) -- batch once, it is the only step
that lowers D_census.  Also the champion 1RB1LD_1RC1RB_1LC1LA_0RC0RD (needs
`exists B, QHBound B` plus a 32.8M-step prefix) and the carry-shifted one-off
0RB1LC_1LC0LC_0RD1LA_1RD1RB (anchor Cc (p, k) with a frame offset).

WHEN STUCK ON A CLASS: print a few machine strings WITH AN ABSOLUTE-COORDINATE
TAPE DUMP (tools/counters/spacetime.py) and ask John.  Hand-inspection is
21-for-21 across waves 8-14.  In waves 13-14 he identified the j=0 frame
ambiguity, the two-pass carry, the quadratic round-trip family, Gray code
(twice, from two different surface descriptions), and the alternating frame --
and that last one turned out to BE the overflow mechanism, which six waves of
automated search had mis-diagnosed.  ASK EARLY, ask with a TAPE, and ask about
a CLASS not a machine: cluster with residue_triage.py or wall_survey.py first
so one reading covers many machines.

Commit + push per validated batch.  Name new files so they cannot clash with a
concurrent session's (waves 10-14 used ILS1_*/ILS4_*/ILS4F_*, ILS1M_*/ILS4M_*/
ILS4FM_*, IXP_*/IXPM_*, WLS_*/WLSM_*, WLJ_*, LAPC_*, LAPG_*).
```
