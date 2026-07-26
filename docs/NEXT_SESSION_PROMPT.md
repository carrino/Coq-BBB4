# Next-session prompt — break the OVERFLOW WALL

_Rewritten 2026-07-26 at the end of wave-13 (branch
`claude/lapdecider-residue-reduction-989ggx`, PR #35).  Wave-13 built the exact
lap checker, made certificate derivation mechanical, and boarded 119 machines —
then measured that ~523 of the remaining residue fail on ONE thing.  Full
record: `docs/WAVE13_FINDINGS.md`; design in `docs/LAPDECIDER.md`.  Paste-ready
below._

**Before pasting, check:** substitute the branch the session should develop on,
and name any files a concurrent session owns.

---

```
Continue the (4,2) residue reduction in carrino/Coq-BBB4, on a new branch off
main.

READ FIRST, in this order:
  docs/WAVE13_FINDINGS.md   -- sections 9 and 10 are the whole brief: five tape
                               readings, four structural classes, the measured
                               overflow wall, and the three things wave-13 got
                               WRONG (section 4).  Do not repeat them.
  docs/LAPDECIDER.md        -- the checker's design: what each step kind is,
                               where its soundness comes from, and why the
                               model is AFFINE in the carry index.
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

STATE: 3,890 of the frozen 5,156 settled (75.4%); D_remaining = 1,266.
Per-machine cost is now a vm_compute:
  python3 tools/counters/emit_lapcert.py --list FILE --emit
derives, differentially validates and compiles a board unattended.  24/25
sampled hand-emitted ILS4_* boards re-derive automatically.  After a wave,
`make closeout` shrinks D_remaining by exactly what you boarded (the
Closeout.vo compile needs the ~719-file board .vo closure, ~85 min once).

THE TASK -- the overflow wall.

  MEASURED (WAVE13 section 10a).  ~523 machines fail ONLY on the overflow
  chain: 385 already had an interior chain, and wave-13's new j=0 split added
  138 more that get past the interior and then die on the msb carry.  Every one
  is a SINGLE CHAIN away from a board.  Nothing else in the residue has that
  leverage -- it is >4x the 119 boarded in wave-13.

  THE HYPOTHESIS TO TEST FIRST (WAVE13 section 10b).  John, reading
  0RB---_0RC0LD_1LD1RC_0LA1LB: "1's to the LEFT of the bits when the msb is
  even and 1's to the RIGHT when the msb is odd".  That is the Ip/Mp one-cell
  frame shift, and it would flip EXACTLY at the overflow, since the overflow is
  the increment that grows the msb.  It predicts precisely what was measured:
  interior laps keep the bit length fixed so both ends share a frame (they all
  derive), while an overflow lap has its source and target in DIFFERENT frames
  -- and emit_lapcert builds B0 and B1 from the SAME ENCDATA row, so such a lap
  is UNREPRESENTABLE, not merely hard to search for.

  IT IS NOT VERIFIED.  A crude frame classifier was inconclusive (all-ones
  words satisfy both patterns) and the snapshots caught were all of one
  bit-length parity.  VERIFY BEFORE BUILDING: decode the anchor words at
  CONSECUTIVE bit lengths (msb 8 vs msb 16 on one machine) and check the frame
  actually flips.  Wave-12 section 4.1 and wave-13 section 4 are both about
  concluding structure from a partial search; do not add a third.

  IF IT HOLDS, the build is small and LapDecider.v is UNTOUCHED (srun_sound
  never sees the encoding, only the symbolic sides):
    1. emit_lapcert learns an overflow branch whose SOURCE and TARGET come from
       different ENCDATA rows (enc_src / enc_dst).  Both cview_none_* lemmas
       already exist -- no new Coq for step 1.
    2. the anchor family becomes frame-alternating: Cc p = (q, (W p ++ tail,
       S0, far)) with W p chosen by the parity of bitlen p.  One new fixpoint,
       plus the fact that bitlen is constant across an interior lap and
       increments at an overflow.

  IF IT DOES NOT HOLD, do not template blind.  Trace two or three overflow laps
  and ASK -- see WHEN STUCK below.

THEN, in ranked order (all independent of the above):

  (1) GRAY-CODE counters (WAVE13 section 9d).  The decomposition is DERIVED and
      VERIFIED for every p in 2..39, reuses cview verbatim, and is AFFINE:
        j >= 1:  Gp p = rep [S0] (j-1) ++ [S1] ++ [x]  ++ T
                 Gp (succ p) = rep [S0] (j-1) ++ [S1] ++ [~x] ++ T
        j  = 0:  the words differ in cell 0 only
      So: write theories/Counters/GpCounter.v (Gp plus those two lemmas, proved
      like cview_some_I by induction on p) and add one ENCDATA row, with the
      interior split on the extra bit x exactly as section 9a splits on j=0.
      This is an IMPLEMENTATION pass, not a design pass.
      Size the class FIRST with tools/counters/residue_triage.py, which accepts
      a PERIODIC difference pattern -- a constant-difference test scores
      paired-phase Gray anchors as "none" and undercounts.

  (2) The ~143 QUASI-HALTING counters (WAVE13 section 6).  John: "qh is fine,
      we just need to know it qh before 32M."  47 have StA untargeted, so
      LapGlueQH.glue_qh gives QHBound 1 outright (already wired; blocked in
      practice on a SECOND quiet state -- StB fires once at index 1 by the same
      argument -- and on mirrorize not knowing the QH closing shape; both
      small).  The other 96 need a bound of t0+1 from the boot length, which
      needs ONE new fact: "the lap visits only states in S".  That is
      computable from the chain (collect the states of every window sub-step
      and cycle unit run) but needs a states-visited variant of wsteps_frame /
      cycL / cycR, which today state only their ENDPOINTS.  One theorem, not
      one per machine.

  (3) The QUADRATIC family (WAVE13 section 9c).  Four machines measured with
      interior lap cost exactly (j+1)(j+2) -- one widening round trip per carry
      bit.  sside carries its count as a*j+b and srun returns ca*j+cb, both
      AFFINE by construction, so these are OUTSIDE the model and no chain
      search reaches them.  Needs either a quadratic count or a nested chain
      (an inner cycle repeated j times whose own length grows).  This is the
      first thing in six waves that the existing theory genuinely cannot
      express, so give it a DESIGN pass before an implementation pass.  It does
      NOT contradict wave-12 section 4.1, which correctly rejected three-level
      recursion for the WALL family -- different family, and here it is real.

  (4) The ~149 with NO anchor family at all.  Triage before assuming anything
      (residue_triage.py + triage.py fingerprint + lapshape).

  (5) The 27 genuine mxdys holdouts (tools/census_holdouts_kept.txt) -- the
      real endgame, and what John actually wants to be working on.

DO NOT RETRY (measured; grids in COUNTER_CLOSEOUT.md section 5, WAVE12 section
8, WAVE13 sections 4 and 8):
  * NGramHist/NGramCPS liveness over this residue at any (k,n,t); RepWL over
    the counter core; more per-machine lap emitters; emitter anchor-search
    widenings; Ip-encoding-alone; ripple ulen widening.
  * Maximal-only window cuts in the chain search -- finds nothing; the search
    must be target-aware.
  * Reaching an anchor's syntactic form by rotations alone -- impossible in
    principle; the constant offset needs SFold.
  * Widening the ENCODING table hoping for boards -- Kp/Dp/Mp bought 7 total.
    The chain search, not the alphabet, was binding; now the OVERFLOW is.
  * Peeling the overflow block to fix the wall -- tried, 0 of 385.
  * mxdys' implementation: John reports it is NOT available.  Stop asking.
    (WAVE9_FINDINGS.md section 7 is closed out.)

ALSO: lapshape.py segments laps by phase but has NEVER measured cost-vs-j.
That single missing measurement is why a quadratic family sat invisible for
five waves while searches that could not possibly reach it were widened.
residue_triage.py now measures it -- run it before templating anything.

DEFERRED TO STABLE HARDWARE: census fold-in (gen_proven.py + Deferred regen +
make census-verify + census_cache --update) -- batch once, it is the only step
that lowers D_census.  Also the champion 1RB1LD_1RC1RB_1LC1LA_0RC0RD (needs
`exists B, QHBound B` plus a 32.8M-step prefix) and the carry-shifted one-off
0RB1LC_1LC0LC_0RD1LA_1RD1RB (anchor Cc (p, k) with a frame offset).

WHEN STUCK ON A CLASS: print a few machine strings WITH A TAPE DUMP and ask
John.  Hand-inspection is 20-for-20 across waves 8-13.  In wave-13 alone he
identified the j=0 frame ambiguity, the two-pass carry, the quadratic
round-trip family, Gray code (twice, from two different surface descriptions),
and the alternating frame -- every one converted into a measurement, and two of
them into structure the automated search provably could not have found.  ASK
EARLY, ask with a TAPE, and ask about a CLASS not a machine: cluster with
residue_triage.py first so one reading covers many machines.

Commit + push per validated batch.  Name new files so they cannot clash with a
concurrent session's (waves 10-13 used ILS1_*/ILS4_*/ILS4F_*, ILS1M_*/ILS4M_*/
ILS4FM_*, IXP_*/IXPM_*, WLS_*/WLSM_*, WLJ_*, LAPC_*).
```
