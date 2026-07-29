# Residue prompt — the peel is spent; the QUAD extensions are now the top bite

_Refreshed 2026-07-29 at the end of the wave-28 track (branch
`claude/residue-reduction-4-2-2dp48i`), which took the CHEAP item the
previous refresh ranked third and found a route under it: the overflow
branch of every `obS = 0` alphabet was never PEELED, and peeling it boarded
**21** rows whose laps had been exactly affine all along
(`emit_lapcert._peel_ovf`, `PEEL_*`) -- then took the QUAD route's cheapest
cluster the same way and boarded **4** more (`QMG_*`; three padding gates
and one missing lemma, `QuadGlue.quad_reach`), plus 3 free from re-running
wave-27's tolerant reader now that `derive` peels.  `D_remaining`
**319 -> 291** (4,865 of the frozen 5,156 settled, 94.4%).  The same wave measured the register x
counter bucket end to end (`tools/counters/regscan.py`) and the headline is a
NEGATIVE result that re-ranks the whole list: of the 53 rows the reader can
read, **53 carry a `Theta(2^k)` branch**.  The register build is not four
ordinary chains; it is a piecewise `Cc` with a NESTED branch inside it.
`docs/WAVE28_FINDINGS.md` is the wave's own assessment; wave-27 built the
SKIP and QUAD routes (`docs/WAVE27_FINDINGS.md`), wave-26 the cascade
closeout and the QUAD design pass._

_**Scope: the RESIDUE, which is everything.**  The (4,2) HOLDOUT list was
closed on 2026-07-28; these 291 rows are the entire remaining problem._

**Before pasting, check:** substitute the branch the session should develop
on, and name any files a concurrent session owns.

---

```
Continue the (4,2) residue reduction in carrino/Coq-BBB4, on a new branch off
main.

READ FIRST, in this order:
  docs/WAVE28_FINDINGS.md   -- THE TASK's state, all of it; it is short.
                               Section 2 is the PEEL and its 21 boards (and
                               why 15 of them needed no exception at all);
                               section 3 is the register bucket MEASURED --
                               3c is the split of all 113 and 3d says what
                               the build actually is.
  docs/WAVE27_FINDINGS.md   -- the SKIP route (98 boards) and the QUAD route
                               (6 boards); section 3 lists the FOUR measured
                               emitter extensions the QUAD route still needs,
                               which are now the top-ranked bite.
  docs/WAVE26_FINDINGS.md   -- sections 7-8c.  7f is the QUAD design (what
                               "parity classes" and "double ladder" mean);
                               8 the SKIP decode; 8b/8c John's hand-reads.
  docs/WAVE25_FINDINGS.md   -- the cascade boarding wave (CASB_*).
  docs/WAVE18_FINDINGS.md   -- all of it; the two remaining nested-lap
                               chain buckets are EXPONENTIAL (section 4b).
  docs/WAVE16_FINDINGS.md   -- sections 5 and 6 (do-not-retry lists).
  docs/LAPDECIDER.md        -- the checker's design.
  docs/CLOSEOUT_ROUTE_A.md  -- how boards become D_remaining shrinkage.

ENV: apt coq 8.18.0 -- `apt-get install -y coq`, then
`coqc -native-compiler no -Q theories BBB4 <file>`.  No opam bootstrap.
`coq_makefile -f _CoqProject -o Makefile.coq` first; the Counters+Checkers
closure builds in ~30 s.  Do NOT run `make all` -- it pulls in the census.

NON-NEGOTIABLE: never touch theories/Census/; `python3 tools/census_cache.py
--check` must stay MATCH.  A board counts only when its file compiles and
`Print Assumptions` shows functional_extensionality_dep only (LapDecider,
LapCertGlue, LapGlueAbs, SkipGlue, QuadGlue, NestedLap and NestedLapLift are
axiom-FREE or funext-only -- keep them that way).  Everything under tools/
is UNTRUSTED; the kernel re-checks every board.

STATE: 4,865 of the frozen 5,156 settled (94.4%); D_remaining = 291.
docs/RESIDUE_MAP.md + tools/closeout/residue_map.tsv give lap shapes and
blockers (wave-23's measurement; subtract the boards of waves 25-28 --
CASB_*, SKIP_*, QMG_*, PEEL_* -- from its rows).

Failure profile at D_remaining = 291:

  113  no overflow phase        -- the register x counter bucket, MEASURED
                                   in WAVE28 3c: 35 grow-11, 8
                                   grow-11+virt, 4 plain+virt, 4
                                   period-2+virt, 2 plain (all 53 with a
                                   Theta(2^k) branch), 24 drift, 36 the
                                   reader cannot read yet
   95  no interior chain        -- QUAD 31 (16 parity + 12 double-ladder
                                   + 3 deep-pivot; the 4 non-rep are
                                   BOARDED), AFFINE/AFFINE 14, HIGHER 13,
                                   PARITY-AFFINE 13, EXP3 10, EXP2 8,
                                   EXP4 6
   37  no inner family at pow2 j -- what the peel left; the 15 affine rows
                                   are gone, these have no consecutive-value
                                   family at all under jexcept_scan
   19  no anchor
   18  the CASCADE's non-gated  -- 17 one/two-count rows (WAVE26 section 3;
                                   the 10's blocker is the SHIFT chain, a
                                   re-encoding pass no single-index window
                                   chain can be) and 1 main count at 4..7
    5  no second exit chain     -- the SCycR-entry-offset checker gap
    4  no inner interior chain
(113+95+37+19+18+5+4 = 291)
Per-machine cost is a vm_compute.  After a wave, make closeout (inventory +
gen_stages + audit) shrinks D_remaining by exactly what you boarded.

THE TASK (re-ranked 2026-07-29 after wave-28's measurement):

  (1) THE QUAD EMITTER EXTENSIONS (WAVE27 section 3, re-measured at their
      own gates in WAVE28 3e with tools/counters/quad_classes.py) -- 35
      rows, NO NEW THEORY, and now the largest no-new-theory bite in the
      residue.  In CHEAPEST-FIRST order, which is not size order:
        *  4 non-rep right sides -- DONE (WAVE28 3f).  Three of the four
           gates were PADDING and one was a missing lemma
           (QuadGlue.quad_reach: walk the ladder's rungs to Cq W j 0, where
           both terminals start, so a state that fires INSIDE the ladder
           has a witness).  Read that section before the 16: the same three
           padding shapes (a rung one blank short, a terminal one blank
           past the far side, a cbn that eats the ++ [S0] a rewrite needs)
           will be in front of them too.
        * 16 PARITY-CLASS -- now the top of this list.  THREE gates, not one.  Every one is a 2-cell
           alphabet (Bp / Alph_00_10_1, so rep RU k slides two cells), has
           the parity class in the MICRO hop only (cls 21111), AND a
           DOUBLED mark-count law ((2,1)/(2,3) or (2,2)/(2,4), not the
           plain ladder's (1,1)/(1,2)).  Per-parity chain pairs plus the
           k = 2i+r reindex (rep (u ++ u) i = rep u (2*i) in QuadGlue,
           destruct parity in hop_) is necessary and NOT sufficient -- the
           stride and the mark law are two more gates in extract().
        * 12 DOUBLE-LADDER: read_law itself fails ("term counts fit no
           affine law").  Ascending probes then a descending clearing
           ladder inside the terminal; two mrun compositions back to back
           (the theorem composes with itself); the reader needs recursive
           terminal segmentation.
        *  3 deep-pivot (mode (1, True), mark law (1,0)/(1,1)).

  (2) THE REGISTER x COUNTER BUILD, re-scoped by WAVE28 section 3.  It is
      NOT "a Cc with a register argument and one extra lap shape" -- every
      readable row has a Theta(2^k) branch.  The missing piece is one
      composition:

          piecewise Cc (VIRT arm + framed arm)  x  a NESTED branch

      SkipGlue supplies the p0-fenced reach/vis for the virtual arm,
      NestedLapLift the boot + inner-counter induction + exit, glue_neverqh
      the closer over an arbitrary Cc.  What does not exist is an emitter
      that puts a nested branch inside a piecewise Cc -- nestcert assumes
      the single-Cc template throughout.  Build it against the 4
      period-2+virt rows (John's own exemplar
      0RB0LC_1LC1RB_1LD1LA_1RD0RC is one) and then the 8 grow-11+virt.
      Note the framed arm for 43 of the 53 is NOT a residue register but a
      WALL that gains [S1;S1] per octave: Cc p = (q, E p ++ tail, S0,
      rep u (size p - c)), a Pos.size_nat argument, not a modulus.
      Second half of the same job: the 36 `short` rows are the READER's
      limit, not the machines' -- regscan.chase needs the counter word to
      end exactly at the head, and these rest MID-TAPE (WAVE26 8c's 83).
      Head-anywhere decode is what reads them.

  (3) JOHN'S REMAINING WAVE-27 READS (WAVE27 section 4b; hand-inspection
      31-for-31), cheapest first:
        * the no-anchor bucket reads as BOUNCERS (0RB0LD_1LA1LC_0LD0LC_
          1RD1RB and 0RB1LA_1LA1LC_0LD0LC_1RD1RB are one class, plus
          0RB0RD_1LC1RB_1RA0LC_1LB0LC "a bouncer counter"): probe with a
          bouncer-flavored QuadGlue/MeasureGlue reader before any new
          theory.  This bucket did NOT move this wave.
        * the 4 Jp long-phase rows are skip + a GRAY-CODE inner induction
          (counts up and down inside the phase) -- an inner NestedLap-style
          induction between VIRT and the landing, not a third chain.
        * the mechanical skip leftovers: wire s <= 4 (a pexpii view + the
          same fences; at least one confirmed skip-4 machine).

  (4) The 39 "no inner family" survivors and the cascade's 18: unchanged
      from the wave-26 prompt (the 10 two-count rows' blocker is a
      re-encoding SHIFT, a design question, not search).  Run cascade_probe
      over the EXP3/EXP4/HIGHER interiors -- still untouched.

  STANDING MOVE (wave-28): after ANY change to emit_lapcert.derive, re-run
  `restscan.py --emit` over the open buckets.  The tolerant reader finds
  anchor families the tail enumeration never offers, and that is a
  DIFFERENT gate from whatever derive just learned -- three rows this wave
  needed both the tolerant tail and the peel, and cost nothing but the run.

  DO NOT RETRY (this wave's additions):
  * The UN-PEELED overflow chain on any obS = 0 alphabet.  Measured: 0 of
    21 derive without the peel, 21 of 21 with it.  derive() now tries the
    peel automatically -- check that it fired before widening any framing
    search.
  * Reading a register family by INTERSECTING per-value rest forms.  The
    run passes a value once per OUTER octave, so the intersection mixes
    passes and names families whose laps never close (measured on
    0RB0RD_1LA1RC_1RD1LC_0LC1RA).  CHASE the family forward instead.
  * Expecting any branch of the register bucket to be a chain -- 53 of 53
    readable rows carry a Theta(2^k) branch at every frame assignment
    tried.  And do not call a virtual anchor flat because the lap OUT of
    it is short: the 4 plain+virt rows leave in 4 steps and ARRIVE in
    Theta(2^k).
  DO NOT RETRY (standing, from earlier waves): everything in WAVE27
  section 5, WAVE26 section 6, WAVE25 section 6, WAVE24 section 7, WAVE18
  section 5, WAVE16 section 5, and the long list in the wave-26 prompt
  (mxdys deciders, emit_graycert, encoding-table widening, overflow-block
  peeling, head-relative frame decodes, halting-transition batching).

THREE STANDING LESSONS (now six waves of evidence):
  * WHEN A TRANSITION TRACES BUT DOES NOT DERIVE, PEEL BEFORE ANYTHING
    ELSE.  (B->A wave-24; octave-down boot wave-25; two-count boot
    wave-26; QUAD micro wave-27; the whole overflow branch of every
    inferred alphabet wave-28 -- 21 boards for ~40 lines of emitter.)
  * READ THE LANDING OFF THE MACHINE instead of assuming its padding.
    Three SKIP boards were recovered that way in wave-27; in wave-28 it is
    the difference between a register family that exists and one that does
    not.
  * MEASURE THE BUCKET BEFORE DESIGNING FOR IT.  The previous prompt
    ranked the register build first expecting four ordinary chains; one
    afternoon of measurement says one of the four is an induction.  The
    measurement is cheap and the build is not.

WHEN STUCK ON A CLASS: print a few machine strings WITH AN
ABSOLUTE-COORDINATE TAPE DUMP (tools/counters/spacetime.py) and ask John.
Hand-inspection is 31-for-31 across waves 8-28.  ASK EARLY, ask with a
TAPE, and ask about a CLASS not a machine.

DEFERRED TO STABLE HARDWARE: census fold-in (gen_proven.py + Deferred regen
+ make census-verify + census_cache --update) -- batch once, it is the only
step that lowers D_census.  Also CloseoutFinal.v (OCaml pin, WAVE16 4b);
the champion 1RB1LD_1RC1RB_1LC1LA_0RC0RD; the carry-shifted one-off
0RB1LC_1LC0LC_0RD1LA_1RD1RB.

Commit + push per validated batch.  Name new files so they cannot clash
with a concurrent session's (recent waves: CASB_*, SKIP_*, QMG_*, PEEL_*).
```
