# Residue prompt — the SKIP counters are boarded; the register machines are next

_Refreshed 2026-07-29 at the end of the wave-27 track (branch
`claude/residue-reduction-4-2-cont-frgu3x`), which built BOTH routes the
previous refresh ranked and boarded 104 machines in one wave -- the largest
since the nested-lap waves: the SKIP route end to end (`Counters/SkipGlue.v`
+ `tools/counters/skipcert.py`, 98 of the 211 `no overflow phase` rows,
`SKIP_*`) and the QUAD route end to end (`Counters/QuadGlue.v` +
`tools/counters/quad_emit.py`, 6 of the 41 QUAD/QUAD rows, `QMG_*`).
`D_remaining` **427 -> 323** (4,833 of the frozen 5,156 settled, 93.7%).
`docs/WAVE27_FINDINGS.md` is the wave's own assessment; WAVE26 sections 7f,
8, 8b and 8c (John's four hand-reads, 26-for-26) are the design briefs both
routes were built from and the brief for what remains.  Before it, wave-26
spent the cascade route (all 69 gating machines boarded, `CASB_*`,
431 -> 427); the story back to wave-18 is in the respective FINDINGS files._

_**Scope: the RESIDUE, which is everything.**  The (4,2) HOLDOUT list was
closed on 2026-07-28; these 323 rows are the entire remaining problem._

**Before pasting, check:** substitute the branch the session should develop
on, and name any files a concurrent session owns.

---

```
Continue the (4,2) residue reduction in carrino/Coq-BBB4, on a new branch off
main.

READ FIRST, in this order:
  docs/WAVE27_FINDINGS.md   -- THE TASK's state, all of it; it is short.
                               104 boards: the SKIP route (98) and the QUAD
                               route (6).  Section 2 is the SKIP build and
                               its three measured leftovers; section 3 the
                               QUAD build and its FOUR measured emitter
                               extensions (16 parity, 12 double-ladder, 4
                               non-rep right sides, 3 deep-pivot); section 4
                               the tolerant rest scan over the 113 rows the
                               211-bucket has left.
  docs/WAVE26_FINDINGS.md   -- sections 7-8c.  Section 7f is the QUAD
                               design (what "parity classes" and "double
                               ladder" mean); section 8 the SKIP decode;
                               8b/8c John's hand-reads: ONE encoding ("1 to
                               the left of every bit"), THREE resting
                               regimes -- skip-s (boarded), REGISTER x
                               COUNTER (the big open bucket), and reads
                               that look plain but measure two-regime.
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

STATE: 4,833 of the frozen 5,156 settled (93.7%); D_remaining = 323.
docs/RESIDUE_MAP.md + tools/closeout/residue_map.tsv give lap shapes and
blockers (wave-23's measurement; subtract the 69 CASB_*, 98 SKIP_* and 6
QMG_* boards from its rows).

Failure profile at D_remaining = 323:

  113  the 211-bucket's rest     -- dominated by the REGISTER x COUNTER
                                     regime (restscan: 30 of the first 31
                                     scanned; WAVE27 section 4), plus the
                                     4 Jp long-phase rows, at least one
                                     skip-4, and a few deeper skips
   99  no interior chain         -- QUAD 35 (16 parity + 12 double-ladder
                                     + 4 non-rep + 3 deep-pivot, ALL
                                     emitter extensions of quad_emit.py),
                                     AFFINE/AFFINE 14, HIGHER 13,
                                     PARITY-AFFINE 13, EXP3 10, EXP2 8,
                                     EXP4 6
   60  no inner family at pow2 j -- what survived the offset/split/refill
                                     routes; 32 have no family under any
                                     route
   18  the CASCADE's non-gated   -- 17 one/two-count rows re-measured in
                                     WAVE26 section 3 (10 + 4 + 3, all `no
                                     boot chain`; the 10's blocker is the
                                     SHIFT chain, a re-encoding pass no
                                     single-index window chain can be) and
                                     1 main count at 4..7
   24  no anchor
    5  no second exit chain      -- the SCycR-entry-offset checker gap
    4  no inner interior chain
(113+99+60+18+24+5+4 = 323)
Per-machine cost is a vm_compute.  After a wave, make closeout (inventory +
gen_stages + audit) shrinks D_remaining by exactly what you boarded.

THE TASK (re-ranked 2026-07-29 after wave-27):

  (0) THE REGISTER x COUNTER BUILD -- the biggest and best-characterised
      bite left (WAVE26 8b, WAVE27 section 4).  The tape is
      [register][1b-pairs]; the counter encoding is the SAME
      Alph_10_11_11; the family is (register state x counter): a FINITE
      union of anchor forms, alternating by octave, with register-step
      laps at measured mid-octave points (e.g. a B@R rest at 2^(k+1)-2).
      The boarding device already exists TWICE over: piecewise Cc +
      glue_neverqh (skip route), and the p0-fenced reach/vis plumbing
      (SkipGlue) -- what is new is a Cc with a register argument and one
      extra lap shape per register step.  Build order: extend
      restscan.py to read the register (head-anywhere rests, constant
      prefix frames, per-octave forms), hand-board
      0RB0LC_1LC1RB_1LD1LA_1RD0RC (John's read, confirmed), then the
      emitter.  Expect most of the 113 here.

  (1) THE QUAD EMITTER EXTENSIONS (WAVE27 section 3) -- 35 rows, no new
      theory, in measured-size order:
        * 16 PARITY-CLASS: micro chains differ in LETTERS by k-parity.
          Derive per-parity chain pairs; the sconf count fields already
          express k = 2i+r (a = 2); add rep (u ++ u) i = rep u (2*i) to
          QuadGlue and destruct parity in hop_/term_.
        * 12 DOUBLE-LADDER: ascending probes then a descending clearing
          ladder inside the terminal; two mrun compositions back to back
          (the theorem composes with itself); the reader needs recursive
          terminal segmentation.
        *  4 non-rep right sides (2-cell stride variants of the ladder).
        *  3 deep-pivot (boot is a j-dependent law, mode (1, True)).

  (2) SKIP leftovers (WAVE27 section 2): wire s <= 4 (a pexpii view +
      the same fences; at least one confirmed skip-4 machine) and the
      4 Jp rows whose ~8j phase needs a 2-SEGMENT virtual pipeline
      (V -> X -> E; the extractor already enumerates the candidates).

  (3) The 60 "no inner family" survivors and the cascade's 18: unchanged
      from the wave-26 prompt (the 10 two-count rows' blocker is a
      re-encoding SHIFT, a design question, not search).  Run
      cascade_probe over the EXP3/EXP4/HIGHER interiors -- still untouched.

  DO NOT RETRY (this wave's additions):
  * The 4 Jp skip rows with a SINGLE V->E chain -- 0 through 32+
    candidates and both landing families; the middle has a second
    turnaround.
  * restscan keys ranked by coverage alone -- alias families (Ip reading
    octave-shifted forms) out-score the true key; rank by regularity
    class first.
  * Reading 8c's "plain-full" rows as one-form families: measured
    two-regime (StA octave bands + StB rests with a growing far of
    ones) on 0RB0LC_1LC1RB_1RD1LA_1LD1LB.  The flat route does not take
    them; the register build will.
  DO NOT RETRY (standing, from earlier waves): everything in
  WAVE26_FINDINGS section 6, WAVE25 section 6, WAVE24 section 7, WAVE18
  section 5, WAVE16 section 5, and the long list in the wave-26 prompt
  (mxdys deciders, emit_graycert, encoding-table widening, overflow-block
  peeling, head-relative frame decodes, halting-transition batching).

THREE STANDING LESSONS (now five waves of evidence):
  * WHEN A TRANSITION TRACES BUT DOES NOT DERIVE, PEEL BEFORE ANYTHING
    ELSE.  The QUAD micro hops and terminals derive ONLY in the peeled
    framing plus a concrete k = 0 chain -- wave-13's split-mode device,
    one level down.  (B->A wave-24; octave-down boot wave-25; two-count
    boot wave-26; QUAD micro wave-27.)
  * When a population is "in model but the search cannot find it", check
    what the search is being asked to PROVE before widening it (wave-16).
  * Read the LANDING off the machine instead of assuming its padding --
    three SKIP boards were recovered exactly that way (WAVE27 section 2).

WHEN STUCK ON A CLASS: print a few machine strings WITH AN
ABSOLUTE-COORDINATE TAPE DUMP (tools/counters/spacetime.py) and ask John.
Hand-inspection is 26-for-26 across waves 8-26.  ASK EARLY, ask with a
TAPE, and ask about a CLASS not a machine.

DEFERRED TO STABLE HARDWARE: census fold-in (gen_proven.py + Deferred regen
+ make census-verify + census_cache --update) -- batch once, it is the only
step that lowers D_census.  Also CloseoutFinal.v (OCaml pin, WAVE16 4b);
the champion 1RB1LD_1RC1RB_1LC1LA_0RC0RD; the carry-shifted one-off
0RB1LC_1LC0LC_0RD1LA_1RD1RB.

Commit + push per validated batch.  Name new files so they cannot clash
with a concurrent session's (recent waves: LAPQ_*, CASC_*, CASB_*, SKIP_*,
QMG_*).
```
