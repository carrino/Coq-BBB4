# The exponential exit is a descending-octave CASCADE (wave-23 reconnaissance)

_Measured 2026-07-28 on branch `claude/residue-list-refinement-cxzdax`,
after the wave's 15 boards landed.  Reproduce everything with
`tools/counters/cascade_probe.py` (`--classify` for the bucket,
`--timeline SPEC -K 7` for one machine).  This is the design brief for the
next wave on the exp-counter front — the biggest decoded population left
(132 `AFFINE`/`EXP2` of the 496)._

## 1. The finding

WAVE18 §4b measured the `no exit chain` (65) and `no boot chain` (22)
halves EXPONENTIAL and said the inner family is mis-identified at one end.
Wave-22 measured the fixed-N multi-count route at **0 of 87** and filed
them as "identification, not chains".  Both were right, and the actual
structure is now measured.  One outer overflow phase is:

```
main count    2^j .. 2^(j+1)-1        tail 001
level j-1 :   TWO counts 2^(j-1)..2^j-1     tails 10101, 00101
level j-2 :   TWO counts 2^(j-2)..2^(j-1)-1 tails 1010101, 0010101
...
level 2   :   TWO counts 4..7         tails (10)^(j-2)+01-shaped
closing sweep to the outer successor
```

(`--timeline 0RB1LA_0LC1RD_1LA1LD_1RB0LA -K 7` prints this verbatim; the
per-level tails grow by exactly one `10` unit per level.)

* The STEP cost is `Θ(2^j)` — §4b's exponential, confirmed.
* The NUMBER of counts per phase is **affine in `j`** (~`2j`), which is
  why `nestcert.MAXCOUNTS = 4` could never express it: no fixed list of
  chains covers a `j`-dependent count of counts.
* The cascade was invisible to `nestcert.families` for two mechanical
  reasons: it only searches octaves **≥ 0** (`2^(K-1+o)`, `o ≥ 0`; the
  cascade runs BELOW the main octave), and its key tails are capped at
  `MAXTAIL = 3` (the cascade tails are 5, 7, 9, … cells).  Note wave-18
  §5's "maxtail = 6 boards zero" negative was measured on the
  `no inner family` bucket — it does not cover this shape, and stays
  valid for what it measured.

## 2. The census of the bucket

`cascade_probe.py --classify` over the 87 `no exit chain` + `no boot
chain` rows: **72 CASCADE, 15 other** — and the cascade machines are
strikingly uniform (dominant octave-multiplicity profile
`2^(j-1):2, 2^(j-2):6, 2^(j-3):10, 2^(j-4):14`, i.e. arithmetic — the
raw counts include octave shadows; the deduped per-level multiplicity is
TWO, plus shadows).  Nearly all are `Jp`-decoded, in three big transition
sub-families.

The 15 "other" have distinct shapes (single stray octave runs, or
`2^K:x3`-type profiles) and should be re-probed individually.

## 3. The design (next wave's build)

The fractal lesson (`docs/HOLDOUTS_FRACTAL.md`) applies verbatim: *a
carry of length m is not a gadget — it IS the machine one level down.*
The cascade needs a LEVEL INDUCTION, not more chains:

* **`Counters/NestedLapCascade.v`** (additive): an induction over the
  level `l` composing, per level, `inner_to_fill_lift` at `v0 = pow2 l`
  (ALREADY stated at arbitrary `v0` — nothing to generalize) with two
  inter-count chains whose ssides are UNIFORM IN `l` — the growing tails
  are `rep unit l ++ base`, exactly what an sside's `a*l + b` count
  carries.  The conclusion is one `csteps`/`stepn` run from the last main
  fill to the outer successor, i.e. a drop-in exit for
  `nested_overflow_lift` (whose `Hexit`, like its `Hboot`, is just a run).
* **Emitter**: detect the cascade (negative octaves, deep tails — the
  probe's `segments`), derive the per-level chains at two consecutive
  levels and check they are the SAME chain (uniformity), derive the base
  case (level 2) and the closing sweep concretely, and validate every
  level of every phase against the raw simulator at `j = 2..7` — the
  wave-18 validation discipline unchanged.
* The 22 `no boot chain` machines are expected to be the mirror image
  (a cascade BEFORE the identified count); the probe classifies 72 of the
  joint 87 as cascade without distinguishing ends — the emitter should.

## 4. Where else to point the probe

* The **60 "no inner family" survivors** (32 with "no family under any
  route") — the cascade detector sees families the `families()` octave
  window cannot; some of the 32 may simply BE cascades with no clean main
  count.
* The **EXP3/EXP4/HIGHER interiors** (29 rows) — if a lap's cost is
  `Θ(3^j)`, a two-per-level cascade (`1 + 2` copies per level) is exactly
  the kind of structure that produces it; the probe's octave profile will
  say.

## 4b. The transition mechanics, traced (and a correction)

Raw-stepping one A-fill → B-start transition (the excursion between
blank-head configs; `scratchpad` trace, machine
`0RB1LA_0LC1RD_1LA1LD_1RB0LA` at K=7) shows the per-level transitions are
NOT whole-tape sweeps (an earlier read of the blank-head dump suggested
they were — only the ENTRY transition from the main fill is):

* a cycle EATS the counter digits (`(1,0)` units, count affine in the
  level `l`) and STOPS at the tail head (the unit misreads there);
* a FIXED-SIZE turnaround window at the tail head does the level's whole
  arithmetic — A→B flips the tail's head cell `1→0`; B→A(l-1) consumes
  one digit and grows the tail by one `01` unit;
* a cycle LAYS the region back (count affine in `l`), and the REST of the
  `(01)^m` tail is never read — it is exactly the OPAQUE region the
  existing `sside` language already quantifies over.

Consequence: the big cluster needs NO new checker language.  Per level,
single-index chains (index `l`, tail opaque) + `inner_to_fill_lift` at the
level's family (tail opaque to the counts too); the entry chain is a
one-off at index `j`; the base close is concrete-plus-index-`j`.  The new
Coq is only a small cascade-chaining lemma (composing `exists n, stepn`
runs down the levels) and per-level reframing glue that is pure `rep`
algebra (`rep_add`-style, like the boards' existing `gbo_`/`gxi_`).

**How much of the 132 one construction covers** (John asked whether each
machine really needs a direct look — the measured answer is no): the
cascade covers ~72 (the big uniform `Jp` cluster — ~55 sharing the exact
octave profile, many single-transition variants — plus most of the second
group); the 5 `SCycR`-entry-offset machines share one checker extension;
the open remainder is the 60 "no inner family" survivors (point this
probe at them first) and the 15 odd-shaped rows.  Direct per-machine
looks should only be spent on what survives those.  mxdys' deciders made
this look easy because they synthesize per-machine rule systems from the
exact forward behavior — the emitter-per-machine + kernel-recheck route
is our equivalent, and per-machine differential validation stays the
discipline.

## 4c. The go/no-go gate, part-run (2026-07-28, same session)

The critical uniformity question — do the per-level transitions derive as
single-index chains in the EXISTING language? — was tested directly on
`0RB1LA_0LC1RD_1LA1LD_1RB0LA` (mirrored, `Jp`, count state `A`,
`el=False er=True`, index := the level):

* **The A→B transition DERIVES, exact (no lift):**

      FROM (StA, ((), uS, 1, 0, soS ++ [1]), S0, far)     -- A-fill, tail head 1
      TO   (StA, ((), uD, 1, 0, soD ++ [0]), S0, far)     -- B-start, tail head 0
      chain [SRotL 1; SWin 1; SCycL 2 0; SWin 2; SCycR 2; SWin 1; SUnrotL 1]

  with the `(01)^m` tail OPAQUE on both sides.  This is the load-bearing
  half of the design: the level-uniform chain exists.

* **The B→A(l-1) transition did not derive at the first framings tried.**
  The raw trace says why the framing is delicate: the eat runs through the
  digit region AND the repaired tail region, the turnaround writes `010`
  rightward (3 cells, states B→C→D on this machine), and the relay lays
  one `1` per cell.  The two scratchpad trace scripts disagreed on
  blank-head numbering before this was resolved — endpoint extraction for
  BA (and the base close) must be built INSIDE `nestcert` where
  `phase_mid`/`rstrip0` conventions are single-sourced, not in ad-hoc
  probes.  Until that is done it is OPEN whether BA is one single-index
  chain (the A→B result makes it likely), a two-piece chain pasted with a
  reframing equality, or genuinely two-index.

Next session: build `cascade endpoints` in `nestcert.py` (the analogue of
`endpoints()` for the four per-level sconfs), gate BA/base there, and only
then write the composition lemma and template.

## 5. Do-not-retry, refined

* The fixed-N multi-count route on this bucket stays dead (wave-22's 0 of
  87) — the count of counts is `j`-dependent.
* `derive_chain` widenings stay dead (§4b) — the exit half is genuinely
  exponential in steps.
* What is NEW here and not covered by those negatives: negative-octave
  family search with deep (`~2j`-cell) tails, and the level induction.
