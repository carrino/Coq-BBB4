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

## 5. Do-not-retry, refined

* The fixed-N multi-count route on this bucket stays dead (wave-22's 0 of
  87) — the count of counts is `j`-dependent.
* `derive_chain` widenings stay dead (§4b) — the exit half is genuinely
  exponential in steps.
* What is NEW here and not covered by those negatives: negative-octave
  family search with deep (`~2j`-cell) tails, and the level induction.
