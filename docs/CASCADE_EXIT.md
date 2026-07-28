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

## 4c. The go/no-go gate: CLOSED (wave-24)

**Superseded by §4d below.**  Everything §4c reports still holds as measured;
what it left OPEN is now closed, and two of its structural readings were off
by one level and by one count.  Read §4d first and §4c as the history.

## 4c (history). The go/no-go gate, part-run (2026-07-28, same session)

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

## 4d. The gate, closed, and the route built (wave-24)

**[STATUS, wave-25: BOARDED.  All 57 gated machines carry kernel-checked
`NeverQuasiHaltsSt` theorems (`theories/Machines/Counters/CASB_*.v`),
`D_remaining` 496 → 439; `docs/WAVE25_FINDINGS.md`.  What remains of this
bucket is the 30 non-gated rows of `WAVE24_FINDINGS.md` §5.]**

The extractor went where §4c said it had to -- `nestcert.py`, beside
`phase_mid` -- and **B→A and the base close both derive as single-index
chains**.  §4c's first alternative was the right one; nothing needed two
indices, and no reindex was needed anywhere.

Reproduce: `cascade_probe.py --endpoints 0RB1LA_0LC1RD_1LA1LD_1RB0LA -K 7`.

```
  A→B    index l,   peel (0,0) split 2   4i+4    (§4c's chain, unchanged)
  B→A    index l-1, peel (1,0) split 5   4i+10
  CLOSE  index j,   peel (1,0) split 2   4i+23
  boot 4j+4, inner lap 4i+4
```

**Why B→A resisted, precisely.**  Two framing knobs, and it needs both:

* the **peel** -- how many unit copies sit in `post` rather than in the
  count.  Its turnaround walks back out over cells it has just written and at
  peel 0 runs one short: the window is then blocked and the chain does not
  exist, at any split.  One peeled unit is exactly the room it needs.
* the **split** -- how many cells stay concrete before the opaque tail.  The
  eat reads ONE cell into the growing region (the unit misreads there, and
  that misread is what ENDS the eat), so its split cannot sit where A→B's
  does.  §4b said the turnaround was fixed-size and read only the tail head;
  it reads one cell further.

Both are now searched rather than guessed (`nestcert._frame_pair`), which is
what a per-machine emitter needs anyway.

**Two structural corrections to §1 and §3.**

* The cascade descends to **level 0**, not to level 2.  Levels 1 and 0 are
  invisible to the segment scan only because their runs are 2 and 1 values
  long, under `minlen`.  `cascade_check` predicts all four words of every
  level from the law and finds each one in `phase_mid`'s own configurations,
  down to level 0, at K = 6, 7 and 8.
* The **main count is the level-j second count**: `tail_main = extraB ++ rep
  unit (M - j)` on the nose (`law['main_is_B']`).  So the phase is uniform
  from level j down, the boot lands on B(j), and the induction needs no
  separate entry step -- the ENTRY chain the extractor derives independently
  comes out equal to B→A, same framing and same chain.  §1's "main count,
  then TWO per level" is really "TWO per level, from level j down, and the
  first A is missing".

**Population.**  `cascade_probe.py --gate` reads the law, checks it at every
level, derives boot + lap + all three chains and replays the whole cascade
against the raw simulator at j = 2..8 (77 counts, 1433 inner laps per
machine): **57 of the 87** gate end-to-end, and `cascade_emit.py --proto`
turns all 57 into a Coq overflow branch the kernel accepts -- 57 compile,
none fails.  The 30 that do not, at K = 7:
12 report a main count at `2^(j-1)..2^j-1` (an octave-shifted top level --
`families()` already carries an `oct` for that shape, so this is emitter work,
not new theory), 17 report one or two counts in the phase (the "no boot
chain" mirror half and the 15 odd-shaped rows), 1 a main count at 4..7.

**The Coq.**  `theories/Counters/NestedLapCascade.v`, additive and
funext-only: `fill_hop`, `level_hop`, `cascade_down`, `cascade_overflow`,
`cascade_vis_at`.  `D l m` carries the level and the tail length as SEPARATE
`nat`s -- they move together, so one index would force `j - l` into an anchor
and that is the wave-15 index-shift trap in a new costume.

`tools/counters/cascade_emit.py` renders the branch per machine, and
`theories/Tests/CASC_0RB1LA_0LC1RD_1LA1LD_1RB0LA.v` is the exemplar's,
committed and kernel-checked: `lapo_` proves the `LapStep` obligation for an
overflow phase with `2j+1` counts, `Print Assumptions` =
`functional_extensionality_dep`.  It is a REGRESSION, not a board -- it
carries the overflow branch only, so it moves `D_remaining` by zero.

**What is left to board these machines** (wave-25): wire the branch into
`emit_lapcert.derive`/`render` as a third route beside `nested` and `offset`,
so a full board gets its interior branch, bootstrap, visit witnesses and
closer.  The visit witnesses are the one piece with a new shape:
`cascade_vis_at` is stated at an arbitrary level, but only level 0 is
available at EVERY outer index, so states that fire nowhere in the boot must
fire in the closing sweep.

## 5. Do-not-retry, refined

* The fixed-N multi-count route on this bucket stays dead (wave-22's 0 of
  87) — the count of counts is `j`-dependent.
* `derive_chain` widenings stay dead (§4b) — the exit half is genuinely
  exponential in steps.
* What is NEW here and not covered by those negatives: negative-octave
  family search with deep (`~2j`-cell) tails, and the level induction.
