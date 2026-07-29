# Wave-29b: the `no boot chain` bucket is a SOLO CASCADE — 10 boarded

_Branch `claude/cascade-twocount-4-2-r82mvf`, 2026-07-29.  The task was the 18
remaining `no boot chain` rows, whose design brief was `WAVE26_FINDINGS.md` §4:
a two-count overflow whose first count sits one octave down, blocked on a
"shift chain" that measured 0 of 378 framings per machine and was diagnosed as
"a re-encoding pass over a `j`-length word, which a single-index window chain
cannot be at any framing".  The wave's instruction was to name that piece._

## 1. The one-line result

**There is no shift piece, because there is no shift.**  The region WAVE26 §4c
could not chain across is THE REST OF A CASCADE, and the level induction it
needs has been in the tree since wave-24.  Ten of the eighteen rows are one
uniform class, all ten gate end to end, and **all ten are boarded** —
`D_remaining` **266 → 258**, every board accepted by the kernel on the FIRST
render, every `Print Assumptions` = `functional_extensionality_dep` only.  No
library Coq was added or changed.

## 2. What the phase actually is

One outer overflow phase of these machines, at outer index `j`:

```
  level j-1 : ONE count 2^(j-1) .. 2^j-1        tail  extra ++ unit
  level j-2 : ONE count 2^(j-2) .. 2^(j-1)-1    tail  one unit longer
  ...
  level 0   : the single value 1                tail  j units longer
  the MAIN count 2^j .. 2^(j+1)-1, in a SECOND digit alphabet
  -> the outer successor
```

That is wave-24's cascade with **one count per level instead of two** and the
`2^j` count **last instead of first** — precisely the mirror image
`CASCADE_EXIT.md` §3 predicted the `no boot chain` half would be ("a cascade
BEFORE the identified count").  `--timeline`/`--solo` prints it verbatim.

**Why the reader could not see it, mechanically.**  `cascade_segments` keeps
only maximal runs: any run whose mid-index span sits inside a wider run's is
dropped as an octave shadow.  On these machines an octave shadow of the
DESCENT — the same words re-decoded with one extra leading digit, e.g.
`Ip@C tail=[1]` reading `96..127` where the levels read `32..63`, `16..31`, … —
spans the whole descent, so **every real level count is inside it and every one
is dropped.**  What survives is (top level, main count): WAVE26's "two counts in
the phase".  The shadow rule is right when a shadow covers the count it
shadows and wrong when it covers a whole descent.

The fix is `cascade_segments_all` (the same scan, shadow rule off) plus
`solo_runs`, an earliest-start / widest-at-a-start non-overlap scan.  Overlap
alone separates the shadow from the levels, and the widest-at-a-start rule
still takes a shadow where nothing finer starts at its own index.

The reading is checked, not assumed: `solo_check` predicts all four words of
every level from the law and finds each one among `phase_mid`'s own
configurations, in phase order, **down to level 0** and then at the main count's
start.  Levels 1 and 0 run 2 and 1 values and are below `CASC_MINLEN`, so they
are never in the input — finding them is a genuine extrapolation test.  The law
comes out identical at K = 6, 7 and 8 (`unit = 11`, `extra = []`, `M = j`,
levels `j-1 … 0`).

## 3. The measurement, over all 18 (§1's instruction, done first)

The WAVE26 §3 split does not hold three waves on.  Note two of the 18
(`0RB1LC_1LA1RB_0LD0LA_1RA0RA`, `0RB1LC_1LA1RB_0RD0LA_1LB0RD`) are already
settled through `RerootStage` partners, so 16 were unproven at the branch point.

| n | shape | this wave |
|---|---|---|
| **10** | **SOLO CASCADE** (§2) | **all 10 boarded** |
| 4 | one 5-value run `12..16`, `\|mid\| ≈ 1030`, far growing one `0` per octave | §6 |
| 1 | an **ASCENDING** ladder, one count per level, tails SHRINKING | §5 — designed |
| 1 | one octave-down count and nothing else — **not a cascade at all** | §5 — cheapest |
| 2 | `AFFINE`/`HIGHER` | §7 — characterised, and it is decisive |

WAVE26 §4's two working pieces both reproduce on the SOLO 10, and the third
turns out to be three ordinary chains.  Everything below is at K = 7 and is
differentially validated against the raw simulator at `j = 2..8` — 7 overflow
phases, 35 levels, 42 counts, ~967 inner laps per machine, plus the concrete
`p = 1` lap.  The validation bites on all seven cost slots (+1 on any of them is
caught at `j = 2` or `3`).

```
  BOOT   i=n-1  peel (1,0) post 6   4i+6   EXACT  7 steps   <- WAVE26 §4b, reproduced
  DOWN   i=n-1  peel (1,0) post 3   4i+6   EXACT  7 steps   <- the level step
  MAINA  i=n+0  peel (0,0) post 0   4i+{10,12,14}
  MAINB  i=n+mo peel (0,0) post 2   4i+{6,8,12,14}
  lap(level family)  SPLIT: 2 at i=0, 4i+6 at i=S i'     identical on all 10
  lap(main  family)  SPLIT: {4,8,12,14,16} at i=0, 4i+{8,12,…} beyond
```

BOOT and DOWN are the SAME chain on all ten machines,
`SRotL 1 SWin 1 SCycL 2 0 SWin 4 SCycR 2 SWin 1 SUnrotL 1`, at two different
framings.

**A new place for the standing peel lesson: the INTERIOR LAP.**  The level
family's lap has NO chain at the plain `AI0`/`AI1` on any of the ten, and the
reason is structural rather than a search budget: `rep uS i ++ sS` can only be
entered by `SRotL`, which needs the post to begin with the rotated symbol, and
`Alph_01_11_011` has `sS = uD = [0;1]` — it begins with a blank.
`_inner_lap_split` (the wave-22b Z/P device: exact `Z` chain at `i = 0`, peeled
`P` chain at `i = S i'`) takes all ten, and so does the OUTER anchor's interior
lap, which needs `emit_lapcert`'s own `INT_SPLIT`/`GLUE_SPLIT` for exactly the
same reason — these machines' outer alphabet IS the level family's.  Peel before
anything else now applies to laps, not just to transitions.

## 4. Why this needed no new theory, and what it did need

`NestedLapCascade`'s level step is a HYPOTHESIS:

    Hstep : forall l m, exists n, stepn tm n (lift (D (S l) m)) = Some (lift (D l (S m)))

so a level carrying one count is a legal instantiation — `fill_hop` where the
gated route uses `level_hop`.  Everything else was already built:

| piece | where it came from |
|---|---|
| the descent | `cascade_down_all`, unchanged |
| the level step | `fill_hop` (one count) instead of `level_hop` (two) |
| the close | `MAINA` + `fill_hop` at the SECOND family + `MAINB` — the wave-25 `oct = -1` close, at a different alphabet |
| the top level one octave down | the wave-25 reindex: `cview_none_shape`, a concrete `p = 1` lap (`lapz_`), concrete per-state `visz_` witnesses |
| the visit through the whole descent | `cascade_vis`, unchanged |
| both interior laps | `_inner_lap_split` + a tail-parametric restatement of the wave-22b Z/P glue |

The one genuinely new shape in the board is that it carries **two families**:
`Cin` for the levels and `CinM` for the main count, each with its own split lap,
because the main count is in a different digit alphabet at a different state
with a different far side.  `fill_hop` is parametric in the family, so this
costs a second copy of the lap block and nothing else.

Three things the emitter had to READ OFF THE MACHINE rather than assume — all
three the wave-29 standing lesson, none needing theory:

* `Dc l m` carries `m + 1` tail units, so the emitter's `m` at the level a
  `DOWN` step LEAVES is `j - l - 1`: `_xterm`'s `'AB'` offset, not `'BA'`'s.
* The close's `rep` splits must be **constant-first** (`1 + S j`, not
  `S j + 1`): its targets are written `rep u (S (S j))`, which `cbn` peels from
  the front, so the count has to split as `rep u b ++ rep u v`.
* On the one row whose main count sits one octave UP, `MAINB` is framed at the
  MAIN COUNT's own index, one above the outer one — three holes carry that
  (`@CLBI@`/`@CLBIP@`/`@CLBIA@`) and nothing else moves.

## 5. The two rows that are one small step away

* **`1RB1LC_0LC0RB_1LA1RD_1RC0RD` — not a cascade at all.**  Its phase is ONE
  count at `2^(j-1)..2^j-1` (`Alph_00_01_0@A tail=[0;1] far=[1;1;1]`, 16..31 at
  K=6 and 32..63 at K=7) with a short boot in and a short exit out; the lap is
  `4i + 28`, affine and `j`-independent.  This is the plain FLAT nested route
  with the family one octave down — `families()` at `oct = -1` plus the wave-25
  reindex, no cascade and no second family.  **The cheapest row left in this
  bucket.**
* **`1RB0RD_1LC1RA_0RB0LC_1LD0LA` — an ASCENDING ladder.**  One count per level
  going UP, tails SHRINKING by one `11` per level (`tail(l) = [1;1;1] ++ rep
  [1;1] (j - l)`), lap `4i + 2`, affine and `j`-independent; the top level's
  count IS the `2^j..2^(j+1)-1` one, so there is no separate main count.
  Uniform at K = 6 (levels 2..5) and K = 7 (levels 2..6).
  **`cascade_down` already covers it with the two indices SWAPPED**: instantiate
  `D l m := Cin (T l) (pow2 m)` and `Hstep : D (S l) m -> D l (S m)` reads
  `Cin (T (S l)) (pow2 m) -> Cin (T l) (pow2 (S m))`, which is the ascending
  step.  The boot then lands on `D j d0` = the LOWEST level with the LONGEST
  tail and the close leaves from `D 0 (j + d0)` = the top level — both exactly
  what the theorem wants.  The open question is only how far down the ladder
  goes: the scan's floor is level 2 at both K, and levels 1 and 0 would be below
  `CASC_MINLEN`, so `solo_check`-style extrapolation has to settle whether the
  floor is 0 (no extra reindex) or 2 (the wave-25 reindex applied twice, with
  concrete `j = 0` and `j = 1` cases).  **Measure the floor before building.**

## 6. The 4 `12..16` rows: the run is not the counter

`1RB---_1LC1RD_0LB1RD_1LB0RD`, `1RB0RC_1LC1RD_0LB1LA_1LB0RD`,
`1RB0RD_1LC1RD_0LB1RA_1LB0RD`, `1RB1LB_1LC1RD_0LB1RA_1LB0RD`.  The reported run
stays `12..16` at every K while `|mid|` doubles (523 → 1037) and the far side
grows by one `0` per octave.  Its "laps" DOUBLE with the outer index
(`i = 0`: 76 → 156; `i = 4`: 856 → 1704), so the five values are not a counter
at all — each of its steps hides a `Θ(2^j)` run, and the thing that actually
counts is the growing far side.  WAVE26 §3 read this correctly as "a slow count
spanning ~the whole phase with a GROWING far side"; nothing in the cascade
family fits it and no amount of framing will make it.

## 7. The 2 `AFFINE`/`HIGHER` rows: characterised, and it is a hard no

`0RB0LA_1LC1RD_0RD0LC_1RB1LA` and `1RB1LC_0LC0RB_1LA1RD_0LA0RD` are mirror
siblings and share one shape.  Their phase is a SINGLE count at the main octave
`2^j..2^(j+1)-1` (`Alph_00_10_1`, empty tail and far) spanning the whole phase —
and their interior lap's exact step cost, identical at K = 5, 6 and 7, is

    i = 0:4   i = 1:16   i = 2:36   i = 3:72   i = 4:140     i.e.  8*2^i + 4i - 4

**exponential in the CARRY INDEX.**  That settles two things at once:

* it is why the overflow measures `HIGHER` and not `EXP2` — carry index `i`
  occurs `2^(j-i-1)` times in a `2^j`-increment count, so the phase costs
  `Σ_i 2^(j-i-1) · 8·2^i = Θ(j·2^j)`;
* it is why they are not in the exponential-counter model, in one sentence: a
  `LapDecider` chain is a fixed list of steps whose cycle counts are affine in
  the index, so EVERY lap it can certify costs `a*i + b`.  A lap costing
  `Θ(2^i)` is not a chain at any framing, at any alphabet, at any split.

What they are instead is the fractal lesson one level further in
(`HOLDOUTS_FRACTAL.md`): the inner counter's own carry is itself a counter, so
the lap is a CASCADE one level down.  That is a nested-cascade construction —
`cascade_overflow` inside `Hin` — and it is a wave of its own, not a variant.
**Do not spend framing search on these.**

## 8. Do-not-retry, extended

Everything in `WAVE29_FINDINGS.md` §5, `WAVE28_FINDINGS.md` §4,
`WAVE27_FINDINGS.md` §5, `WAVE26_FINDINGS.md` §6, `WAVE25_FINDINGS.md` §6,
`WAVE24_FINDINGS.md` §7, `WAVE18_FINDINGS.md` §5 and `WAVE16_FINDINGS.md` §5
stands, with one correction and three additions.

* **CORRECTION to `WAVE26_FINDINGS.md` §4c and §6.**  The "shift chain" those
  sections could not derive does not exist: the configurations between the
  octave-down count and the `2^j` count are the rest of a descending cascade,
  and they are covered by three ordinary chains (`DOWN` at every level, then
  `MAINA`/`MAINB`) at framings the existing search finds immediately.  §6's
  measurements stand as measurements — no single window chain crosses that
  region, and widening is still pointless — but the conclusion drawn from them
  ("whatever takes these 10 is a NEW piece") was wrong, and it was wrong because
  the reading of the phase came from the failure print rather than from the
  tape.  **MEASURE THE BUCKET BEFORE DESIGNING FOR IT**, again.
* **Do not reach for `MeasureGlue.mrun` on a region a cascade already covers.**
  `mrun` was the obvious instantiation for "unbounded many micro laps bounded by
  a measure" and it is the right tool for the QUAD route's linear-search carry —
  but here the per-level step is a FIXED chain uniform in the level, which is
  what `cascade_down` composes, and reaching for a measure would have added a
  well-founded induction to replace one that was already there.  Check whether
  the existing level induction fits before adding a measure.
* **Do not trust `cascade_segments`' shadow rule on a phase whose shadow spans
  many counts.**  Use `cascade_segments_all` + `solo_runs` when the phase reports
  suspiciously few counts; two runs where the octave profile shows a descent is
  the signature.
* **Do not look for a framing of the `12..16` rows' run (§6) or of the
  `AFFINE`/`HIGHER` rows' lap (§7).**  In the first the run is not a counter; in
  the second the lap costs `Θ(2^i)` and no chain has that cost.

## 9. The numbers

* **10 boarded** (`CASB_*`, 7 mirror / 3 direct), all first-render, all
  funext-only.  Two of the ten were already settled through `RerootStage`
  partners, so the tables move by 8: core undecided **177 → 176** and `0RB`
  shadows **85 → 82** against the branch point's 181/85.
* `D_remaining` **266 → 258**; 4,898 of the frozen 5,156 settled (**95.0%**).
  `inventory.py` / `gen_stages.py` / `audit.py` re-run, audit OK (exact
  partition); `census_cache --check` MATCH throughout; nothing under
  `theories/Census/` touched.
* `theories/Closeout/*.vo` are NOT recompiled on this branch: the stage files
  need the ~559-file board `.vo` closure, the documented ~85-minute one-time
  cost, and this container only needed the ten new boards.  The generated tables
  are audited, which is the check that they say what the prose claims.
* **Regression: 79/79 byte-identical** — the 69 committed gated `CASB_*`, the 9
  solo `CASB_*` from the first boarding commit, and the pinned `CASC_` proto,
  re-rendered and diffed before every commit.  It caught real breakage twice:
  two string replacements had also hit the gated `render_board` and `reps_low`
  (reverted), and parenthesising a new index hole turned `4 * S j' + 8` into
  `4 * (S j') + 8` in all nine committed solo boards (given its own
  unparenthesised hole).  Wave-25, wave-26 and this wave have each checked and
  each caught something.

## 10. What is left of this bucket

8 rows: the 1 flat octave-down row and the 1 ascending ladder of §5 (both
designed, both cheap, the flat one cheapest), the 4 growing-far rows of §6, and
the 2 nested-cascade rows of §7.  None of them is a variant of what this wave
built; the two in §5 are the only ones worth an emitter pass.
