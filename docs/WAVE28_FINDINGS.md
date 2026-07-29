# Wave-28: the PEELED overflow, and the register step measured

_Branch `claude/residue-reduction-4-2-2dp48i`, 2026-07-29.  Wave-27 built the
SKIP and QUAD routes and re-ranked the residue, putting the register×counter
build at the top and John's `Alph_00_01_1` read ("cheapest first") under it.
This wave takes the cheap one — and it turns out to be a route, not a
one-off — then measures the register bucket properly and finds the build the
prompt asked for is **one piece bigger than the prompt thought**._

## 1. The one-line result

**21 new boards, all first render, all funext-only, no new library Coq.**
`D_remaining` **319 → 298**.  One emitter extension
(`emit_lapcert._peel_ovf` + the `PEEL_*` template arms), two new scans
(`tools/counters/jexcept_scan.py`, `tools/counters/regscan.py`).
`LapDecider`, `LapCertGlue`, `SkipGlue`, `QuadGlue` and every other library
file are **untouched**; nothing under `theories/Census/` was touched and
`census_cache --check` stayed MATCH throughout.

(The wave opened at `D_remaining` = 319, not the 323 the wave-27 prompt
states: `main` had picked up four more boards in PR #55 before this branch
was cut.)

## 2. The PEEL, on the overflow branch — the whole of item (2)'s first bullet

John's wave-27 read of `0RB0LB_1LC1RD_0RD0LC_1RB1LA` — "a regular counter
with a 0 to the left of every bit, and the carry has to alternate states to
cross these 0s" — was already confirmed mechanically.  What the prompt asked
for was a MEASUREMENT of the shape across the `no inner family` (60) and
`no anchor` (20) buckets, "it may be a batch".  It is a batch, and the fix is
one line of the standing lesson.

### 2a. What was actually blocking them

`tools/counters/jexcept_scan.py` reads the per-`j` lap cost of every
candidate anchor family off the raw simulator and fits an affine law above a
floor.  On John's machine it reproduces his read exactly:

    0RB0LB_1LC1RD_0RD0LC_1RB1LA   Alph_00_01_1@C tail=[0] mirrored
    interior  4j+4  at every j
    overflow  4j+6  for j >= 2, and 8 (not 10) at j = 1

and the `j = 1` overflow anchor is `p = 1`.  Now look at what the flat route
does with it.  `emit_lapcert.confs` peels one unit copy into the overflow
chain's prefix **only when the alphabet's `obS` is 1** (`Kp`, `Dp`, `Mp`,
`Bp`).  Every INFERRED alphabet has `obS = 0`, and so do `Ip`/`Jp` — for
those the chain's count can be EMPTY, and at `j = 0` the anchor is `p = 1`,
the smallest overflow word, where the head has no concrete cell to step onto.
So `derive_chain` returns nothing, `derive` falls through to the nested and
cascade routes, and the row is filed `no inner family at pow2 j`.

**PEEL BEFORE ANYTHING ELSE** (WAVE24 §2, and every wave since).  State the
overflow branch at `j = S j'` with one more unit copy in the chain's prefix
and discharge `p = 1` as one concrete run:

    B0 = pre (rep uS (obS+1)) ++ rep uS j ++ soS ++ tail
    B1 = uD ++ rep uD (S j) ++ soD ++ tail

On John's machine the peeled chain derives EXACTLY, first try, cost `4j+14`
(= `4(j+2)+6`, the measured law reindexed twice).  The unpeeled one derives
at no framing at all.

### 2b. The measurement: 21 of the 80, and 15 of them are not exceptions

`jexcept_scan.py` over `no inner family` (60) + `no anchor` (20):

| n | class | what the laps measure |
|---|---|---|
| **15** | `affine` | BOTH branches affine at every `j` — no exception anywhere |
| **6** | `jexc:i0/o2` | interior affine everywhere, overflow affine for `j >= 2`, one concrete `j = 1` |
| 59 | no anchor family / other | the scan finds no consecutive-value family |

The 15 are the surprise and they carry the batch: rows whose laps are
**exactly affine on both branches** and which every wave still reported as
`no inner family`.  The `j = 1` exception was never the blocker — the missing
PEEL was, and the exception only decides whether the leftover `p = 1` case
needs a different number in its `vm_compute`.

All 21 board.  `emit_lapcert --list --emit` over the same 80 rows: 21 OK, all
first render, all `Print Assumptions` = `functional_extensionality_dep` only.
Costs: interior `4j+4` on 17 of them, overflow `4j+10 .. 8j+16`; alphabets
`Alph_00_01_1` (18), `Alph_000_001_1` (2), `Alph_11_00_1` (1).

The same emitter over the other 239 unproven rows boards **0** — the batch is
exactly where the scan said it was.

### 2c. What the board looks like

Nothing new in `theories/`.  The peel reuses the offset route's reindex holes
(`cview p = (S (S j), None)`, `@NNJ@ = (S j)`) with the FLAT chain, and adds
two per-board lemmas, both `vm_compute`:

* `lapz_<ID>` — the `p = 1` lap, `Cc 1 -> Cc 2` up to `lift`, closed exactly
  the way `boot_` closes (`ceqb` + `ceqb_lift`);
* `visz_<ST>_<ID>` — one concrete visit witness per state at `p = 1`, because
  `vis_via_ovf` needs a witness at EVERY overflow anchor and the peeled
  `viso_` only speaks from `S (S j)` up.

`cview_none_shape p 0 E : p = fill (pow2 0)` (already in `IXPGadgets`) is what
turns `cview p = (1, None)` into the concrete `p = 1`, so the board's import
line gains `IXPGadgets` and nothing else.  Boards are named `PEEL_*`.

Regression: the peel is only ever tried after the plain chain AND its `lift`
twin have both failed, so no previously-boarded row changes route.

## 3. The register × counter build (prompt item 0): measured, and it is
   nested

`tools/counters/regscan.py` is the reader the prompt asked for ("extend
restscan.py to read the register — head-anywhere rests, constant prefix
frames, per-octave forms").  It ended up being written a different way, and
the reason is worth recording.

### 3a. Intersecting rest forms does not read the family; CHASING it does

The first version collected every frame each value was ever seen in and
intersected them per octave.  That is wrong, and measurably so: the run
passes a given value once per OUTER octave, so the intersection mixes
passes.  On `0RB0RD_1LA1RC_1RD1LC_0LC1RA` it offers the clean-looking
two-form family `C@[] | C@[S1;S1]` — and then the `C@[S1;S1] -> C@[]`
overflow never closes, at any floor, because the machine does not land there.

The scan now SEEDS on one rest and walks the family forward, reading each
next anchor's state and far side off the machine (wave-27's own lesson, one
level up).  With the chase the exemplar's structure is unambiguous:

    p       frame        cost of the lap INTO it
    4       StD @ -      11
    5,6,7   StA @ [S1]   27, 8, 4
    8..15   StA @ -      17, 4, 8, 4, 12, ...
    16      StD @ -      19
    17..31  StA @ [S1]   75, 8, 4, ...

Two things at once, and the scan reports both:

* **a period-2 frame** — `StA @ [S1]` on even octaves, `StA @ []` on odd
  ones.  This is John's register, and it is a single cell, not a word.
* **a VIRTUAL ANCHOR at every power of two** — `E (2^k)` is first rested in
  `StD` with an empty far, before the octave's own frame.  That is exactly
  the SKIP route's device (`SkipGlue`), one dimension up, and holding those
  anchors out is what turns an apparent mid-octave change into a clean
  per-octave frame.

### 3b. The register step is `Theta(2^k)` — an inner induction, not a chain

This is the finding that changes the plan.  With the frames chased, the laps
are:

    interior            4j + 4      in BOTH frames, every j
    virt -> octave      4           on odd k
                        4*2^k + 11  on even k   (75 at k=4, 267 at k=6)

The wave-27 prompt expected the build to be "a `Cc` with a register argument
and one extra lap shape per register step", i.e. four ordinary chains and a
piecewise `Cc`.  It is not: **the lap out of the virtual anchor — the
register step itself — costs `Theta(2^k)`**, so it is a boot + inner-counter
induction + exit, the `NestedLapLift` shape, and no `srun` can express it.
(Checked the other way round too: choosing `StA@[S1] / StA@[S1;S1]` as the
two frames instead moves the exponential from the even octaves to the odd
ones.  One of the two directions is always exponential — the register mark
cannot be moved without a pass that counts.)

So the register×counter board is

    Cc p = match pexp p with Some k => VIRT k | _ => (q, E p ++ tail, S0, reg p) end

with `reg p` the period-2 far, and FOUR branches: interior (2 flat chains,
one per frame), virt-in (flat), virt-out (NESTED).  Every piece exists
(`SkipGlue`'s p0-fenced reach/vis for the virtual anchor, `NestedLapLift` for
the register step, the piecewise `Cc` + `glue_neverqh` closer from the SKIP
route) — but composing the nested branch with a piecewise `Cc` is a build,
not an emitter extension, and it is the next wave's main job.

### 3c. Two further shapes the chase names

Besides `period-P (+virt)`, the chase separates out:

* **`grow-<u>`** — the far side GROWS by a fixed unit per octave
  (`+11/oct` on `0RB0RD_1LA1RC_1RD1LC_0LC1RA` and
  `0RB1LA_1RC0LA_1LD1RB_1LB1LD`): a wall that gains one block per octave, not
  a register that cycles.  `Cc p = (q, E p ++ tail, S0, rep u (size p - c))`
  states it; whether the laps then derive is unmeasured.
* **`drift`** — the frame moves by no law the scan knows.  These are the rows
  to hand to John with a tape.

The full per-row split over the 113 is `tools/counters/reg113.json` (see §5).

## 4. Do-not-retry, extended

* **The un-peeled overflow chain on any `obS = 0` alphabet.**  Measured: 0
  of the 21 derive without the peel, 21 of 21 with it.  This is the sixth
  bucket in a row where one peeled unit copy was the whole difference.  The
  peel is now tried automatically inside `derive`; do not go looking for a
  wider framing search before checking that it fired.
* **Reading a register family by INTERSECTING per-value rest forms.**
  Measured on `0RB0RD_1LA1RC_1RD1LC_0LC1RA`: the intersection names a
  two-form family whose laps do not close at any floor, because it mixes two
  different passes over the same value.  Chase the family instead.
* **Expecting the register step to be a chain.**  Measured on the exemplar
  John read: `4*2^k + 11`, at both frame assignments.  Budget for the nested
  composition from the start.
* Standing: everything in WAVE27 §5, WAVE26 §6, WAVE25 §6, WAVE24 §7,
  WAVE18 §5, WAVE16 §5.

## 5. Standing lessons, confirmed again

* **Peel before anything else.**  Sixth wave running, and this time it was
  worth 21 boards for ~40 lines of emitter.
* **Read the landing off the machine.**  Wave-27 recovered three SKIP boards
  that way; this wave it is the difference between a register family that
  exists and one that does not.
* **Measure the bucket before designing for it.**  The prompt ranked the
  register build first on the expectation of four ordinary chains; one
  afternoon of measurement says one of the four is an induction.  The
  measurement is cheap and the build is not.
