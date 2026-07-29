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

### 3c. The whole bucket, measured: 53 read, and every one of them is nested

`regscan.py --laps` over all 113 rows of the `no overflow phase` bucket
(`tools/counters/reg113.json`):

| n | frame law | what the laps cost |
|---|---|---|
| **35** | `grow-11` | far grows `[S1;S1]` per octave; one overflow direction `Theta(2^j)` |
| **8** | `grow-11+virt` | growing far AND a virtual anchor; BOTH its laps `Theta(2^k)` |
| **4** | `plain+virt` | constant frame, virtual anchor; the lap INTO it `Theta(2^k)` (114, 240, 494, 1004 at k = 4..7), the way out 4 steps flat |
| **4** | `period-2+virt` | John's exemplar class; 2 with both virt laps exponential, 2 with the way out exponential |
| **2** | `plain` | constant frame, overflow `Theta(2^j)` |
| 24 | `drift` | the frame moves by no law this scan knows |
| 36 | `short` | the chase never advanced past its seed — see below |

**53 rows read cleanly and 53 of 53 carry at least one `Theta(2^k)` branch.
Not one is four ordinary chains.**  That is the answer to prompt item (0),
and it is not the answer the prompt expected.

Two further things the split says:

* **"Register" is the wrong word for 43 of the 53.**  `grow-11` and
  `grow-11+virt` do not cycle through a finite set of frames: the far side
  GAINS one `[S1;S1]` block per octave.  That is a wall that grows with the
  counter, and it states as `Cc p = (q, E p ++ tail, S0, rep u (size p - c))`
  — a different `Cc` from the finite union the prompt describes, with a
  `Pos.size_nat` argument rather than a residue.  Only the 4
  `period-2+virt` rows are the two-form family John read.
* **The 36 `short` rows are the READER's limit, not the machines'.**  The
  chase demands a blank-head rest with the counter word ending exactly at
  the head (`E p ++ tail` on the near side); 25 of the 36 stall at the seed
  itself.  These are WAVE26 section 8c's mid-tape rests — the head sits
  INSIDE the frame — and reading them needs the head-anywhere decode that
  section asked for and this scan does not have.  Nothing here says they are
  hard; it says they are unread.

### 3d. What the next wave should build

Not "a `Cc` with a register argument and one extra lap shape per register
step".  The piece that is missing is the composition:

    piecewise Cc  (VIRT arm + framed arm)   x   a NESTED branch

`SkipGlue` gives the p0-fenced `reach_ovf` / `vis_via_ovf` for the virtual
arm; `NestedLapLift` gives boot + inner-counter induction + exit for the
exponential branch; `glue_neverqh` closes an arbitrary `Cc`.  What does not
exist is an emitter that puts a nested branch inside a piecewise `Cc` --
`nestcert` assumes the single-`Cc` template throughout.  That, plus the
head-anywhere decode for the 36, is the register wave.

## 3e. Same session: the QUAD 35, re-measured at their own gates

Since §3 demoted the register build, the QUAD emitter extensions become the
next wave's top item — so they got the same treatment.
`tools/counters/quad_classes.py` runs `quad_probe.read_law` over the 35 and
reports the FIRST gate each row trips plus the per-class shape behind it:

| n | gate | what `read_law` says |
|---|---|---|
| **16** | `stride-2` | `Bp` / `Alph_00_10_1`, `mode = (-1, False)`, `cls = 21111`, mark law `(2,1)/(2,3)` or `(2,2)/(2,4)` |
| **12** | read fails | "term counts fit no affine law" — the double ladder, exactly as WAVE27 §3 named it |
| **4** | passes every early gate | `Kp`, `cls = 11111`, mark law `(1,1)/(1,2)` — the boarded shape, and they fail LATER, on `right sides are not rep RU k ++ RPOST` |
| **3** | `deep-pivot` | `mode = (1, True)`, mark law `(1,0)/(1,1)` |

The counts reproduce WAVE27 §3 exactly (16 / 12 / 4 / 3), which is worth
having independently.  What is new is the shape of the 16:

**the "parity-class" 16 need three things at once, not one.**  Every one of
them is a 2-cell alphabet (`len uS = 2`, so `rep RU k` slides two cells at a
time), carries a parity class in `micro` (`cls = 21111` — the parity is in
the MICRO hop only, never in `term`/`ovf`/`boot`), and has a DOUBLED
mark-count law (`nint = (2, _)`, `novf = (2, _)`) instead of the plain
ladder's `(1,1)/(1,2)`.  Wiring "per-parity chain pairs and the `k = 2i+r`
reindex" is necessary and not sufficient: the 2-cell stride and the doubled
mark law are two more gates in front of it, both in `quad_emit.extract`.

The 4 non-rep rows are, by contrast, one gate deep — they read as the
boarded shape all the way to the right-side test.  They are the cheapest
QUAD rows and should go first, and this wave took the first step for them.

### 3f. The 4 non-rep rows: the right-side gate was PADDING, and it is fixed

Their ladder right sides, measured (`0RB0LA_1RC1RB_1LA0LD_0RB1LD`, and the
other three are identical):

    k = 0   [S1]           k = 3   [S1;S1;S1;S1;S0]
    k = 1   [S1;S1;S0]     k = 4   [S1;S1;S1;S1;S1;S0]
    k = 2   [S1;S1;S1;S0]  ...

That IS `rep RU k ++ RPOST` with `RU = [S1]` and `RPOST = [S1;S0]` — for
every `k >= 1`.  At `k = 0` the ladder's first rung has not written the cell
past it yet, so the rung is one trailing BLANK short.  `extract` took the
stride off `rs[1] - rs[0]`, which with that missing blank reads `RU` two
cells wide, and then the test fails on every rung and reports a shape
mismatch that is not there.  **Read the landing, not its padding** — again.

Fixed: the stride comes off two rungs that are both fully written
(`rs[2] - rs[1]`), `RPOST` is what is left of `rs[1]`, and the rungs are
compared up to trailing blanks.  Regression: all 6 committed `QMG_*` boards
re-render **byte-identical** and recompile; the 4 rows now clear the
right-side gate and stop one gate deeper, at `no BOOT1 chain`.

That gate was the same thing one level in, and it is now fixed too.  Every
chain stated at `k = 0` (`BOOT1`, `BOOT0`, `BOOTO`, `MC1z`, `MC0z`, `TCz`)
asked for the right side `RPOST = [S1;S0]` where the machine is at `[S1]`.
`Cq` is now PIECEWISE in `k` — the `k = 0` arm carries the MEASURED first
rung `rs[0]`, every `k >= 1` arm the canonical `rep RU k ++ RPOST` — and the
six chains are stated against `rs[0]`.  (`rstrip0 RPOST` is NOT the right
value and breaks all six committed renders: that trailing blank is a real
written cell on most boards, and it is missing only at `k = 0` and only
because the ladder has not reached past itself.  Read the landing.)  On a
board whose first rung is fully written the two arms coincide, so the
rendered text is unchanged — checked, all 6 `QMG_*` re-render
byte-identical after both fixes.

**All nine chains now derive on all four rows.**  What is left is one named
lemma.  The visit gate reports:

    no visit witness for state A (fires in MC0p,MC0z,TCp,TCz,BOOT0)

on every one of the four (states A, D, B, C respectively).  `quad_emit` only
ever looks in the `BOOTO` prefix, because `LapCertGlue.vis_via_ovf` is the
only carrier the QUAD board has — and the state these rows are missing fires
INSIDE the ladder (the `MC0*` hop onto the stop cell and the terminal), not
in the boot.  So they need a ladder-aware witness: run the anchor to the
rung `Cq W k m` that `quad_lap`'s `mrun` already passes through, then fire —
the exact analogue of `NestedLapLift.vis_via_fill`, which is what the nested
route needed for the same reason.  A `vis_via_quad` in `QuadGlue` plus the
bullet that uses it, and these 4 board.

(The emitter now NAMES where the state fires instead of just refusing, so
the next wave does not have to rediscover this.)

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
* **Expecting any branch of the register bucket to be a chain.**  Measured
  over the whole 113: of the 53 rows the chase reads, 53 carry a
  `Theta(2^k)` branch, at every frame assignment tried.  Budget for the
  nested composition from the start.
* **Calling a virtual anchor flat because the lap OUT of it is short.**  The
  4 `plain+virt` rows leave the virtual anchor in 4 steps and REACH it in
  `Theta(2^k)`.  Both laps have to be checked.
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
