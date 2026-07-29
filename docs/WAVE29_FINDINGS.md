# Wave-29: the QUAD bucket, read at the right rungs

_Branch `claude/residue-reduction-4-2-ao95wq`, 2026-07-29.  Wave-28 measured
the register bucket, demoted the register build, and promoted the QUAD
emitter extensions to the top of the residue as "the largest no-new-theory
bite".  This wave takes them.  Every gate that fell was a READER gate: the
ladder was there on the tape in each case and the emitter was looking at the
wrong rungs, the wrong index, or the wrong padding._

## 1. The one-line result

**22 new boards, all funext-only, all first render.**  `D_remaining`
**291 → 269**.  `QUAD`/`QUAD` **31 → 9**.

* **16** — the `stride-2` cluster (WAVE28 §3e's "parity-class 16"), §2.
* **6** — six of the twelve `read_law` failures (WAVE27 §3's "double
  ladder"), §3.

One library lemma (`QuadGlue.quad_reach_at`, §3c) and nothing else in
`theories/` outside the board files.  `LapDecider`, `SkipGlue`,
`NestedLapLift`, `LapCertGlue*`, `LapGlue*` untouched.  `QuadGlue` stays
axiom-free (`Print Assumptions quad_reach_at`: closed under the global
context).  Nothing under `theories/Census/` touched and `census_cache
--check` MATCH throughout.  **All previously committed `QMG_*` re-render
byte-identical** after every change (checked at each of the three commits;
10 boards, then 30).

## 2. The 16 `stride-2` rows: THREE gates that were one

WAVE28 §3e measured the cluster and named three things needed at once:

> Every one of them is a 2-cell alphabet (`len uS = 2`, so `rep RU k` slides
> two cells at a time), carries a parity class in `micro` (`cls = 21111`),
> and has a DOUBLED mark-count law (`(2,1)/(2,3)` or `(2,2)/(2,4)`).  Wiring
> "per-parity chain pairs and the `k = 2i+r` reindex" is necessary and not
> sufficient.

It is not necessary either, and none of the three is a property of the
machine.  **On a 2-cell alphabet the probe sets TWO depth records per
digit**, so `lap_marks` returns two marks per rung, in two alternating
states.  Exactly ONE of those states is the ladder's own rung — the one
whose left side slides by a whole `uS`, whose stop block is `sS`, and whose
deepest rung is the anchor's own `E q0 ++ tail`.  Selecting it collapses all
three gates simultaneously: the two micro parity classes merge into one hop,
`2j+2` marks become `j+1` rungs (the plain ladder's count), and the "2-cell
stride" disappears because the ladder's unit IS `uS`.

`quad_emit.extract` now tries each rung state and keeps the one whose whole
structure closes.  On a 1-cell alphabet `qr` is a singleton and the loop is
the old code — which is why every earlier board is unchanged.

### 2a. Three padding gates behind it

All three are the standing lesson, and all three are one line each:

* **the ladder's unit is `uS` ROTATED.**  The boot walks the head some
  number of cells into the leading `uS` block, so the rung's slide is `uS`
  rotated by that many cells (`(1,0)` where the alphabet says `(0,1)`).
  `LapDecider`'s `SRotL` is exactly that move and the boot chain derives it
  without help; the emitter's gate simply demanded `LU = uS` literally.
* **the deepest rung can carry one concrete cell in front of the opaque
  word.**  When the rungs sit on the stop block's FIRST cell, the second one
  rides in front of `E q0 ++ tail` (`WPRE`).  It comes off the boot chain's
  own `post`, which is `sS` minus it, so the two agree and nothing else
  moves.  `WPRE = ()` on the 10 `Bp` rows and `[S0]` on the 6
  `Alph_00_10_1` rows.
* **the OVERFLOW ladder's stop block is the anchor's TAIL**, which is one
  cell shorter than the interior's `sS`.  Its deepest rung therefore runs
  one cell past the written region and NO chain from the anchor can land on
  the family's own two-cell `LSTOP` — the symbolic run can only ever produce
  suffixes of the anchor's own concrete side.  The fix is not in the chain
  search: **append a blank to the anchor's tail.**  It is invisible to the
  machine and to `lift` (`Cc` denotes the same tape, `boot_` closes through
  `ceqb_lift` exactly as before) and it gives that cell a name.  Tried only
  after the unpadded read, so no 1-cell board changes.

All 16 board, first render, `Print Assumptions` =
`functional_extensionality_dep` only: 10 `Bp`, 6 `Alph_00_10_1`, 8 mirrored.

## 3. The 12 "double ladder": it is a DESCENDING ladder, and the reader
   could not see it

WAVE26 §7f and WAVE27 §3 named these twelve from the failure print —
`read_law` reports "term counts fit no affine law" with block counts
descending `…5,1,5 … 4,1,4 … 3,1,3…`, which reads as a second, descending
ladder inside the terminal, and the prescription was "the reader needs to
segment the terminal recursively".

Measured off the tape, there is no second ladder.  There is one ladder, and
it descends.

### 3a. Restore points, not column records

`lap_marks` finds rungs by HEAD-COLUMN RECORDS, which is only a proxy for
the restore point the skeleton is actually defined by (`quad_probe`'s own
docstring: *"the tape content is EXACTLY the anchor's again"*).  The proxy
holds when the probe goes one digit deeper each trip.  These machines walk
out to the DEEPEST digit first and then make SHRINKING round trips, so every
column record is set inside the opening walk and the ladder that follows
sets none.  The whole ladder then lands in what the reader calls the
terminal, and its per-trip counts — descending — fit no affine law.  The
`5,1,5 / 4,1,4 / 3,1,3` in the failure print is the ladder itself, printed.

Reading the restore points straight off the tape recovers a textbook ladder
on all 12, interior and overflow: `j+1` and `j+2` rungs, sliding by `uS`,
`LSTOP = sS`, deepest rung exactly `E q0 ++ tail`.  One measured example
(`0RB0LA_1LA0RC_0LD1RC_1RB1LD`, mirrored, `Kp@A`, `j = 6`):

    rung  t     col   left           head  right
    0     1     -1    11111010       1     0
    1     14    -2    1111010        1     10
    2     25    -3    111010         1     110
    ...
    6     49    -7    10             0     1111110

against which the column-record reader returned marks at `t = 1..7` only —
the opening walk — and called `t = 7..58` the terminal.

### 3b. The hop's index is the REMAINING count, not the probe depth

The second gate is the reason the ladder descends: the round trip runs out
to the deepest UNPROBED digit rather than back to the anchor, so its cost is
`Theta(m)` and not `Theta(k)`.  Measured: hop costs `13, 11, 9, 7, 5, 3` at
`m = 6..1`, i.e. `2m+1`, and the same law on the overflow branch at
`m = 7..1`.  (The boarded regime's costs grow with `k`.)

A chain carries ONE index, so the index has to be `m` — and then the right
side, which the hop touches only at the head-adjacent cell, moves into the
chain's OPAQUE tail (`er = false`, `XR = rep RU k ++ RPOST`).  That is what
lets one chain cover every probe depth at once, and it is why this regime
needs **two** micro chains where the near-pivot regime needs four (the peel
is at the LANDING, not at the start).  Which regime a machine is in is read
off by trying the chains, not declared.

`quad_probe` gained the same choice (`mkey`), so the law reader can fit a
descending ladder too.

### 3c. `QuadGlue.quad_reach_at`: a visit witness at a RUNG

The remaining gate is the one WAVE28 §3f met one level up.  `vis_via_ovf`
carries a witness from ONE chain prefix at the anchor — the boot — and
`visq_` added the terminal via `quad_reach0`.  A state that fires in the
MICRO HOP is in neither.

`quad_reach_at` stops the same ladder walk at an arbitrary rung (a four-line
induction on `k`, dual to `quad_reach`'s on `m`).  The rung to stop at is
forced: the witness has to hold at EVERY overflow anchor, and an interior
rung (`m >= 2`) exists only once `j >= 1`.  The LAST rung, `Cq W j 1`, exists
at every `j`, and a prefix of the `m = 1` hop chain fires from it.
`QuadGlue` stays axiom-free.

### 3d. The emitter wants the SKELETON, not the law

`quad_emit` now asks `quad_probe.read_skeletons` for the ladder's skeleton
(anchor, mode, rung states, mark counts) instead of `read_law`'s full fit,
and tries every skeleton that closes rather than the first.  The step-pattern
fits fail whenever the rungs cycle through more than two states — the
segment between two marks then depends on the rung's residue and no single
template covers it — and **the emitter never used them**: it re-derives every
chain from the measured configurations and validates against the raw
simulator (exact rung configurations and totals, `j = 2..10`, both
branches).  Mark-state periods 3 and 4 are recognised now for the same
reason.

### 3e. Two more reader gates, wired, and the six that are left

Two further shapes were measured and wired while chasing the remaining six:

* **the k = 0 rung can be in a state of its own.**  The boot's last step
  enters it and only the HOP re-enters the rung state proper, so the mark
  states read `C D D D D D D`.  `Cq` carries the state piecewise in `k` —
  exactly as it already carries the `k = 0` right side — and every chain
  that starts at `k = 0` (`MC*z`, `TCz`) is a separate chain already.
* **the right side's rung count can start at `k-1`.**  On a ladder whose
  `k = 0` rung is peeled the first FULL rung is `k = 1` and carries `RPOST`
  alone: `rs = [1], [0;1], [1;0;1], [1;1;0;1], …`, which is
  `rep RU (k-1) ++ RPOST`, not `rep RU k ++ RPOST`.  Read the offset off the
  rungs.

With both, the four remaining `6 marks at J=6, want 7` rows clear every
structural gate — and there the failure print is honest: their terminal
really does contain a second, descending ladder.  **Those four, plus the two
that reported `no TCp chain` from the start, are the genuine double ladder**,
and they are two `mrun` compositions back to back exactly as WAVE26 §7f
predicted: `term_` becomes a `quad_lap` over a second two-index family
rather than a chain.  That is the next wave's QUAD item, and it is six rows
rather than twelve.

### 3f. The QUAD residue is now ONE gate

`quad_emit --list` over all 9 remaining `QUAD`/`QUAD` rows: **9 of 9 stop at
`no TCp chain`**, and nothing else.  Every anchor, every ladder, every boot
and every micro hop derives on all nine; the terminal is the only piece
left, and it is the same missing piece in both sub-families (the six double
ladders need a second `mrun` there, the three deep-pivot rows a terminal
stated on the other side).  A bucket that was seven distinct failure
messages at the start of the wave is one.

    0RB0LA_1RC1LB_1LA0RD_0LB1RD   0RB1LA_1LC1RB_1RD0LA_0LB0RD
    1RB0LD_0LC0RB_1LA1RC_0RC1LD   1RB1LA_1LC0RD_0RA0LC_0LA1RD
    0RB1LC_1LA1RB_0RD0LC_1RD0LA   1RB1LA_0LA1RC_0LD0RC_1LD0RB
    0RB0RA_0LC0LD_1RB1LC_1LD1RA   0RB0RC_1LA1RB_1RC1LD_0LA0LD
    1RB1LA_0LA0LC_1LC1RD_0RB0RD          (the last three: deep-pivot, §4)

## 4. The 3 deep-pivot rows: designed, not built

`mode = (1, True)`, all `Kp`, mark law `(1,0)/(1,1)`.  Their ladder runs
RIGHTWARD: the head walks out left once, then the rungs march back toward
the anchor with the LEFT side growing by `uD` per rung and the RIGHT side
shrinking by `uS`.  Measured on `0RB0RA_0LC0LD_1RB1LC_1LD1RA` at `j = 6`:

    rung  t   col   left       head  right
    0     8   -6    110        1     111110
    1     11  -5    0110       1     11110
    ...
    5     43  -1    00000110   1     0

so the family is `Cq W k m = (qr, rep uD k ++ LPOST ++ W, HH,
rep RU m ++ RPOST)` with `k + m = j - 1`, `LPOST = sD` (the carry, already
written at rung 0) and `W = E q0 ++ tail`.  The hop's cost is `2k+3` — the
LEFT index — so the chain is indexed by `k` with the right side opaque
(`src` right `= RU ++ XR`, `dst` right `= XR`); the terminal and the boots
are ordinary indexed chains with `XR = []`.  There is no `HSTOP`: the head
symbol is the same at every rung.

**No new theory** — `quad_lap` does not care which side is which — but it is
a second board template (`Cq`, `hop_`, `term_`, `qrun_`, `lapi_`, `lapo_`)
plus one extra chain for the `j = 0` interior lap, because the ladder has
`j-1` rungs and vanishes at `j = 0`.  Three rows.

## 5. Do-not-retry, extended

* **Reading a growing far side as the counter's own MSB end** ("one word
  read from the wrong split").  MEASURED AND REFUTED on the register
  bucket's exemplar `0RB0LC_1LC1RB_1RD1LA_0LD1LB`: decoding the WHOLE tape
  as one word (`rev(r) ++ [h] ++ l`), both orientations, every alphabet,
  every tail split and every 0..6-cell drop off the far end, tops out at
  168 / 255 coverage with a solid missing block.  The far grows
  independently of the counter.
* **Segmenting the QUAD terminal recursively as the FIRST move on a
  `term counts fit no affine law`.**  Measured: 6 of the 12 so classified
  have no second ladder at all — they have one descending ladder the
  column-record mark finder cannot see.  Check the mark finder before
  building a second `mrun`.
* **Per-parity chain pairs and the `k = 2i+r` reindex for the `stride-2`
  cluster.**  Measured: 16 of 16 need neither; the parity is the reader
  seeing two records per digit.
* **Widening the chain search when the OVERFLOW ladder's deepest rung will
  not accept `LSTOP`.**  It is a representation gap, not a search gap: the
  symbolic run cannot produce a side longer than the anchor's own.  Pad the
  anchor's tail with a blank.
* Standing: everything in WAVE28 §4, WAVE27 §5, WAVE26 §6, WAVE25 §6,
  WAVE24 §7, WAVE18 §5, WAVE16 §5.

## 6. John's reads this wave (hand-inspection now 34-for-34)

Given live during the wave, on the three classes that did not move:

* **`0RB0LC_1LC1RB_1RD1LA_0LD1LB`** (the register bucket's `drift` 24):
  *"just a counter with 1 to the left of each bit.  msb on the right.  2 1s
  to the right of msb."*  The alphabet is confirmed — the tolerant reader
  names `Ip@B tail=[1] far=[1;1;1]` mirrored, coverage 225, and `Ip` IS
  "1 to the left of each bit".  Its sibling `0RB0LC_1LC1RB_1RD1LA_1LD1LB` is
  in the same 24 and is WAVE26 §8c's confirmed row.  The gap starts at
  `128 = 2^7` because the far grows by `11` per octave; §5 records that the
  growing far is NOT the counter's own high end.
* **`0RB1LA_0LC1RD_0LD1LD_1RB0LA`** (the `short` 36): the head never returns
  to the word's end — it rests INSIDE, at `p = -6/-8`, with a fixed `01` two
  cells to its right that it keeps coming back to.  The decode question for
  the head-anywhere reader is which cell is HOME.
* **`0RB0LD_1LA1LC_0LD0LC_1RD1RB`** (the `no anchor` 19): *"keeps bouncing
  back and forth with c and d states.  then when it passes the wall on the
  right it moves the wall over one and heads back left and then goes back to
  bouncing."*  So the counter is the WALL POSITION and the bounce is the
  measure — `MeasureGlue`/`BounceCounter` shape, not a digit alphabet at
  all, which is why every anchor enumeration in eight waves has returned
  nothing.  That is the bucket's route and it has never been tried.

## 7. Standing lessons, confirmed again

* **READ THE LANDING OFF THE MACHINE.**  Five gates this wave, every one of
  them: a rung one blank short, a ladder unit that is `uS` rotated, a stop
  block one cell longer on one branch than the other, a `k = 0` rung in its
  own state, a right-side count starting at `k-1`.  None was a search
  problem and none needed theory.
* **MEASURE THE BUCKET BEFORE DESIGNING FOR IT.**  Wave-28 ranked the
  `stride-2` 16 as "three gates, not one" and the 12 as "needs recursive
  terminal segmentation".  Measured: the three gates are one gate, and half
  the 12 have no second ladder.  Both readings came from the failure PRINT
  rather than from the tape.
* **The emitter should ask for the least it can use.**  `read_law` fits step
  patterns the emitter throws away, and those fits were the binding
  constraint on a whole cluster.  When a producer gates a consumer, check
  what the consumer actually reads.
