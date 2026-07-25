# Machine notes — wave-8 hand inspection log

_Written 2026-07-24.  Every machine below was eyeballed by a human on
bbchallenge and/or traced by simulation during the wave-8 residue push.  The
human reads repeatedly out-diagnosed the automated analysis and each one
exposed a TOOLING gap rather than a hard machine — that pattern is the main
lesson here.  Keep appending: this log is cheap to write and expensive to
re-derive._

Format: `machine` — human read → measured structure → consequence.

---

## The lesson, stated once

Three times this session an entire class looked "hard" and was actually a
recognizer/parameter failure:

1. **1,105 sawtooth quasihalters** — nobody had ever run `bin/irules` over the
   residue.  One sweep decided them.
2. **Counter recognition 7% → 70%** — two bugs in the fingerprinter
   (blank-vs-empty far side; interleave parity), both found by a human
   pointing at one machine and saying "that's just a counter".
3. **RepWL wrongly declared dead** — the sweep capped block size at `L<=6`; a
   machine whose tape period is 10 is caught cleanly at `L=10`.  I had already
   written "RepWL cannot finitize these" into the docs; it was a parameter
   artifact.

**Before building anything, check whether an existing tool with different
parameters already works.**

---

## Interleaved binary counters (the bulk: ~1,738 of 2,480 recognized)

- **`0RB0LC_1LC1RB_1RD1LA_0LB0RC`** — human: "binary counter, you can see it in
  the pattern `1, n%2, 1, (n/2)%2, 1, ...`".  Confirmed by anchor sampling:
  value climbs 3, 7, 15, … 511, with carry deltas exactly the powers of two
  {4,8,16,32,64,128,256}.  The canonical shape of the whole family.
- **`0RB0LD_0RC1RC_1LD1RC_0RC1LA`** — human: "just interleaved counter, nothing
  fancy".  **The most valuable single machine of the session.**  At its
  left-wall anchor the right side reads `1, 011, 111, 01011, 11011, 01111,
  11111, 0101011, 1101011` = 2,3,4,5,6,7,8,9.  It was invisible to
  `fingerprint.py` for two reasons, both fixed in `fingerprint2.py`:
  (a) **blank ≠ empty** — the far side is `[S0;S0]`, denotationally blank but
  not an empty list, and the v1 anchor test demanded an empty list;
  (b) **parity** — its digits sit at even offsets (data-first, `d0,1,d1,1,…`)
  rather than marker-first.  Fixing both took recognition 181 → 1,738.
- **`0RB1LA_1RC0LA_0LD1RB_0LA1LD`**, **`1RB---_1LC0RD_1LC1RB_0RB0LB`**,
  **`1RB0RC_0LA0LC_0RD1LB_1LC1RD`** — human: "interleaved counter".  All
  recognized by v2 at data-first anchors, i.e. in the 729-machine group whose
  anchor is not an `Ip`/`Jp` term and so cannot yet be emitted.  A data-first
  anchor is a marker-first anchor **one cell over**; searching the lap for the
  shifted anchor should reclaim them without new Coq.
- **`1RB1RA_0RC1LB_1LA1RD_1RC0LB`** — human: "interleaved counter".  Note its
  state A last fires at 174,742 **and climbing** — it is the log-rare overflow
  state of a NEVER-QH counter, not a quasihalter.  A 50k-step shape classifier
  mislabelled it; log-rare states need a long horizon to distinguish from quiet
  ones.

## Two-sided counters (a counter plus a companion region)

- **`0RB0LA_1RC1LC_1LA0RD_0RC0LC`** — human: "definitely a counter, but the
  left appears to be some function of the counter, like negative".  Measured:
  the right side is the interleaved counter; the **left side is a single `1`
  marker at varying depth** (`10`, `0000000010`, `0000000000000010` = depths
  0, 8, 14) — a position pointer riding alongside.  This is the biggest
  emitter blocker ("no anchor family", 57 of 120 in a batch): the emitter
  assumes the far side is blank.  `glue_neverqh` accepts an arbitrary anchor
  `Cc p`, so a two-sided anchor
  `(edge, (marker-at-depth f p, head, enc p))` is already in scope — only the
  emitter's anchor search needs widening.
- **`1RB1LB_0LB1LC_1RD0RD_1LA0RC`** — human: "counter on the right but like a
  summary of the counter on the left; the left is maybe the negative".
  Measured: RLE at the left-edge anchor gives **1-runs of even length, 0-runs
  of odd length** (`1x1,0x5,1x2` / `1x1,0x1,1x2,0x3,1x2` / `1x2,0x1,1x4`) — the
  value lives in RUN LENGTHS, not in cells.  A distinct encoding class;
  compare the already-boarded `Spacer_16/22/23.v`.

## Doubling-field / exponential counters

- **`1RB1RD_1LC0RC_0RB1LD_1LA0LD`** — human: "a counter with extra lines that
  show up at the top of each column".  Measured: rare anchors whose **times
  double** (t = 4, 12, 32, 76, 168, 356, 736, 1500, 3032, 6100, 12240, 24524)
  at which the tape is a clean `1 0^{2k} 11`; between them it holds an
  interleaved counter (`101010100010(0)10011`).  So a counter fills a field,
  and when full the field doubles.  Routes to the landed `ExpCounter.v` /
  `DblCounter.v` (boarded: Exp_2/4/12, Double_9).  The "extra lines" are the
  field-doubling sweeps.
- **`1RB1LC_1LC1RA_1RD1LB_0LC0RD`**, **`0RB0LB_0RC1LB_1RD0LB_1LA1RC`** — human:
  "counter with some extra lines".  Tape like `11000100000000010001(0)1`:
  sparse 1s with irregular gaps — gap/run-length encoded, same family as the
  spacer class above.

## Periodic bouncers (the RepWL correction)

- **`1RB0LB_0RC1RD_1LC0LA_0RA0RB`** — human: "like a game of life that just
  does `1110110110` repeating".  Exactly right: run-lengths cycle
  `3,1,2,1,2,1`, tape period **10**.  **RepWL catches it at L=10** (490-node
  closure, every state discharged) while failing to even close at L≤6.  This
  overturned the earlier "RepWL is dead on the residue" conclusion — see
  `tools/counters/repwl_bigblock.py`.

## Sawtooths (the 1,100 already boarded)

- **`1RB---_1LC1RD_1LB1RD_1LB0RD`** — human: "basically a 3-state machine with
  a sawtooth, a single 1 at position 0 and head at position 1; A is never
  returned to after the first transition".  Confirmed: no transition targets A,
  so A fires once; B/C/D sweep between the fixed `1` wall and a growing right
  frontier.  `bin/irules` returns `anchor=0` on it at every budget — its
  record-based anchor detector needs two-sided monotone records and a
  fixed-wall one-sided bouncer produces no left record.  A decider-coverage
  gap, not machine hardness.

## Resistant counter exemplars (defeat every generic decider)

- **`0RB0LC_1LC1RB_0RD1LA_1LA1LD`** — carry state D fires every ~24 steps
  (4,097 times per 100k): D is *part of the increment cycle*, not an overflow
  event.  Every abstraction rung closes and A/B/C certify instantly, but D's
  avoiding-subgraph contains spurious D-free cycles at n = 2…8 (closure grows
  42 → 1,118 nodes without breaking the fake cycle).
- **`0RB0LC_1LC1RB_1RD1LA_0LB0RC`**, **`0RB0LA_1RC1LB_1LA1RD_0LB0RC`** —
  behavioural twins whose rare state fires ~15× per 100k at **doubling**
  intervals: true overflow states.  Two different forcing structures from the
  one above, so likely two different fixes.
- **`0RB0LB_1LC1RA_0LD0LC_1RD1LB`** — human: "a counter and a sawtooth
  together".  Measured: a unary wall `1^n` (2 → 6 → 26) plus an interleaved
  digit region that roughly doubles (1 → 5 → 9 → 17 cells), giving extent ∝
  value ∝ √steps.  A wave/bounce counter → `WaveCounter.v` / `BounceCounter.v`
  (boarded: Wave_7/17/27/36, Bounce_8/33).  Only ~1% of the resistant core.

## Still genuinely open

- **`1RB1RC_0LA1LC_0RD0LB_1LB1RD`** — human: "interleaved counter, but the high
  bit is whether the data is in even or odd tape positions".  Resists v2 AND a
  purpose-built parity-flexible decoder (which lets the parity vary per
  anchor), so the whole field shifts rather than just the read offset.  No
  route yet.

## The champion

- **`1RB1LD_1RC1RB_1LC1LA_0RC0RD`** — human: "it's the champ, the 32M one".
  Confirmed: the tape goes **blank at step 32,779,478** in state C after
  spanning ~10,240 cells, then **spins out** — the table has `C,0 -> 1LC`, a
  self-loop, so on the blank tape it writes a 1 and steps left forever
  (verified 12M steps: displacement exactly −1/step, ones exactly +1/step,
  state C throughout).  NOTE: an initial 2M-step simulation showed no blanking
  and I wrongly concluded it never blanks — the event is at 32.8M, far outside
  that window.  **Always size the horizon to the claim.**
  Consequence: A, B, D are quiet with last visit ~32.8M, so it satisfies
  `QHBound 32779479` but never `QHBound 2000` — which is why `boarded` was
  generalized to `exists B, QHBound B`.  Full write-up:
  `docs/COUNTER_EMITTER_WAVE8.md` §7.

## Wave-9 human reads (2026-07-25) — the orientation axes and the state-carried bit

Four reads, each overturning an automated conclusion.  Same pattern as the six
in the log above: the class was never hard, the recognizer was wrong.

- **`1RB1RD_1LC0LB_1RA1LC_0RD1LB`** — human: "right wall and 2 copies of each
  bit."  Exact.  Anchor `Cc p = (StD, (Dp p, S1, []))`, decode marches
  1..7,503 with no gaps, both lap branches affine 4+4j.  This is a THIRD
  encoding (`DpCounter.Dp`, each bit doubled, no marker cells) and it was
  invisible because every decoder here checks that the marker-parity cells all
  hold `S1` — in a doubled tape those cells ARE the data.  Boarded:
  `ILD_1RB1RD_1LC0LB_1RA1LC_0RD1LB.v`.

- **`0RB0RC_1LC1RB_0LD1RA_1RC1LD`** — human: "a 1 to the left of each bit, MSB
  is on the left."  This named an AXIS, not a machine.  The interleave family
  has three independent orientation axes — marker before/after its bit in tape
  order, MSB at which end, counter on which side of the head — and `Ip`/`Jp`
  are one corner of that cube.  At the correct anchor (marker-left, MSB-left,
  1-cell wall) the run is 14,553 long and the interior lap is a clean 2+4j.
  **This machine is in the 298 quasihalting counters that wave-9 had declared
  unreachable**, and its overflow branch splits on the PARITY of j: odd j is
  affine (2+4j), even j costs ~4^k.  Half of that class is template-shaped
  after all.  Sibling in the opposite corner (marker-right, MSB-right):
  `0RB1LC_1LA1RB_0LD0LA_1LB---`, run 14,542, identical up to a 10-step offset.

- **`1RB0LD_0LC1LA_0RC1LA_1RC0LD`** — human: "wall on the right, msb on the
  left, normal counter."  A PLAIN binary counter, nothing between the bits —
  the largest family in `tools/counter_encodings.tsv` (375 `KCOPY1`) and the
  one with no Coq encoding, because every recognizer was built around a marker
  cell it does not have.  Now `KpCounter.Kp`, boarded as
  `ILK_1RB0LD_0LC1LA_0RC1LA_1RC0LD.v`, both branches affine 6+2j.
  **This one also corrected me**: I had it in the doubled-bit bucket.  A
  doubled read of its tape decodes consecutively at one anchor, so the scan
  took it — but only the plain reading makes both branches affine.  A
  consecutive decode is necessary and nowhere near sufficient; the LAP PROFILE
  is the arbiter, not the decoder.  The 34 machines where my scan disagreed
  with `counter_encodings.tsv` should be re-read as plain.

- **`0RB1LC_1LC0LC_0RD1LA_1RD1RB`** — the machine `COUNTER_CLOSEOUT.md` §3
  records as the only one of the 708 still unread.  Human: "appears to
  alternate A and C when moving left, which does produce a weird counting
  behaviour"; earlier, "inverted bits except MSB, which is always 1; MSB on
  the right."  The alternation is real and is in the table:
  `A,S1 -> 1LC` and `C,S1 -> 1LA`, so a leftward run of `S1` is swept with the
  state flipping A/C every cell — the state carries the run length's PARITY.
  That is the mechanism behind the "field advances by one cell as it counts"
  observation, and it explains why no fixed `(stride, offset)` read works: the
  digit boundary moves with the parity, not the tape.
  **Measured, still open.**  A sweep over marker position x MSB end x side x
  wall x suffix x inversion, with the anchor STATE left free (so a
  parity-dependent state would be found), returns no consecutive family at
  all.  So the barrier is the digit alphabet, not the state — consistent with
  the closeout's note that 2-cell slots read as a THREE-state digit
  (`11`->0, `01`/`10`->1, `00`->2) give 2,4,6,8,10,12,14.  Next probe: a
  base-3 (or parity-shifted binary) digit, not another orientation.
  `glue_neverqh` takes an arbitrary `Cc p`, so a parity-dependent anchor state
  is legal if a decode is ever found.
