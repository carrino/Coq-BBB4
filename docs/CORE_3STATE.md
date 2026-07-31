# The three-state core rows (`1RB---_...`), and how to finish them

_Written 2026-07-31.  The 24 core rows whose `StA` has an undefined `S1`
transition: after step 1 they are THREE-state machines started on a tape
carrying a single `1`.  This is the map of that population — what they
actually are, what boarded, and what each survivor still needs.  Companion
reading: `COUNTER_CLOSEOUT.md` (the counter route in general),
`WAVE34_REACHSTI.md` (the previous session on these rows)._

## 0. The one fact that reorganises the population

**The 24 rows are 9 sub-machines.**  `StA` fires once, at index 0, and 23 of
the 24 rows are the target of no transition, so everything after step 1 is
the `{StB, StC, StD}` sub-machine running on a tape with one `1` on it.  Up
to relabelling those three states, the 24 rows collapse to **nine** distinct
sub-machines (plus one row that does target `StA`):

| sub-machine (canonical) | rows | boarded | closer |
|---|---|---|---|
| `0LB1RC_0RD0RC_1LB1LD` | 3 | **3** | `Counters/Ter3Wall.v` |
| `0LC1RD_0LB1RD_1LB0RD` | 3 | **3** | `Counters/KpWallAlt.v` |
| `0LC1RB_0LB1RD_1LC0RD` | 3 | **3** | `Counters/KpWallScan.v` |
| `0LC1RD_1LB1RD_1LC0RD` | 1 | **1** | `Checkers/LapDecider.v` (nested) |
| `0LB1RC_1LB0RD_1LC0RC` | 2 | **2** | `Counters/Ter3WallB.v` |
| `0LB1RC_1LD0RC_1LB1RC` | 3 | 0 | — |
| `0LC1RD_1LB1RC_1LB0RD` | 3 | 0 | — |
| `0LC1RD_1LB1RD_1LB0RD` | 3 | 0 | — |
| `0LB1RC_1LB0RD_1LC0RD` | 2 | 0 | — |
| (targets `StA`) | 1 | 0 | — |

Two rows sharing a sub-machine differ **only in their bootstrap**: the entry
from `StA` lands in a different one of the three states, so the trajectory to
the first anchor differs while the lap does not.  That is why every closer
here is ROLE-PARAMETERISED (`qW`/`qC`/`qD` as `St` arguments) and why one
closer + one boot probe boards a whole row-group at once.  `tools/counters`
sibling scans looked for relabellings among *boarded* machines; the useful
question on this population is the relabelling classes of the population
itself.

## 1. What they are

All 24 are **wall counters growing rightward**: cell 0 holds a permanent `S1`
(the wall), the counter's digits live at cells 1, 2, … with the LOW digit
next to the wall, and the head bounces between the wall and the carry
frontier.  The head never visits a negative cell on any of the 24.

The natural anchor is therefore

```coq
Cc p = (q, ([], S1, <counter word>))
```

— the head sitting **ON** the wall cell, nothing to its left.  That anchor's
head symbol is `S1`, and until this session every anchor search in the tree
(`emit_interleave.derive_tail_best` and `_far`, and so
`emit_lapcert.anchors`) hard-coded `h == 0`.  One literal, and it hid the
whole population.  `emit_lapcert.py` now carries the head symbol as `HD`,
searched `S0`-first so no previously boarded row can change route, and
`anchors` proposes every family with a long consecutive-value run rather than
the single best-scoring one.  Regression: a 10-row sample of already-boarded
`LAPC`/`LAPQ`/`NLAP`/`PEEL` rows still derives 10/10, every one of them by
the same encoding and step law as before and none of them by the new `S1`
route.

## 2. The boarded five families

All five are `iqh` — `NonHalt /\ QHBound 2000 /\ QuasiHaltsSt` — **not**
`NeverQuasiHaltsSt`: `StA` fires once and never again, so these machines
genuinely quasihalt, with score 1.  `LapGlueQuiet.glue_qh_quiet` is the
closer in every case (`qa = StA`, `s0 = 0`), and its `AvoidRun` premise is
free from `ReachStI.inv_csteps_all` because the three roles are a total,
closed state set that excludes `StA`.

### `Ter3Wall.v` / `Ter3WallB.v` — base three (3 + 2 rows)

`tools/closeout/residue_map.tsv` calls these "EXP3": read at base 2 their lap
grows like `3^j`.  They are not base 2.  After the wall the tape is 2-cell
digits over `{00, 01, 11}` and the lap is `4j + 4` in the carry length —
`tools/counters/radix_infer.py` measured that over 10^4 consecutive anchor
snapshots a session ago; what was missing was the Coq side.

* `Counters/TernCounter.v` — base-3 numerals `tern`, the carry view `tview`
  (the run of low 2s), the word `Tw` over three digit words and a
  terminator, and TWO increments, because both occur in these rows:
  `tsucc` (no terminator: overflow writes a fresh digit 1) and `tsuccT` (a
  terminator sits past the top digit and the overflow carry clears it too,
  so the fresh digit is a 0).  `TerStep` packages what a lap consumes: one
  trichotomy in single cells, proved for both increments.
* `Counters/LapGlueIx.v` — `LapGlueQuiet` over an ARBITRARY index.  Neither
  it nor `LapGlue` uses arithmetic; `Pos.le` only carries the `p0 <= p`
  guard.  A base-3 counter has no `positive` to index by.

`Ter3WallB.v` is the same radix over a DIFFERENT alphabet — digits
`{00, 10, 11}`, and the increment writes its fresh `1` in the digit's first
cell (`00 -> 10`) where `Ter3Wall`'s writes it in the second (`00 -> 01`).
There the parity IS the branch: the outward clear alternates one cell at a
time and what stops it is the first clear cell, so a digit-0 stop leaves an
even run and a digit-1 stop an odd one.  Base 3's two interior branches are
therefore not two lap lemmas but the two parities of one, both `2k + 2` in
the run length.

### `KpWallAlt.v` / `KpWallScan.v` — the alternating return (3 + 3 rows)

`KpWallQH.v` (wave 34) closed the shape whose carry RIPPLE alternates between
two states.  These two are its siblings:

* **`KpWallAlt`**: the ripple is one state and the RETURN alternates.  The
  two return states agree at the wall, so the parity is invisible: the return
  lemma carries "the state is still one of the two" instead of naming it.
  Lap `2j + 6`, both branches exact.
* **`KpWallScan`**: the return alternates AND its two members DISAGREE at the
  wall — `qQ` bounces into the ripple, `qP` bounces into itself.  Lap
  `2j + 2` for even `j`, `2j + 4` for odd (`residue_map`'s "PARITY-AFFINE").
  The parity still never reaches the anchor: a `qP` bounce runs one cell out
  onto the counter's low cell, which an increment with `j >= 1` has just
  cleared, so `qP` turns straight back and hands to `qQ` at the same anchor.

**Why `Checkers/LapDecider.v` cannot take any of these six.**  Its `SCycL` /
`SCycR` steps require the unit run to return to the state it started in.  An
alternating sweep does so only every second cell, so no chain over a
`rep u (a*j+b)` block can express it.  A fixed 2-cell unit would cover only
even runs, and `j` is universally quantified.  This is a real expressiveness
gap, not a search gap — the alternative would be a state-SET in `sconf`,
which changes `srun_sound` and every step's soundness lemma.

## 3. The 12 survivors, and what each needs

Measured with `tools/counters/radix_infer.py` and by hand-reading traces.

**The flat wall reading is measured absent — but read the caveat.**  A search
over the TRUE wall anchor (head at cell 0) for all four surviving
sub-machines, across anchor state, anchor head symbol, radix 2–4, digit width
1–3, terminator length 0–2 and 0–2 padding blanks past the top digit, finds
**no consecutive-value decode** on any of them.  The same search finds base 3
immediately on the two `Ter3Wall*` groups.

The caveat is the one the `StA` row taught (§3 last entry): every scan named
above pins the anchor's head to a fixed offset from a tape END.  A counter
read AT THE CARRY straddles the head and is invisible to all of them.
`tools/counters/carry_anchor.py` searches that shape and finds it on the
`StA` row — and on **none** of these four sub-machines, with run-units `1`,
`11`, `01`, `10`, `111` and eight digit-pairs.  So the nested diagnosis
survives both searches, but "no flat reading" now means "no flat reading at
the wall AND none at the carry", which is a stronger and better-founded
statement than it was.

### `0LB1RC_1LB0RD_1LC0RD` (2 rows), `0LB1RC_1LD0RC_1LB1RC` (3 rows)

`residue_map` reads both as `Dp` (each bit in two identical copies) and calls
them "HIGHER".  That label is a PARTIAL fit: sampling
`1RB---_0LB1RC_1LB0RD_1LC0RD` at the wall gives the words

```
(empty), 1, 11, 011, 111, 0011, 1011, 1111, 00011, 10011, 11011, 01111, …
```

which are plain `Kp` words — a binary counter, low bit at the wall, top bit
as terminator — and only the subsequence that happens to pair up as
`00`/`11` looks like `Dp`.  So the counter reading is fine.  What is wrong is
that **the wall is not where every increment shows**: those words decode to

```
1 | 3 | 6,7 | 12,13,15 | 24,25,27,30,31 | 48,49,51,54,55,60, …
```

— a sparse self-similar set, each block twice the previous.  Consecutive wall
visits are therefore separated by a whole sub-epoch, which is why the lap
measured at that anchor is super-affine: `6, 16, 36, 82, 196` steps at carry
lengths `0..4`.  The open question is not "is it a counter" but WHERE the
anchor makes every increment visible.  A lap that
grows like that is a NESTED counter — the outer increment runs an inner one —
which is what `Counters/NestedLap*.v` and `nestcert.py` exist for.  The
nested route in `emit_lapcert.py` is currently `S0`-anchor-only (it is
refused outright when `HD = 1`, see the guard): `nestcert` states its INNER
anchor with a literal `S0` head of its own, and that head is genuinely
independent of the outer one.  **Threading a second head symbol through
`nestcert` is the sized next piece for these five rows.**

### `0LC1RD_1LB1RC_1LB0RD` (3 rows), `0LC1RD_1LB1RD_1LB0RD` (3 rows)

`residue_map` reads both as `Ip`, "HIGHER".  Same diagnosis as above: no
affine lap at any anchor the scan finds, so nested rather than flat.  Note
`1RB---_1LC1RD_0LB1RD_1LB0RD` — the one row that DID board by certificate —
is the nested route (`NLAP_`) at an `S0` anchor, so the machinery is not far
away.

### `1RB---_1RC1LB_0LB1RD_0RA0RC` — the one row that targets `StA`

**It is a plain binary counter** (John's reading, 2026-07-31): MSB to the
LEFT, one marker `1` to the left of every bit, ordinary carry.  Confirmed by
`tools/counters/carry_anchor.py`: **127 consecutive values** decode at the
anchor

  state `StB`, head symbol `S0`, run-unit `11`, digits `10`/`11`.

**Why every scan in the tree missed it.**  The anchor is read AT THE CARRY:
the head sits on the stop bit — the lowest clear bit — so the counter
*straddles* the head, its high digits to the left and the run of set low
digits to the right, and the head's position inside the word depends on the
value.  Every anchor search here and in `tools/counters` pins the head to a
fixed offset from a tape end (`anchor_scan`, `anchor_snaps_all`,
`anchor_snaps_far_all`, `radix_infer`, and the `HD` scan added this session),
so none of them can see it.  That is a general gap, not a quirk of this row.

In `cconf` terms the anchor is

```coq
Cc p = (StB, (S1 :: Rw q0, S0, rep [S1] (2 * j)))    where cview p = (j, Some q0)
```

— the stop digit's own marker nearest the head on the left, then the higher
digits as `(bit, marker)` pairs reading leftward, then the wall cell `S0` at
cell 0; and on the right the carry run, two cells per set digit.
`Checkers/LapDecider.v` can express exactly this shape (`cden` allows an
opaque tail on one side and a `rep u (a*j+b)` block on the other, and here
`el = false`, `er = true`, `c0 = mkC StB (mkS [S1] [] 0 0 []) S0 (mkS []
[S1] 2 0 [])`).  **What is missing is the anchor search and a template whose
anchor straddles the head, not the checker.**

**Why `StA` fires, and sparsely.**  The interleaved markers mean `StD`'s
`0RA` is only reached when the counter WIDENS — `StA` is on the expand-the-
wall path.  Measured, it is re-entered at configuration indices

```
19, 66, 257, 1024, 4095, 16382, 65533, 262140, 1048571, …
```

(to `t = 2·10^6`; `4095 = 2^12 - 1`, `16382 = 2^14 - 2`, `65533 = 2^16 - 3`,
…), i.e. once per epoch.  So the counter is FIXED-WIDTH within an epoch and
the widening is the outer level — and the row's target is
**`NeverQuasiHaltsSt`, not `iqh`**: it is the one row of the 24 that does not
quasihalt, and `LapGlue.glue_neverqh` is its closer rather than
`LapGlueQuiet.glue_qh_quiet`.

## 4. Reproducing the measurements

```sh
python3 tools/counters/radix_infer.py <rowfile>     # radix, digits, lap law
python3 tools/counters/carry_anchor.py <rowfile>    # anchors that straddle the head
python3 tools/counters/emit_lapcert.py --list <rowfile> [--emit]
```

The emitters are UNTRUSTED, as everything under `tools/` is: a wrong role,
digit triple, boot index or chain fails to typecheck rather than mis-proving,
and the Coq kernel re-runs every checker on every board.
