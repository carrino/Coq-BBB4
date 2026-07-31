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
| `0LB1RC_1LD0RC_1LB1RC` | 3 | 0 | — |
| `0LC1RD_1LB1RC_1LB0RD` | 3 | 0 | — |
| `0LC1RD_1LB1RD_1LB0RD` | 3 | 0 | — |
| `0LB1RC_1LB0RD_1LC0RC` | 2 | 0 | — |
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
the single best-scoring one.

## 2. The boarded four families

All four are `iqh` — `NonHalt /\ QHBound 2000 /\ QuasiHaltsSt` — **not**
`NeverQuasiHaltsSt`: `StA` fires once and never again, so these machines
genuinely quasihalt, with score 1.  `LapGlueQuiet.glue_qh_quiet` is the
closer in every case (`qa = StA`, `s0 = 0`), and its `AvoidRun` premise is
free from `ReachStI.inv_csteps_all` because the three roles are a total,
closed state set that excludes `StA`.

### `Ter3Wall.v` — base three (3 rows)

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

## 3. The 14 survivors, and what each needs

Measured with `tools/counters/radix_infer.py` and by hand-reading traces.

### `0LB1RC_1LB0RD_1LC0RC` (2 rows) — base three, different digits

`1RB---_0LB1RC_1LB0RD_1LC0RC`, `1RB---_1LC0RD_0LC1RB_1LB0RB`.
Base 3, 2-cell digits `{00, 10, 11}`, anchor at the wall, lap `4j + 2` and
`4j + 4` on the two interior branches.  **This is the cheapest survivor
group.**  `TernCounter.v` already supplies numerals, both increments and
`TerStep`; what does not fit is `Ter3Wall`'s lap, because the increment
writes its fresh `1` in the digit's FIRST cell (`00 -> 10`) where `Ter3Wall`
writes it in the second (`00 -> 01`).  So: one more closer of the same size
as `Ter3Wall`, or a `TerStep` widened to carry the stop-digit rewrite as
data.

### `0LB1RC_1LB0RD_1LC0RD` (2 rows), `0LB1RC_1LD0RC_1LB1RC` (3 rows)

`residue_map` reads both as `Dp` (each bit in two identical copies) and calls
them "HIGHER".  Measured directly at the `Dp` wall anchor, the lap really is
super-affine: `6, 16, 36, 82, 196` steps at carry lengths `0..4`.  A lap that
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

`StD`'s `S0` transition is `0RA`, so `StA` is re-entered whenever that fires.
Everything above assumes `StA` fires once; this row needs either a proof that
`0RA` never fires after the bootstrap (then `LapGlueQuiet` applies verbatim,
its `AvoidRun` premise discharged by `LapAvoid` rather than by
`ReachStI.inv_ok`), or a genuinely different argument.  It is also the row
`radix_infer` reads at `p0 = 257` rather than 1, so its bootstrap is long.

## 4. Reproducing the measurements

```sh
python3 tools/counters/radix_infer.py <rowfile>     # radix, digits, lap law
python3 tools/counters/emit_lapcert.py --list <rowfile> [--emit]
```

The emitters are UNTRUSTED, as everything under `tools/` is: a wrong role,
digit triple, boot index or chain fails to typecheck rather than mis-proving,
and the Coq kernel re-runs every checker on every board.
