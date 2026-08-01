# Gate table over the 9 open core rows

`tailcert.py --list tools/closeout/core_rows.txt --out scan.json` (scan labels,
no --emit), split by `buckets.py`, filtered to live membership after each wave.
An exact partition of `core_rows.txt`.  Regenerate rather than trust: both
commands are untrusted Python and need no Coq.

| n | furthest gate |
|--:|---|
| 4 | `no_interior_jS_j_chain_at_octave_parity_0` |
| 2 | `no_inner_interior_chain` |
| 1 | `no_gap_free_two_form_family` |
| 1 | `no_interior_j0_chain_at_octave_parity_0` |
| 1 | `no_inner_family_at_pow2_j` |

`register_step_does_not_close` and `no_boot_chain` are both EMPTY.

**At nine rows this table has stopped being useful, and that is the finding.**
Every bucket it ever called large has emptied without the gate being answered,
so what follows is kept as the record of how a gate label fails rather than as
a difficulty map.  For choosing a target, read the per-row notes in
`docs/RESIDUE_MAP.md`.

## What is actually left in the biggest bucket

`no_interior_jS_j_chain_at_octave_parity_0` is 4 rows:

* **THREE are the BASE-3 block** — `1RB1LC_1LB1RA_0LC0LD_0RA0RD`,
  `1RB1LC_1LC1RA_0LC0LD_0RA0RD` (which differ in exactly one transition) and
  `1RB1RC_1LA0LB_1LD0RD_1LB0RC`.  All three read `EXP3`/`EXP3`; two carry a
  shadow, so they are 5 of the 14 rows left.  **The third is reconnoitred and
  build-ready** — `tools/counters/ter3_probe.py` located its anchor and
  measured 75,006 consecutive visits with 0 failures and an affine lap in two
  branches (`6c+4`, `6c+6`).  Its alphabet is `Ter3WallB`'s digit for digit
  and its branches are `TernCounter`'s `tsucc`/`tsuccT`; only the closer is
  new (`LapGlue.glue_neverqh`, since `StA` is a transition target here).  The
  other two have not been probed.
* **ONE is a `no anchor` row wearing this label** —
  `1RB0RB_0LC1RD_1LC1LA_0LA1RB` finds no family at any anchor
  (`digit_words(rules)` names nothing).  It once counted with the fibonacci
  rows; it was never one of them.

## What this table has been wrong about, four times

A gate name says what stopped the emitter, never what stops a proof.  This
file has asserted four verdicts that later measurement overturned.  The shape
of the mistake is the same every time and is worth more than any label in it:

1. **"The four QUADRATIC rows are not coming back without a new arm shape."**
   The arm measurement was right and was made three times — 4p on the arm,
   `docs/QUAD_TERMINAL_MEASUREMENT.md` independently, §4t a third time.  **All
   four boarded anyway, none with a new arm shape**: #115 took three as
   `Counters/LinC_*`, #116 the last as `Counters/BinCarry_*`.  The verdict
   bounded the LADDER and never the machines.  **Never read "closed as a ladder
   row" as "closed."**

2. **"The fibonacci rows have no anchor."**  Four waves searched for one.
   `radix_clock.py` reads `ratio = 1.6180` at spread 0.00 and the toggle counts
   satisfy `F(n) = F(n−1) + F(n−2)` exactly.  The anchor was always fine; the
   RADIX was wrong.

3. **"The six are Zeckendorf, weights 1,2,3,5,8."**  4s inferred that from a
   fit that had DROPPED A COLUMN — the counter's lowest digit is a constant 1,
   so `fit_weights` has a zero coefficient in a column that never varies and
   abandons the fit.  `1,2,3,5,8,13` is `1,1,2,3,5,8` with the bottom rung
   missing: the numeration the kernel already had.  Building `(Fib, 2)` would
   have produced a `fam_lim`, a weight ladder and a round trip that all exist.

4. **"Whether the new code reaches the remaining rows is unmeasured — that is
   an emitter run."**  It was measured, twice (§4s, §4v), and neither answer
   was "it reaches them" nor "the emitter refuses".

**All of them boarded.**  #118 took the six at `(FibL, 1)` — a fourth CODE, not
a second numeration: `fibdec`/`fibokb` pick the greedy representative and these
six stood on the LAZY one, so `LadderFam` gained `FibL` with the decoder
`fiblaz` (`fibdec`'s two-state automaton with the transitions swapped), plus
`fam_lo`, because what a weighted numeration really costs the interface is a
FLOOR — width `k` spells exactly `[fibw k .. fibsum k]`.

## `no_gap_free_two_form_family`: 10 -> 1, and the gate was never answered

Nine rows left this bucket in four waves and not one needed the gate answered:

* **4s took three.**  The champion `1RB1LD_1RC1RB_1LC1LA_0RC0RD` had a board
  that compiled since wave 33 and was held out by an arithmetic comparison in
  `inventory.py`.  The two gray rows closed once the searcher preferred, among
  readings tied on chain length, one whose digit words do not all end in a
  blank — a `cconf` carries no trailing blanks, so the other reading's boot
  check could never pass.
* **#114 took four** — the remaining `0RB` rows, all four bouncer counters.
* **#115 took one** (a doubling nested bouncer).
* **#116 took one** (a two-block bouncer, hand-boarded off
  `WTape.cycR`/`cycL`/`cycLW`) and its shadow.

## A shape worth remembering

Wave 4o briefly put two rows in `core_rows.txt` that were in none of these
lists — the 0RB shadows its four boards promoted.  A promoted shadow needs the
re-root transport, not a family, so it will never have a useful gate label.
Since #105 that case is handled without anyone noticing: `make closeout` runs
`gen_shadow.py --harvest`, which boards a freed shadow in the same regen as its
partner.  It first fired in anger in wave 4u, and every quadratic row's shadow
came that way.
