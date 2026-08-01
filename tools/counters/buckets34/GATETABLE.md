# Gate table over the 15 open core rows

`tailcert.py --list tools/closeout/core_rows.txt --out scan.json` (scan labels,
no --emit), split by `buckets.py`, filtered to live membership after each wave.
An exact partition of `core_rows.txt`.  Regenerate rather than trust: both
commands are untrusted Python and need no Coq.

| n | furthest gate |
|--:|---|
| 10 | `no_interior_jS_j_chain_at_octave_parity_0` |
| 2 | `no_inner_interior_chain` |
| 1 | `no_gap_free_two_form_family` |
| 1 | `no_interior_j0_chain_at_octave_parity_0` |
| 1 | `no_inner_family_at_pow2_j` |

`register_step_does_not_close` and `no_boot_chain` are both EMPTY.  The first
lost `1RB1LA_0LA1RC_0RD0RB_1RA---` in wave 4u (together with its shadow), the
second lost `1RB0RD_1LC1RA_0RB0LC_1LD0LA` in #115, which widens into its own
padding.

## What the biggest bucket is really made of

`no_interior_jS_j_chain_at_octave_parity_0` is 10 rows and has never been one
population:

* **SIX are one sub-machine** — the `1RB---` fibonacci rows.  At their own
  anchors all six produce the identical value-to-string table, so **one
  instance boards all six**, and none of them carries a shadow.  They count in
  the kernel's own `fibw = 1,1,2,3,5,8`; `fam_lim`, `fam_top`, `fibval` and the
  round trip are all already stated by `LadderFam`.  What differs is the
  REPRESENTATIVE: `fibw 0 = fibw 1 = 1`, so a value does not determine a
  string, `fibdec`/`fibokb` pick the greedy member, and these six stand on the
  LAZY one — LSB-first, top digit 1, **no two ZEROS adjacent** — on all 23,614
  measured values.  4r's five boarded rows are the exact complement of that
  check, which is the control.

  **What blocks them is `Class`, not `Code`.**  The increment sends
  `1^(2m) 0 rest -> (1 0)^m 1 rest`, and `cs_t : nat` is a run of ONE REPEATED
  DIGIT.  No regrouping rescues it: a 2-cell digit at index `j` has values
  `0, fibw (2j+1), fibw (2j), fibw (2j+2)`, not multiples of a common weight.
  The widening is `Class.cs_t, cs_t' : nat -> list nat` and
  `Fill.f_mid : nat -> list nat` — a change to the generic half, which the arm
  side already speaks.  `docs/LADDER_PLAN.md` §4v; oracle
  `tools/ladder/fiblazy.py`.

* **ONE is a `no anchor` row wearing this label** —
  `1RB0RB_0LC1RD_1LC1LA_0LA1RB` finds no family at any anchor
  (`digit_words(rules)` names nothing).  Do not count it with the six.

* **THREE have never been arm-probed at all** —
  `1RB1LC_1LB1RA_0LC0LD_0RA0RD`, `1RB1LC_1LC1RA_0LC0LD_0RA0RD`,
  `1RB1RC_1LA0LB_1LD0RD_1LB0RC`.  Two of them carry a shadow.

## What this table has been wrong about, three times

A gate name says what stopped the emitter, never what stops a proof.  This
file has asserted three verdicts that later measurement overturned, and they
are kept here because the shape of the mistake repeats:

1. **"The four QUADRATIC rows are not coming back without a new arm shape."**
   The arm measurement was right and was made three times — 4p on the arm,
   `docs/QUAD_TERMINAL_MEASUREMENT.md` independently, §4t a third time — and no
   widening of `ARM_GRID` reaches a quadratic.  **All four boarded anyway, none
   with a new arm shape**: #115 took three as `Counters/LinC_*` and #116 the
   last as `Counters/BinCarry_*`, off John's carry reading, with its two
   shadows.  The verdict bounded the LADDER and never the machines.  **Never
   read "closed as a ladder row" as "closed."**

2. **"The six fibonacci rows are Zeckendorf (weights 1,2,3,5,8)."**  4s
   inferred that from a weight fit; 4v measured that the fit had DROPPED A
   COLUMN — the counter's lowest digit is a constant 1, so `fit_weights` has a
   zero coefficient in a column that never varies and abandons the fit rather
   than completing it.  `1,2,3,5,8,13` is `1,1,2,3,5,8` with the bottom rung
   missing, i.e. the numeration the kernel already has.  Building `(Fib, 2)`
   would have produced a `fam_lim`, a weight ladder and a round trip that all
   exist, and still not spelled these machines' strings.  **Do not re-derive
   the Zeckendorf reading**, and do not re-run the weight search: `fibread.py`
   did it exhaustively — 840 fits over all six rows, every anchor, both digit
   widths, every prefix, terminator and permutation, zero at `1,1,2,3,5,8`.

3. **"Whether the new code reaches the remaining rows is unmeasured — that is
   an emitter run."**  It was measured, twice over (§4s, §4v), and the answer
   was neither "it reaches them" nor "the emitter refuses": the anchor and the
   ladder were never the question at all.

## `no_gap_free_two_form_family`: 10 -> 1, and the gate was never answered

Nine rows left this bucket in four waves and not one needed the gate answered:

* **4s took three.**  The champion `1RB1LD_1RC1RB_1LC1LA_0RC0RD` had a board
  that compiled since wave 33 and was held out by an arithmetic comparison in
  `inventory.py`.  The two gray rows `1RB0RD_1LC0LB_1LD0LB_1RD0RA` and
  `1RB0RD_1LC0LC_1LD0LB_1RD0RA` closed once the searcher preferred, among
  readings tied on chain length, one whose digit words do not all end in a
  blank — a `cconf` carries no trailing blanks, so the other reading's boot
  check could never pass.
* **#114 took four** — the remaining `0RB` rows, all four bouncer counters.
* **#115 took one** (`1RB0RB_1LC1LD_0LC1RA_0LD0RA`, a doubling nested bouncer).
* **#116 took one** (`1RB1LB_1LC0RD_0LB1LA_0LA1RA`, a two-block bouncer hand-
  boarded off `WTape.cycR`/`cycL`/`cycLW`) and its shadow.

That is seven consecutive waves in which this table's biggest labels described
the tooling rather than the machines.

## A shape worth remembering

Wave 4o briefly put two rows in `core_rows.txt` that were in none of these
lists — `0RB0LA_1LA1RC_0RD1RD_1LB0LB` and `0RB0LA_1RC1LA_1RD0RD_1LB0LB`, the
0RB shadows its four boards promoted.  A promoted shadow needs the re-root
transport, not a family, so it will never have a useful gate label.  Since
#105 that case is handled without anyone noticing: `make closeout` runs
`gen_shadow.py --harvest`, which boards a freed shadow in the same regen as
its partner.  It first fired in anger in wave 4u.
