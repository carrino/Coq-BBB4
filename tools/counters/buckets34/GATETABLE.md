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

`register_step_does_not_close` and `no_boot_chain` are both EMPTY.

`register_step_does_not_close`'s last row, `1RB1LA_0LA1RC_0RD0RB_1RA---`,
boarded in wave 4u together with its shadow -- and the verdict on it had been
STALE, not negative: it closes at the defaults in 60 s, and the sweep that
said otherwise differed in its arm set, not in its mathematics.
`no_boot_chain`'s last row, `1RB0RD_1LC1RA_0RB0LC_1LD0LA`, boarded in #115 by
widening into its own padding.

Wave 4o briefly put two rows in `core_rows.txt` that are in none of these
lists — `0RB0LA_1LA1RC_0RD1RD_1LB0LB` and `0RB0LA_1RC1LA_1RD0RD_1LB0LB`, the
0RB shadows its four boards promoted.  They boarded the same day
(`Machines/Counters/SH_*.v`), so the partition is exact again.  Worth
remembering as a shape: a promoted shadow needs the re-root transport, not a
family, so it will never have a useful gate label.  Since wave 4s that case is
handled without anyone noticing — `make closeout` runs
`gen_shadow.py --harvest`, which boards a freed shadow in the same regen.

## What the biggest bucket is really made of

`no_interior_jS_j_chain_at_octave_parity_0` is 14 rows, and it has never been
one population.  Wave 4p measured the split; wave 4r acted on half of it:

* **Seven are the FIBONACCI counters** (`docs/CORE_3STATE.md` §3) — radix φ,
  and the label came from measuring their lap on a base-2 clock.  This bucket
  held twelve until wave 4r built `(Fib, 1)` in the kernel and boarded the
  five that had partial ladder boards on disk.  **The remaining seven have
  never been through `emit_ladder` at all** — no board for them exists, partial
  or otherwise — so whether the new code reaches them is unmeasured.  That is
  an emitter run, not a kernel build.
* **The four QUADRATIC rows are GONE — all of them.**  Their arm really is
  quadratic (a second difference of exactly 2, corroborated independently by
  `docs/QUAD_TERMINAL_MEASUREMENT.md` and re-measured a third time in §4t), so
  no widening of ARM_GRID reaches them and that verdict stands **about the
  ladder**.  It never bounded the machines: #115 boarded three as
  `Counters/LinC_*` and #116 boarded the last as
  `Counters/BinCarry_1RB1LA_0LA0LC_1LC1RD_0RB0RD` off John's carry reading,
  with its two shadows.  Four for four, by routes that never build an arm.
* **Three have never been arm-probed** — `1RB1LC_1LB1RA_0LC0LD_0RA0RD`,
  `1RB1LC_1LC1RA_0LC0LD_0RA0RD`, `1RB1RC_1LA0LB_1LD0RD_1LB0RC`.

A gate name says what stopped the emitter, not what stops a proof.  This
bucket has now paid out repeatedly for someone checking the measurement
instead of the label -- most sharply in #115, which boarded three of the four
QUADRATIC rows that this file had called "not coming back without a new arm
shape".  That verdict was right about the LADDER and wrong about the machines:
`Machines/Counters/LinC_*` never builds an arm.  Check the measurement before
reading a bucket as a difficulty class, and never read "closed as a ladder
row" as "closed".

**Wave 4s measured the seven fibonacci rows, and the reason nobody had is
that the searcher never built the family.**  `find_families`' numeration pass
runs only `if not found`, and six of the seven return 26-odd positional
families at chain 8 -- `min_chain`, the floor -- which switches it off.  Under
`valfam.py --numeration` six read as fibonacci, and the seventh
(`1RB0RB_0LC1RD_1LC1LA_0LA1RB`) has no family at any anchor and belongs in the
`no anchor` population, not here.

**4s then read the six as ZECKENDORF, weights 1,2,3,5,8, and wave 4v measured
that it is wrong.**  The fit that produced those weights had dropped a column:
the counter's lowest digit is a constant 1, so `fit_weights` has a zero
coefficient in a column that never varies and abandons the fit rather than
completing it.  `1,2,3,5,8,13` is `1,1,2,3,5,8` with the bottom rung missing --
so it is the SAME numeration `LadderCheck` 11 already states, and **nothing in
the numeration needs building**.  What differs is the REPRESENTATIVE: `fibw 0
= fibw 1 = 1`, so a value does not determine a string, `fibdec`/`fibokb` pick
the greedy member, and these six stand on the LAZY one (LSB-first, top digit
1, no two ZEROS adjacent) on all 23,614 measured values.  The five rows 4r
boarded fail that same check, which is the control.  The real gap is that the
run unit is a two-cell WORD where `Class.cs_t` and `Fill.f_mid` are single
digits -- the same missing shape as 2b3's alternating sweep in `LapDecider`.
See `docs/LADDER_PLAN.md` §4v; do not re-derive the Zeckendorf reading.

## `no_gap_free_two_form_family`: 10 -> 2, and the gate was never answered

Eight rows left this bucket in three waves and not one of them needed the gate
answered:

* **4s took three.**  The champion `1RB1LD_1RC1RB_1LC1LA_0RC0RD` had a board
  that compiled since wave 33 and was held out by an arithmetic comparison in
  `inventory.py`.  The two gray rows `1RB0RD_1LC0LB_1LD0LB_1RD0RA` and
  `1RB0RD_1LC0LC_1LD0LB_1RD0RA` closed once the searcher preferred, among
  readings tied on chain length, one whose digit words do not all end in a
  blank -- a `cconf` carries no trailing blanks, so the other reading's boot
  check could never pass.
* **#114 took four** -- the remaining `0RB` rows, all four bouncer counters.
* **#115 took one** (`1RB0RB_1LC1LD_0LC1RA_0LD0RA`, a doubling nested bouncer),
  and in the same wave took `no_boot_chain`'s last row and three of the four
  QUADRATIC rows next door.

That is now five consecutive waves in which this table's biggest labels
described the tooling rather than the machines.
