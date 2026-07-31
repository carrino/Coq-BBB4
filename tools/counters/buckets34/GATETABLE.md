# Gate table over the 27 open core rows

`tailcert.py --list tools/closeout/core_rows.txt --out scan.json` (scan labels,
no --emit), split by `buckets.py`, filtered to live membership after each wave.
An exact partition of `core_rows.txt`.  Regenerate rather than trust: both
commands are untrusted Python and need no Coq.

| n | furthest gate |
|--:|---|
| 14 | `no_interior_jS_j_chain_at_octave_parity_0` |
| 7 | `no_gap_free_two_form_family` |
| 2 | `no_inner_interior_chain` |
| 1 | `no_boot_chain` |
| 1 | `no_interior_j0_chain_at_octave_parity_0` |
| 1 | `no_inner_family_at_pow2_j` |
| 1 | `register_step_does_not_close` |

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
* **Four are genuinely quadratic on the arm** (`1RB0LD_0LC0RB_1LA1RC_0RC1LD`
  and the three `1RB1LA` rows): a second difference of exactly 2, so no
  threshold or stride in ARM_GRID reaches them.  Closed as ladder rows; do not
  re-probe (`docs/QUAD_TERMINAL_MEASUREMENT.md` corroborates independently).
* **Three have never been arm-probed** — `1RB1LC_1LB1RA_0LC0LD_0RA0RD`,
  `1RB1LC_1LC1RA_0LC0LD_0RA0RD`, `1RB1RC_1LA0LB_1LD0RD_1LB0RC`.

A gate name says what stopped the emitter, not what stops a proof.  Twice now
this bucket has paid out for someone checking the measurement instead of the
label.  Check it before reading a bucket as a difficulty class.

**Wave 4s measured the seven fibonacci rows, and the reason nobody had is
that the searcher never built the family.**  `find_families`' numeration pass
runs only `if not found`, and six of the seven return 26-odd positional
families at chain 8 -- `min_chain`, the floor -- which switches it off.  Under
`valfam.py --numeration` six read as fibonacci at chains 232..376, and the
seventh (`1RB0RB_0LC1RD_1LC1LA_0LA1RB`) has no family at any anchor and
belongs in the `no anchor` population, not here.  The six are **Zeckendorf**
(weights 1,2,3,5,8) and `LadderCheck` 11 states 1,1,2,3,5,8, so they are
still open -- but their gate is now the FILL arm at the top of a width, not
"no interior chain".  See `docs/LADDER_PLAN.md` §4s.

## What wave 4s took out

`no_gap_free_two_form_family` lost three rows and **not one of them needed
the gate answered**: the champion `1RB1LD_1RC1RB_1LC1LA_0RC0RD` (a board that
had compiled since wave 33, held out by an arithmetic comparison in
`inventory.py`) and the two gray rows `1RB0RD_1LC0LB_1LD0LB_1RD0RA` and
`1RB0RD_1LC0LC_1LD0LB_1RD0RA` (which closed once the searcher preferred, among
readings tied on chain length, one whose digit words do not all end in a
blank).  Third wave running in which this table's biggest labels described
the tooling.
