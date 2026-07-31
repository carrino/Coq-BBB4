# Gate table over the 30 open core rows

`tailcert.py --list tools/closeout/core_rows.txt --out scan.json` (scan labels,
no --emit), split by `buckets.py`, filtered to live membership after each wave.
An exact partition of `core_rows.txt`.  Regenerate rather than trust: both
commands are untrusted Python and need no Coq.

| n | furthest gate |
|--:|---|
| 14 | `no_interior_jS_j_chain_at_octave_parity_0` |
| 10 | `no_gap_free_two_form_family` |
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
