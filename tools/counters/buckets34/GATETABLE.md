# Gate table over the 35 open core rows

`tailcert.py --list tools/closeout/core_rows.txt --out scan.json` (scan labels,
no --emit), split by `buckets.py`, filtered to live membership after each wave.
An exact partition of `core_rows.txt`.  Regenerate rather than trust: both
commands are untrusted Python and need no Coq.

| n | furthest gate |
|--:|---|
| 19 | `no_interior_jS_j_chain_at_octave_parity_0` |
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
family, so it will never have a useful gate label.

## What the biggest bucket is really made of

`no_interior_jS_j_chain_at_octave_parity_0` is 19 rows, and wave 4p
(`docs/LADDER_PLAN.md`) measured that it is not one population:

* **Twelve are the FIBONACCI counters** (`docs/CORE_3STATE.md` §3) — radix φ,
  arms measured affine on the five with partial ladder boards, blocked on the
  numeration rather than on a chain.
* **Four are genuinely quadratic on the arm** (`1RB0LD_0LC0RB_1LA1RC_0RC1LD`
  and the three `1RB1LA` rows): a second difference of exactly 2, so no
  threshold or stride in ARM_GRID reaches them.
* The remaining three have not been arm-probed.

A gate name says what stopped the emitter, not what stops a proof.  Check the
measurement before reading a bucket as a difficulty class.
