# Gate table over the 37 open core rows

`tailcert.py --list tools/closeout/core_rows.txt --out scan.json` (scan labels,
no --emit), split by `buckets.py`, filtered to live membership after each wave.
Regenerate rather than trust: both commands are untrusted Python and need no
Coq.

| n | furthest gate |
|--:|---|
| 19 | `no_interior_jS_j_chain_at_octave_parity_0` |
| 10 | `no_gap_free_two_form_family` |
| 2 | `no_inner_interior_chain` |
| 1 | `no_boot_chain` |
| 1 | `no_interior_j0_chain_at_octave_parity_0` |
| 1 | `no_inner_family_at_pow2_j` |
| 1 | `register_step_does_not_close` |
| 2 | *(not gate-scanned — see below)* |

The `.txt` lists partition `core_rows.txt` **except** for two rows:

    0RB0LA_1LA1RC_0RD1RD_1LB0LB
    0RB0LA_1RC1LA_1RD0RD_1LB0LB

Those are 0RB shadows whose core partners boarded in `docs/LADDER_PLAN.md`
§4o, so they became core rows in their own right and were never in a
`tailcert` scan.  They need the re-root transport
(`Census/Reroot.v`, `Census/RerootSwap.v`, `tools/closeout/gen_shadow.py`),
not a family, so a gate label would not say anything useful about them.
Re-running `tailcert` over the current `core_rows.txt` would file them
somewhere; nothing reads that label today.

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
