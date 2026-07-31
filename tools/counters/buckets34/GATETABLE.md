# Gate table over the 42 open core rows

`tailcert.py --list tools/closeout/core_rows.txt --out scan.json` (scan labels,
no --emit), split by `buckets.py`, filtered to live membership after each wave.
Exact partition of `core_rows.txt`.  Regenerate rather than trust: both commands
are untrusted Python and need no Coq.

| n | furthest gate |
|--:|---|
| 23 | `no_interior_jS_j_chain_at_octave_parity_0` |
| 10 | `no_gap_free_two_form_family` |
| 3 | `register_step_does_not_close` |
| 2 | `no_inner_family_at_pow2_j` |
| 2 | `no_inner_interior_chain` |
| 1 | `no_boot_chain` |
| 1 | `no_interior_j0_chain_at_octave_parity_0` |
