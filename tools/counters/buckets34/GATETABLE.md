# Gate table over the 65 open core rows -- scan at 66ad4c2, filtered to e955ed8 membership

`tailcert.py --list tools/closeout/core_rows.txt --out scan.json` (scan labels,
no --emit), split by `buckets.py`, then filtered to the rows still open after
PR #83's 3 boards (all from no_inner_interior_chain).  Exact partition of
core_rows.txt.  Regenerate rather than trust: untrusted Python, no Coq needed.

| n | furthest gate |
|--:|---|
| 40 | `no_interior_jS_j_chain_at_octave_parity_0` |
| 10 | `no_gap_free_two_form_family` |
| 5 | `register_step_does_not_close` |
| 4 | `no_interior_j0_chain_at_octave_parity_0` |
| 2 | `no_inner_family_at_pow2_j` |
| 2 | `no_inner_interior_chain` |
| 1 | `no_boot_chain` |
| 1 | `no_visit_witness_for_state_A_at_octave_parity_0` |
