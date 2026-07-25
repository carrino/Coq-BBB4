# RepWL big-block — wave-8 residue burn-down (34 boards)

_Written 2026-07-25.  The big-block RepWL track of the wave-8 residue push.
Companion to `docs/MACHINE_NOTES_WAVE8.md` ("the RepWL correction") and
`docs/COUNTER_EMITTER_WAVE8.md` §4b (which had recorded RepWL as a dead
lever).  This doc records the correction end-to-end: the parameter that was
wrong, the sweep, and the 34 boards it landed._

## The finding it exploits

RepWL had been written off on this residue twice, both times a **block-size
parameter artifact**, not a real limit of the abstraction:

- `COUNTER_EMITTER_WAVE8.md` §4b swept the counter core at `(L,T) ∈
  {2,3,4}×{2,3,4}` (i.e. `L ≤ 4`), `t=0`, and got `0/60` — "RepWL over the
  counter core: DEAD."
- `MACHINE_NOTES_WAVE8.md` records the human read that overturned it: the
  earlier sweep **capped block size at `L ≤ 6`**, and a machine whose tape
  period is 10 (`1RB0LB_0RC1RD_1LC0LA_0RA0RB`, run-lengths cycling
  `3,1,2,1,2,1`, tape `1110110110` repeating) is caught **cleanly at `L=10`**
  (490-node closure, every state discharged) while failing to even close at
  `L ≤ 6`.

The DEAD verdict is still correct for genuine binary counters — their digit
pattern differs on every increment, so no finite block set closes — and those
simply are not caught here (the closure or the lex check fails).  What the
`L ≤ 6` cap hid is the **periodic-bouncer** sub-population of the residue,
whose finite tape period `p` is finitized by any RepWL block size that is a
multiple of (or commensurate with) `p`.  Matching `L` to the period recovers
them.

## Method

1. **Sweep** — `tools/counters/repwl_bigblock.py` over
   `tools/counters/wave8_unrecognized.txt` (742 unrecognized residue
   machines).  It runs the untrusted `repwl_prover.py` engine across rungs
   `L ∈ {5..20}`, `T ∈ {2,3}`, `t=0`, closure cap 20 000 nodes, and reports
   `(machine, L, T, t, nseen)` for each machine whose whole-tape closure
   closes AND whose every state discharges under the lex procedure.
   Result: **34 / 742 caught.**
2. **Emit** — `tools/gen_rwl8_certs.py` (a driver over the sweep hits) calls
   `repwl_prover.decide` to recover the full per-state certificate and reuses
   the landed `gen_repwl_certs.emit_machine` to string-emit one
   `theories/Machines/RWL8_<NNNNN>.v` per machine (one machine per file for
   failure isolation on the heavy closures), plus `tools/rwl8_manifest.tsv`.
3. **Verify** — each board is closed ONLY through the already-landed
   `rw_check_neverqh_sound` (`Checkers/RepWL.v`) by `vm_compute; reflexivity`.
   **Zero new soundness surface**; no new checker, no new corruption test.
   The Coq kernel re-derives the closure and re-checks every edge, so a wrong
   untrusted certificate fails to TYPECHECK rather than mis-proving.

## Result — 36 boards, all kernel-verified

Every `RWL8_*.v` file `coqc -native-compiler no -Q theories BBB4` compiles and
`Print Assumptions` is `functional_extensionality_dep` only.  All compile
inside a container window (heaviest: `RWL8_00012`, 12 029-node closure, 160 s).
All catch at `T=2`; `L` ranges 9–30 (the tape period of each machine).

The initial `repwl_bigblock.py` sweep (`L ≤ 20`) landed 34.  A follow-up
wider-parameter probe (`L ≤ 40`, `T ≤ 4`, warmup `t`) over the 708 machines
the first sweep missed caught **2 more** — long-period bouncers that close at
`L=30` (`RWL8_00035` `1RB0LD_1RC0RB_1LA1RA_1LD1LA`, `RWL8_00036`
`1RB1LB_1LC0RD_1LA0LC_1RD1RB`) — and returned **NOCLOSE for the other 706**
with **zero** finitize-but-no-certificate cases.  That last fact is the load-
bearing diagnosis: for the residue RepWL cannot board, the wall is
*finitization itself*, never the measure/rank synthesis — so a richer measure
vocabulary would not help.  The 706 are for other routes (see
`docs/RESIDUE_708_DIAGNOSIS.md`).

| machine | L | T | contexts | file |
|---|---|---|---|---|
| `1RB0RC_0RC0LD_1RD1RA_1LB1LA` | 10 | 2 | 426 | `RWL8_00021.v` |
| `1RB0LC_1RC0RB_1RD1LD_1LA0RD` | 11 | 2 | 455 | `RWL8_00009.v` |
| `1RB0RA_1RC1LC_1LD0RC_1RA0LB` | 11 | 2 | 461 | `RWL8_00016.v` |
| `0RB0RC_1RC0LC_0RD1RA_1LD0LB` | 10 | 2 | 480 | `RWL8_00001.v` |
| `1RB0LB_0RC1RD_1LC0LA_0RA0RB` | 10 | 2 | 490 | `RWL8_00005.v` |
| `1RB1RD_1LC1LD_1LA0LB_1RC0RA` | 10 | 2 | 550 | `RWL8_00033.v` |
| `1RB0RD_0RC1RA_0RD1RB_1LD0LA` | 10 | 2 | 586 | `RWL8_00023.v` |
| `1RB0LC_1LC0RC_1RD1LA_1RA0RA` | 12 | 2 | 618 | `RWL8_00008.v` |
| `1RB0LB_1LC0RD_1LC1LA_1RA1RD` | 12 | 2 | 628 | `RWL8_00006.v` |
| `1RB1LC_1RC0RC_1RD0LA_1LA0RA` | 12 | 2 | 662 | `RWL8_00027.v` |
| `1RB1LA_1LC0RB_1LD1RC_0LC0LA` | 10 | 2 | 673 | `RWL8_00025.v` |
| `1RB0RB_1LC1RA_1LA0LD_0LB0LC` | 10 | 2 | 683 | `RWL8_00020.v` |
| `1RB1LD_1RC0RB_1LA0RC_0LD1LB` | 12 | 2 | 700 | `RWL8_00030.v` |
| `1RB0RA_0LC0LB_0LD1LC_1RD1RA` | 12 | 2 | 706 | `RWL8_00014.v` |
| `1RB1LA_1LC0RD_0LC1RD_1RA0RB` | 12 | 2 | 792 | `RWL8_00026.v` |
| `1RB0LD_1LB1LC_1RD0LA_1RA0RB` | 10 | 2 | 831 | `RWL8_00013.v` |
| `1RB0LC_1RC0RD_1RD0LB_1LD1LA` | 10 | 2 | 849 | `RWL8_00010.v` |
| `1RB0RB_1LC0LD_0RB0LB_1RD0RA` | 12 | 2 | 860 | `RWL8_00017.v` |
| `1RB0RC_1RC1LB_1LD0RA_0LD1RA` | 12 | 2 | 870 | `RWL8_00022.v` |
| `1RB0LD_0RC0RB_1LC1RA_0LA1LA` | 9 | 2 | 971 | `RWL8_00011.v` |
| `0RB1RB_1LC0RA_0LD0LC_1RD1LB` | 9 | 2 | 974 | `RWL8_00003.v` |
| `1RB1RD_1LC1RB_0LC1LA_0RB0RD` | 11 | 2 | 993 | `RWL8_00034.v` |
| `1RB0LB_0RC1RD_0RD1RC_1LD0LA` | 12 | 2 | 1282 | `RWL8_00004.v` |
| `1RB0LC_1LB1LA_1RD0LA_0RD0RB` | 10 | 2 | 1521 | `RWL8_00007.v` |
| `1RB1LD_0RC0LB_1LC1RA_1LA0LA` | 9 | 2 | 1744 | `RWL8_00028.v` |
| `1RB1LD_0RC0RB_1LC1RA_1LA0LD` | 16 | 2 | 1833 | `RWL8_00029.v` |
| `1RB0RA_1LC1RA_0LD0LC_1RD1LB` | 16 | 2 | 1934 | `RWL8_00015.v` |
| `1RB0RB_1LC0RA_1RA0LD_0LB1LC` | 12 | 2 | 2100 | `RWL8_00019.v` |
| `1RB0RB_1LC0RA_1RA0LD_0LB0RD` | 12 | 2 | 2160 | `RWL8_00018.v` |
| `1RB1RD_1LC0RC_0RD1LD_1RA0LB` | 20 | 2 | 2218 | `RWL8_00032.v` |
| `1RB0RD_1LC0LC_1RA1LB_0RA0RB` | 16 | 2 | 2905 | `RWL8_00024.v` |
| `0RB0RC_1RC0RA_1LD0LD_1RB1LC` | 16 | 2 | 2907 | `RWL8_00002.v` |
| `1RB0LD_1RC0RB_1LA1RA_1LD1LA` | 30 | 2 | 3804 | `RWL8_00035.v` |
| `1RB1LB_1LC0RD_1LA0LC_1RD1RB` | 30 | 2 | 3877 | `RWL8_00036.v` |
| `1RB1RC_1LC0RD_0RC0LD_1RA0LA` | 10 | 2 | 9999 | `RWL8_00031.v` |
| `1RB0LD_0RC0RB_1LD1RA_1LC1LA` | 11 | 2 | 12029 | `RWL8_00012.v` |

## Cross-check note (the BBB holdouts, and why it's 0)

The task pointed at `tools/BBB4_holdouts_3713.txt` (machines the BBB project
proved) as a corroboration/dedup oracle — "all but a few have proofs in that
repo."  **Measured: 0 of the 34 hits are in that list — and the entire 742-
machine residue is disjoint from the 3 713 holdouts.**  This is not a format
mismatch (same underscore spec format); the two sets are different populations:
`BBB4_holdouts_3713.txt` is BBB's *solved-holdout* set, whereas
`wave8_unrecognized.txt` is the *census-deferred residue* the wave-8
recognizers (counter fingerprint v2 + irules + nghist) could not place.  So
these 34 boards are novel — RepWL big-block opens ground the holdout oracle
does not cover.  Nothing was skipped as an already-solved duplicate; no BBB
proof was ported.  (No overlap with the 27 kept-holdouts either; the machinery
stayed on the residue.)

## Reproduce

```sh
# environment: apt coq 8.18.0 is sufficient (native off; the boards are
# vm_compute/reflexivity).  census cache stays MATCH (Census untouched).
python3 tools/counters/repwl_bigblock.py \
    tools/counters/wave8_unrecognized.txt /tmp/rwl8_hits.tsv     # -> 34 hits
python3 tools/gen_rwl8_certs.py /tmp/rwl8_hits.tsv               # -> RWL8_*.v
for f in theories/Machines/RWL8_*.v; do
  coqc -native-compiler no -Q theories BBB4 "$f"                 # each compiles
done
# Print Assumptions on any nqh_* theorem == functional_extensionality_dep only
```

## Scope

Big-block RepWL track only.  Did NOT touch the counter emitters,
`theories/Machines/Counters/`, `theories/Counters/ILC*`, `theories/Census/`,
or the census cache (verified `census_cache.py --check` = MATCH before and
after).  New files only: `theories/Machines/RWL8_*.v`,
`tools/gen_rwl8_certs.py`, `tools/rwl8_manifest.tsv`, this doc, and the 34
`_CoqProject` lines listing the boards.
