# SBCv1 sweep -- raw results

Produced by `tools/counters/sbcfit.py` (untrusted; no board depends on it).
See `docs/SBCV1_READING.md` for what these say.

| file | what |
|---|---|
| `C_residue.tsv` | all 1016 of `D_remaining`, both orientations |
| `A_boarded.tsv` | 40 machines we have already boarded (positive control population) |
| `B_holdout.tsv` | 40 of mxdys' own (4,2) holdouts |
| `C_sample_why.tsv` | 200 residue machines, evenly sampled, with `why:` failing-rule counts |
| `funnel.py` | the stage-by-stage tabulation |

Line format: `<spec>\tSBCV1\t<fwd|mir>\t<cert>` on a fit, else
`<spec>\tFAIL\tfwd:<stages> mir:<stages>`.  Stages are `rc` (rightward shift
rules found), `lc` (leftward), `part` (surviving the join), `s0` (candidates
whose machine actually reaches a sync-bouncer-counter config), and `why:`
names the first failing hypothesis per near-miss candidate.

Headline: 0 fits anywhere, but 461/1016 residue machines REACH an S0 config
and 96% of the near-misses die on exactly one rule, `RL1`.

Reproduce:

    python3 tools/counters/sbcfit.py --debug --list <machines> -T 200000
    python3 tools/counters/sbcv1_results/funnel.py <dir-of-tsvs>

Controls (both should hold before trusting any of this):

    python3 tools/counters/sbcfit.py --upstream <busycoq>/verify/SBCv1_6x2_solved.v
    # -> checked 416   accepted 416   rejected 0
