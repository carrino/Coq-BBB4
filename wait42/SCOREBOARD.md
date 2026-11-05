# BBB_qh_decide(4,2) scoreboard

**Exact values: open.** State-based work is the priority. Both record lower
bounds below are proved in Coq and passed full recursive kernel checking.

| Convention | Extra wait proved ≥ | Total horizon proved ≥ | Witness | Target |
| --- | ---: | ---: | --- | --- |
| State | [225,592,668](theories/WitnessRecord.v) | [258,372,146](theories/WitnessRecord.v) | `1RB1RC_1LA0LA_0RD0RC_1LD1LA` | B |
| Instruction | [454,402,378](theories/Examples.v) | [487,181,856](theories/LowerBounds.v) | `1RB0LD_1RC1RB_1LA1LC_0RC1LA` | D0 |

Both start at the existing BBB cutoff 32,779,478. The uniform waiting guarantee
applies to each choice of one designated beeping state or instruction. These
lower bounds are not sufficient decision cutoffs yet.

## Proof work completed

| Component | Status |
| --- | --- |
| State and instruction definitions, uniqueness, decision rules | Compiled and recursively checked |
| Reflection, state relabeling, nonhalting completion, shifted tails | Compiled and recursively checked |
| Translated-cycle bound P−1 after the cycle anchor | Compiled and recursively checked |
| Finite abstract rank bounds, including the final rank+1 step | Compiled and recursively checked |
| Waiting-specific TNF expansion and residual coverage | Compiled and recursively checked |
| Checked 1,024-update pilot | 53 pending nodes, 338 unresolved nodes; explicitly unfinished |
| Stronger checked pilot replay | 21 pending subtree roots + 29 prior unknown nodes remain; 341 nodes removed |
| Periodic certificate replay | 204 families: 80 stratified samples plus 124 recovered certificates |
| Finite n-gram replay | 10 samples across widths 2, 3, 4, 6, and 8; completion bounds |
| Repeated-word holdout proofs | 1 initial holdout plus 25 from a 1,000-family sample |
| Certificate-based frontier filtering | Soundness proved; rejected nodes remain explicit |
| Universal upper bound at the current record | Not proved |

The cycle and rank bounds work at cutoffs after a short certified anchor. They
avoid simulating 32 million steps for each easy census leaf. Cheap leaf proofs
use a width of 4,096; the census theorem permits unresolved families to be
discharged at any larger proposed width using the same computed walk.

The stronger pilot's 50 remaining obligations are **not** the final holdout
list. Its 21 pending nodes still represent unexplored subtrees. The theorem
[replay_pilot_conditional_coverage](theories/ReplayPilot.v) retains every
completion obligation and makes no unconditional universal bound claim.
[replay_pilot_coverage_at_width](theories/ReplayCoverage.v) permits the remaining
families to be discharged at any larger proposed width without recomputing the
pilot.

## Exploratory burndown

These are **untrusted search results**, not counts of completed Coq proofs.
Each pass traversed 3,995,004 normalized tree nodes, including 3,136,096 full
tables, with no pending frontier or tape-edge failures. Rows represent
partial-table families; they are not weighted counts of all labelled machines.

| Pass | Search configurations | Unresolved families | Runtime |
| --- | --- | ---: | ---: |
| Initial | 130 simulation steps, short finite n-gram ladder | 289,654 | 26.5 s |
| Deeper | 1,030 steps, n-gram widths 2/3/4/6 | 232,523 | 99.2 s |
| Tail ranks | Same depth; require recurrence only for states in the abstract tail | **221,186** | 94.8 s |
| Deeper tail ranks | 4,096 steps; add n-gram width 8 at anchor 1,600 | 214,074 | 413.4 s |
| Preserve both passes | Verify identical family sets, then retain certificates from either pass | **213,950** | 60.0 s to merge |

The last pass also emitted:

- 249,693 halting-completion families;
- 1,029,749 cycle candidates;
- 2,282,976 translated-cycle candidates;
- 211,401 finite n-gram candidates.

**The full census is not yet assembled in Coq.** Individual replays above now
prove waiting bounds for selected families, while the remaining accepted search
leaves still require replay and coverage assembly. Hash-based cycle guesses
are never treated as proofs. A failed replay returns to the backlog. The proof
counts describe different, potentially overlapping samples; they must not be
added to obtain a coverage total.

Increasing the simulation budget missed 124 earlier translated-cycle candidates
because the bounded extractor chooses recent record events. All 124 earlier
certificates passed exact Coq replay and are retained as regressions. The merged
worklist verifies equality of all 3,995,005 ledger family identities before
intersecting unresolved sets. This checks the relationship between two search
outputs, not their mathematical completeness.

The repeated-word experiment selected 1,000 of the original 221,186 residual
families by a deterministic hash. It nominated 25, and all 25 passed recursive
Coq checking; the other 975 remain unproved by that experiment. Their explicit
windows range from 148 to 871 steps, after anchors 0 or 64. The independent
initial holdout has a window of 456. See the
[proof index](research/repeated-word-proved.tsv) and
[experiment summary](research/repeated-word-summary.json).

The historical 5,156 state holdouts are not the new universe. A separate sweep
of 432 historical rare-fire candidates produced the improved state witness;
all 432 had a finite observed state window with a closed control mask, but that
sample supplies neither exhaustive coverage nor kernel census credit.

## Reproduce the worklist

```sh
mkdir -p wait42/build
gcc -O2 -std=c11 -Wall -Wextra -Werror wait42/tools/census_probe.c \
  -o wait42/build/census_probe
wait42/build/census_probe --max-nodes 20000000 --gas 1030 \
  --rungs 2:100,3:200,4:400,6:800 --output wait42/build/census
wait42/build/census_probe --max-nodes 20000000 --gas 4096 \
  --rungs 2:100,3:200,4:400,6:800,8:1600 --output wait42/build/census-deeper
python3 wait42/tools/merge_census_residuals.py \
  --left wait42/build/census.residual.tsv \
  --right wait42/build/census-deeper.residual.tsv \
  --verify-ledgers wait42/build/census.ledger.tsv wait42/build/census-deeper.ledger.tsv \
  --output wait42/build/census-union
```

`census-union.residual.tsv` is the current search worklist, with the machine and
unused-state pointer retained for each family. `census.ledger.tsv` records every
stopped leaf, including accepted candidates awaiting proof replay.
`census.frontier.tsv` preserves any pending nodes if a budget interrupts the walk.
These large generated files stay out of Git. The checked-in
[union summary](research/census-union-summary.json) records counts and source/output
hashes; no search output is trusted by a theorem.

## Next work

1. Replay emitted cycle and rank certificates with the proved checkers and
   preserve every rejection as an explicit obligation.
2. Add repeated-word and counter timing certificates for the residual families.
   Unbounded counter measures need quantitative first-return arguments at the
   fixed cutoff, beyond the finite-rank solver.
3. Apply symmetry and blank-prefix transport with the correct cutoff shifts.
4. Assemble a universal upper bound matching a concrete lower-bound witness.

Validation uses Coq 8.18.0, recursive `coqchk`, and search/replay boundary tests.
The replay target passed for 204 periodic, 10 n-gram, and 25 sampled holdout
families. The strengthened pilot passed a separate full recursive audit in
6m55s. All 48 tool tests pass. [Validation details](research/replay-validation.json)
record the counts and distinguish compilation from independent audits.
The only assumption in the semantic results is the repository's existing
`FunctionalExtensionality.functional_extensionality_dep`. Existing BBB proof
sources are unchanged. The exact four-state waiting values remain open.
