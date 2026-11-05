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
| Universal upper bound at the current record | Not proved |

The cycle and rank bounds work at cutoffs after a short certified anchor. They
avoid simulating 32 million steps for each easy census leaf. Cheap leaf proofs
use a width of 4,096; the census theorem permits unresolved families to be
discharged at any larger proposed width using the same computed walk.

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

The last pass also emitted:

- 249,693 halting-completion families;
- 1,029,749 cycle candidates;
- 2,282,976 translated-cycle candidates;
- 211,401 finite n-gram candidates.

**Census proof credit remains zero:** all accepted search leaves still require
exact Coq replay and coverage assembly. Hash-based cycle guesses in particular
are never treated as proofs. A failed replay must return to the backlog.
The generic solver proofs and individual lower-bound witnesses above are
separate, already-checked results.

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
```

`census.residual.tsv` is the current search worklist, with the machine and
unused-state pointer retained for each family. `census.ledger.tsv` records every
stopped leaf, including accepted candidates awaiting proof replay.
`census.frontier.tsv` preserves any pending nodes if a budget interrupts the walk.
These large generated files stay out of Git. The checked-in
[summary](research/census-tail-summary.json) records counts and source/output
hashes; no search output is trusted by a theorem.

## Next work

1. Replay emitted cycle and rank certificates with the proved checkers and
   preserve every rejection as an explicit obligation.
2. Add repeated-word and counter timing certificates for the residual families.
   Unbounded counter measures need quantitative first-return arguments at the
   fixed cutoff, beyond the finite-rank solver.
3. Apply symmetry and blank-prefix transport with the correct cutoff shifts.
4. Assemble a universal upper bound matching a concrete lower-bound witness.

Validation: all lower-bound and foundation modules compiled under Coq 8.18.0;
full recursive audit and printed reports passed in 8m47s using existing compiled
objects. The bounded pilot also passed a separate recursive audit. The only
assumption in the semantic results is the repository's existing
`FunctionalExtensionality.functional_extensionality_dep`. Sixteen search-tool
tests pass. No existing proof source was changed.
