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
| Quantitative directional sweeps | 745 current residual families; width B+2 at every B≥6 |
| Growing counter with three active states | 1 distinct current residual family; width B+1 at every B≥2 |
| Sweeps through either symbol | 473 more families; conditional width B+2 at every B≥6 |
| Checked count-and-control certificates | 2,874 more families; width 98,338,439 at cutoff 32,779,478 |
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
| Replay sweep and counter proofs | Remove 745 checked sweeps and one checked three-state counter | **213,204** | See timing validation below |
| Generalized sweeps and count/control ranks | Remove 473 + 2,874 disjoint checked families | **209,857** | 44.7 s for counter discovery; every result replayed |

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

The first timing batch checks **746 distinct families in the merged 213,950-row
worklist**. Every completion of the 745 entries in
[SweepResiduals.v](theories/SweepResiduals.v) has state waiting width B+2 for B≥6.
The proof uses finite tape support to bound scans; it allows expanding runs
whose return gaps are unbounded over time. A separate three-state counter,
`0RB---_0LC0RB_1LD1RD_1RB0LD`, has width B+1 for B≥2, proved by a descending
nonblank-count-plus-control rank inside a closed invariant.

At the BBB cutoff these widths are **32,779,480** and **32,779,479**. Both fit
under the current state waiting record. Subtracting exactly these distinct
identities leaves **213,204** research holdouts. Earlier samples are not
subtracted again, and this count still is not formal universal census coverage.
The [sweep index](research/sweep-proved.tsv) and
[timing validation](research/timing-validation.json) record the source and proof
identities. These initial 746 families remain included in `proof-timing`.

The next timing batch closes **3,347 more distinct worklist families**. It adds
473 mixed-symbol sweep families and 2,874 count-and-control certificates, with
no overlap between those sets or the preceding 746 removals. The generalized
sweep proof is conditional on a future visit, covering scans through blank
zeros without assuming that every such scan must return.

The counter checker verifies every edge inequality inside a closed control
invariant. Its measures count all ones, or the head plus one half-tape, with a
state-dependent offset. These measures can grow without a fixed global maximum;
their value at the cutoff supplies the numerical waiting bound. The aggregate
[Tight.all_completions](theories/ControlRankReplay/Tight.v) proves width
**98,338,439** for every indexed completion. The sweep batch has width
**32,779,480** at the same cutoff.

The combined [proof index](research/proved-residuals.tsv) contains **4,093**
unique identities from the 213,950-row merged snapshot. Exact subtraction leaves
**209,857**, with zero pending research nodes. All new certificate batches and
their generic soundness theorems passed recursive kernel checking; the remaining
full-census assembly obligation is unchanged. See [round-three validation](research/round3-validation.json).

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
make -C wait42 proof-timing -j2
python3 wait42/tools/reduce_residuals.py \
  --input wait42/build/census-union.residual.tsv \
  --source-sha256 8e4302e6c6683cd7280ad3634b42ffa1cd8064049a47fa82cbfc12c55f87ab9a \
  --proof-index wait42/research/proved-residuals.tsv \
  --output wait42/build/census-union-remaining.residual.tsv
```

`census-union-remaining.residual.tsv` is the current search worklist, with the machine and
unused-state pointer retained for each family. `census.ledger.tsv` records every
stopped leaf, including accepted candidates awaiting proof replay.
`census.frontier.tsv` preserves any pending nodes if a budget interrupts the walk.
These large generated files stay out of Git. The checked-in
[union summary](research/census-union-summary.json) records counts and source/output
hashes; no search output is trusted by a theorem.

The reducer hashes and parses one immutable snapshot, matches both the machine
and pointer, rejects malformed or missing identities, and preserves pending
subtrees. It does bookkeeping only; the preceding proof target checks the
indexed statements. Overlapping proof indexes remove a family only once.

## Next work

1. Replay emitted cycle and rank certificates with the proved checkers and
   preserve every rejection as an explicit obligation.
2. Add repeated-word and counter timing certificates for the residual families.
   The count/control checker now settles 2,874 additional families. A graph
   diagnostic found 5,832 further candidates with at most two directional
   scanning phases per target. They remain **unproved and on the worklist**;
   the next task is a quantitative theorem for composing those phases.
3. Apply symmetry and blank-prefix transport with the correct cutoff shifts.
4. Assemble a universal upper bound matching a concrete lower-bound witness.

Validation uses Coq 8.18.0, recursive `coqchk`, and search/replay boundary tests.
The replay target passed for 204 periodic, 10 n-gram, and 25 sampled holdout
families. The strengthened pilot passed a separate full recursive audit in
6m55s. The expanded timing target passed for all 4,093 indexed families,
including the narrower counter bound. All 74 tool tests pass.
[Replay validation](research/replay-validation.json) and
[timing validation](research/round3-validation.json) distinguish compilation
from independent recursive audits.
The only assumption in the semantic results is the repository's existing
`FunctionalExtensionality.functional_extensionality_dep`. Existing BBB proof
sources are unchanged. The exact four-state waiting values remain open.
