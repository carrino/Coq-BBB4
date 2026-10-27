# Four-symbol checker sweeps and proof closeout

The four-symbol development now has checked n-gram, finite-end n-gram,
history n-gram, repeated-word, and affine recurrence checkers. Each accepts
binary score bounds, so a small recurrent-suffix proof can establish a bound
far larger than the executable prefix. The finite/history wrappers also offer
a state-only mode; the recorded closure sweep uses both-bound checkers.

This is still a staged investigation. A failure at one width, anchor, or fuel
budget is not evidence of a difficult machine. The complete BBB(4)-style
escalation ladder has not yet been run on this inventory.
The [second wave](WAVE2.md) continues this playbook with finite/history checks,
stronger repeated-word search, larger kernel replay, and checked shadow closeout.

## First complete core sweep

All **273,969** nonblank-start symmetry representatives received the following
cheap ladder, with anchor 128 and both proposed bounds 4,096:

| Stage | Families examined | Additional candidates | Remaining |
| --- | ---: | ---: | ---: |
| N-gram, width 2, fuel 100, rounds 4 | 273,969 | 57,241 | 216,728 |
| N-gram, width 3, fuel 200, rounds 4 | 216,728 | 22,474 | 194,254 |
| Repeated-word, length 2, threshold 2, fuel 128 | 194,254 | 14,077 | **180,177** |

The sweep found **93,792 candidate families** in 684,951 checker calls, with no
timeouts or stack failures. Summed row time was about 13.2 minutes here.
[`research/pipeline-low-budget.json`](research/pipeline-low-budget.json) pins
the complete input, checker sources, executable, parameters, and output hashes.
Full candidate and remaining-family lists live in ignored
`four/build/pipeline/low-budget/` and are reproducible with the commands below.

These are **extracted-checker search results**, not 93,792 kernel-checked
discharges. The [second wave](WAVE2.md) applies finite/history n-grams and a
stronger repeated-word budget to those 180,177 survivors; broader escalation
and affine search remain. These numbers concern core family representatives,
not raw machine tables or the census's structural pending weight.

## Checked pilot and census integration

The deterministic pilot selects the 128 smallest SHA-256 machine hashes from
the 273,969 nonblank-start symmetry representatives. Its stages use anchor 128
and both bounds 4,096:

| Stage | Parameters | Additional accepted families |
| --- | --- | ---: |
| N-gram | width 2, fuel 100, rounds 4 | 26 |
| N-gram | width 3, fuel 200, rounds 4 | 9 |
| Repeated-word | block length 2, threshold 2, fuel 512 | 41 |
| Total | 128 families attempted | **76** |

All 76 acceptances are replayed by `PipelineExamples.pipeline_rows_checked`.
`pipeline_families_discharged` proves that each family and **all its
completions** were in the original pending set, satisfy both bounds, and are
excluded from `bootstrap_pipeline_pending`. This residual also excludes the
four original affine families through `AffineCloseout`. Those **80 distinct
family records** are linked to exhaustive coverage; they are not 80 removed
eight-step leaves, nor a newly computed raw-table count.

`bootstrap_pipeline_coverage` is the current combined coverage theorem:
every table satisfies both champion bounds or belongs to the refined residual.
The original bootstrap DAG and its structural counts remain unchanged.
The other 52 pilot rows are budget-limited failures. The pilot is a sample of
families, not a population estimate for raw machine tables.

Inputs and evidence:

- [`research/pipeline-pilot.json`](research/pipeline-pilot.json): search
  parameters, source/input hashes, and outcomes.
- [`research/pipeline-examples.json`](research/pipeline-examples.json): compact
  tables and checker parameters for every pilot success.
- [`theories/PipelineExamples.v`](theories/PipelineExamples.v): generated
  kernel replay, completion bounds, pending membership, and coverage.

## Full affine sample replay

Every one of the original 786 affine search candidates was replayed at concrete
fuel 4,096 and symbolic fuel 8,192. Coq accepts **628** and checks that the other
**158** return false at this budget. The accepted theorems prove non-halting and
both bounds at 4,096 for every completion. No upstream quasihalting flag or exact
score is trusted. Compilation and recursive audit took about six minutes here.

The closure pilot independently proves seven of the rejected affine cases and
two families for which affine search found no certificate. Accounting for 67
overlaps, the fixed 1,024-family sample has **637 distinct checked families**,
of which **80** have census links. The original four census links are retained;
the other 624 new affine proofs do not acquire links from replay alone.

The compact certificate bundle, outcome ledger, and audit metadata are
[`affine-batch-certs.json`](research/affine-batch-certs.json),
[`affine-batch.tsv`](research/affine-batch.tsv), and
[`affine-batch-summary.json`](research/affine-batch-summary.json).
The [combined progress ledger](research/progress-sample.tsv) retains each
method's outcome as well as the current proof and census status. A source-hashed
evidence registry prevents a changed certificate or search verdict from gaining
checked status through bookkeeping.

## Symmetry and shadow transport

`Symmetry.v` proves that all six permutations of symbols 1, 2, and 3 preserve
both exact scores, with blank 0 and start state A fixed. It also transports
partial-table completion bounds. `Shadow.v` checks a blank-writing first step
to B, a state swap, a symbol permutation, optional reflection, and inclusion
of a proved core table. A core bound `B` gives shadow bound **`B+1`**.

The regression includes one actual inventory link and its conditional
transport theorem. These generic bridges do not yet certify all 10,572 shadow
links or the entire symmetry quotient. The measured grouping remains separate
from exhaustive census coverage.

## Reproduction

From the repository root, with the Coq toolchain active:

```bash
make -C four check -j2
python3 four/tools/generate_pipeline_examples.py --check
```

That builds and recursively audits all new checker soundness theorems,
four-symbol regressions, symmetry/shadow transports, and the 76-family pilot.
No external search binary or ignored survey files are needed for these proofs.
The proofs use only the preexisting functional extensionality axiom; the
generic closeout machinery is axiom-free.

The larger affine replay is separate from the default build:

```bash
make -C four check-affine-batch
python3 four/tools/progress.py --check
```

It reconstructs the 786 frozen search certificates, generates bounded proof
shards under ignored `four/build/affine-batch/`, checks their recorded outcomes,
and recursively audits them. A rejected certificate proves only that this
particular checker invocation returned false. The compact input bundle and
outcome ledger are tracked; generated proof shards are not committed.

To regenerate the grouped search inventory, first follow
[`GROUPING.md`](GROUPING.md). Then run the extracted checker search:

```bash
# Deterministic 128-family pilot, with the stronger repeated-word stage:
python3 four/tools/pipeline_sweep.py --build \
  --output-dir four/build/pipeline/local-pilot \
  --report four/build/pipeline/local-pilot/report.json

# Complete core inventory, using cheaper repeated-word fuel:
python3 four/tools/pipeline_sweep.py --sample 0 \
  --stages four/research/pipeline-stages.json \
  --output-dir four/build/pipeline/local-low-budget \
  --report four/build/pipeline/local-low-budget/report.json
```

The sweep resumes unfinished stage logs, validates inventory/result uniqueness,
and refuses to mix inputs, parameters, sources, or binaries across runs. Each
row has a 0.25-second stage timeout. Add `--check` to validate completed local
logs without repeating the search. Timings and binary hashes can differ across
toolchains; use a fresh output directory when those change. The full logs and
candidate/survivor inventories stay under ignored `four/build/`.

Extraction preserves arbitrary-precision `positive`, `N`, and `Z` values.
Only small `nat` loop counters use OCaml integers. The command-line bound is
also an OCaml integer, so these sweeps use 4,096; the Coq theorems can weaken
those proved bounds to the much larger champion score.

## Next escalation

Replay the broader sweep's candidates in bounded proof shards and attach them
to the frozen census. Sweep the remaining cores with finite/history n-grams,
larger repeated-word budgets, and affine rules. Apply proved symmetry and
shadow transports to checked cores, retaining their timing offsets. Record
the surviving machine IDs before choosing shared submachine or counter lemmas.
