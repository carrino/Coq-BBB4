# BBB(2,4) burndown

**This is an early survey, not the remainder after the full BBB(4) pipeline.**
Only exact/translated cycles were swept at 256 steps, followed by affine search
on a sample. The [grouping investigation](GROUPING.md) reduces the raw family
list to **284,541 symmetry representatives**, with **10,572 candidate shadows**
of **273,969 nonblank-start cores**, and identifies the missing pipeline stages.

Baseline: 2026-10-26. The 256-step exploratory survey leaves **611,360
partial-table families**, representing **39,521,784 raw tables** after the
initial-transition symmetry multipliers. This is the practical search queue;
the number of difficult families after stronger filtering is still unknown.

A family fixes some transitions and leaves others as `---`. Each free cell has
17 possible completions. Family counts and raw-table weights therefore measure
different things. The machine string is the stable row identifier. The two
initial-transition classes below are representatives, not a full quotient by
all state/symbol symmetries.

For the non-halting search we can focus on **16^8 = 4,294,967,296 fully defined
tables**. `TotalCompletion.totalize_scores` proves that filling a non-halting
machine's unused entries preserves its exact state and instruction scores.
The same 611,360 survey families represent **33,908,616 fully defined tables**
(using 16 rather than 17 choices per free cell). Their family count does not
change: the partial rows are compressed descriptions, not records to discard.

The unrestricted BBB theorem still includes halting machines.
`global_bounds_from_total_and_halts` records the remaining obligation explicitly:
a bound for total tables plus a sufficiently small bound for halting times
implies the unrestricted result. No halting-time bound is assumed here.

## Search queue

| Initial-transition class | Families | Raw-table weight including multiplier |
| --- | ---: | ---: |
| `A0 = 0LB` (multiplier 2) | 63,426 | 5,684,292 |
| `A0 = 1LB` (multiplier 6) | 547,934 | 33,837,492 |
| Total | **611,360** | **39,521,784** |

Only 1,024 families have had the recorded affine search run, with 512 sampled
from each class. Its current ledger is:

| Status | Families | Meaning |
| --- | ---: | --- |
| `coq_checked` | 4 | Both bounds and all completions checked; theorem linked |
| `candidate_unchecked` | 782 | Search found a candidate; Coq acceptance still required |
| `no_certificate` | 238 | No candidate found at the recorded search budget |
| `not_sampled` | 610,336 | Outside this affine-search sample |

The **238 search holdouts are a sample**, not the complete list of difficult
machines. A budget-limited failure also does not imply mathematical difficulty.
Do not extrapolate their proportion to the full population.

| Search failure | Sampled families | Next investigation |
| --- | ---: | --- |
| `noshape` | 98 | Inspect tape evolution and look for another recurring template |
| `nofit` | 64 | Inspect counter samples, residues, and affine fitting |
| `noproof` | 76 | Inspect auxiliary rules and symbolic replay failures |

The experimental three-sample fitter found four additional candidates (234
remaining failures). This ledger deliberately uses the reproducible baseline
fitter; those four are not additional checked proofs.

## Proof queue

The **certified eight-step census** still has **1,756,620 pending leaves**, with
structural weight **216,078,348 raw tables**. Its coverage theorem accounts for
every table, but its pending set has not been replaced by the deeper survey.

The four affine completion theorems prove both state and instruction bounds at
4,096. They have not yet been attached to the census coverage proof. Consequently
`census_linked` is `no` even on their rows, and the certified pending weight has
not decreased. The exploratory symmetry multipliers also need a coverage proof
before they can be used in the formal census.

The burndown has three separate milestones per family:

1. Search finds a candidate certificate.
2. Coq checks the state and instruction bounds, with a named completion theorem.
3. The exhaustive census consumes that theorem and removes the obligation.

Only the third milestone reduces the certified remainder. Keep separate state
and instruction bound columns even though the current four proofs establish both.

## Next work

- [x] Enumerate the fixed 256-step residual queue and record input hashes.
- [x] Port the affine checker and validate four representative families.
- [x] Measure symbol orbits and blank-prefix shadow links; keep transports
  separate from proof discharge (see [GROUPING.md](GROUPING.md)).
- [ ] Run the broader BBB(4)-style checker pipeline on representative cores
  before treating the early survey remainder as difficult holdouts.
- [ ] Check the remaining **782** sampled candidates; retain any Coq rejections
  as checker investigation cases, rather than counting them as solved.
- [ ] Measure search/checking cost, then run budgeted, resumable batches over the
  **610,336** unsampled families.
- [ ] Group the no-certificate cases by observed behavior, starting with the
  **98 `noshape`** examples; retain individual machine IDs and evidence.
- [ ] Attach accepted certificates and deeper enumeration to the coverage proof,
  including a justified symmetry reduction or unrestricted enumeration.
- [ ] Reach zero certified pending obligations before claiming a global maximum.

## Lists, reproduction, and updates

- [`research/burndown-sample.tsv`](research/burndown-sample.tsv): all 1,024 sampled
  families, failure reasons, completion weights, separate bounds, and proof names.
- [`research/burndown-summary.json`](research/burndown-summary.json): aggregate
  counts and hashes of the complete residual files.
- [`research/burndown-verified.json`](research/burndown-verified.json): explicit
  proof evidence at commit `97e9193964c0e3a9c86758da190c137f10a8afe8`. A source hash
  prevents an edited or merely newly generated certificate from gaining checked
  status automatically.
- `four/build/burndown-inventory.tsv`: generated full list of 611,360 families,
  ignored by Git. `family_weight` excludes `root_multiplier`; multiply them only
  for exploratory raw-table accounting. `total_completion_weight` instead uses
  16 choices per free cell, restricting to fully defined tables.

From the repository root:

```bash
# Needed once, or after removing the ignored build artifacts:
python3 four/tools/triage.py --irules /path/to/BBB/bin/irules

# Reproduce compact tracked outputs and optionally the full local inventory:
python3 four/tools/burndown.py --inventory
python3 four/tools/burndown.py --check

# List the 238 baseline sample failures:
rg 'noshape|nofit|noproof' four/research/burndown-sample.tsv
```

The burndown exporter validates counts, weights, uniqueness, sample membership,
and recorded proof-source hashes. It is bookkeeping; `make -C four check -j2`
provides the proof check. Update the verified registry only after that audit,
then regenerate the ledger. Preserve the baseline when adding a new search
pass, and report its budget, input hash, new candidates, checked proofs, and
census-linked obligations separately. A time-series chart becomes useful once
there is a second comparable full-queue checkpoint.
