# BBB(2,4) burndown

**The 611,360-family baseline is an early survey, not the remainder after the
full BBB(4) pipeline.** It used exact/translated cycles at 256 steps, followed
by affine search on a sample. The [grouping investigation](GROUPING.md) reduces the raw family
list to **284,541 symmetry representatives**, with **10,572 candidate shadows**
of **273,969 nonblank-start cores**. The [pipeline update](PIPELINE.md) adds
closure sweeps, checked certificate replay, and census closeout. The baseline
tables below remain frozen so successive passes can be compared.

The first complete cheap closure sweep over **273,969 core representatives**
found **93,792 candidates**, leaving **180,177** for stronger filtering. These
are search outcomes, not kernel-checked discharges or final hard holdouts.
See [the full stage table](PIPELINE.md#first-complete-core-sweep).

The [second full wave](WAVE2.md) added 46,992 candidates. Across those two sweeps,
**140,784 core representatives have search candidates** and **133,185 remain**
for stronger methods, including 13 timeouts. At that checkpoint, **11,336 distinct
families had checked bounds and census links**, including **649 of the
original 1,024-family sample**. That checked closeout is tracked in
[`wave2-families.tsv`](research/wave2-families.tsv), with the
deduplicated counts in [`wave2-summary.json`](research/wave2-summary.json).
The original-sample ledger is [`wave2-sample.tsv`](research/wave2-sample.tsv).

The [stronger census campaign](WAVE3.md) continues from that frozen 133,185-row
cohort. It adds weighted n-grams, deeper affine and closure checks, reuse of
proved recurring behavior, and separate state-only solvers. The combined
checked inventories and their intersection with the starting cohort are
recorded in [`campaign-final-summary.json`](research/campaign-final-summary.json).
The [first supplementary round](NEXT_BURNDOWN.md) adds 131 instruction families
and 254 state families to that frozen checkpoint. The [second round](BURN2.md)
adds another **1,190 instruction bounds** and **1,432 state bounds**, and the
[third round](BURN3.md) adds **676 instruction bounds** and **405 state bounds**.
The [fourth checkpoint](BURN4.md) adds another **122 state bounds**. The
[fifth](BURN5.md) adds **13 instruction bounds and seven state bounds**, and
the [sixth](BURN6.md) adds **63 instruction bounds and four state bounds**. Of the
133,185 starting families, **101,766 have both bounds checked** and **132,651
have a state bound checked**, leaving **31,419 instruction-bound** and **534
state-bound** obligations. The exact union and per-machine lists are recorded
in [`burn6-burndown-summary.json`](research/burn6-burndown-summary.json).
The earlier separate search queue had **32,629** rows, down **75.5%** from the
starting cohort. The existing replay queue now has **2,740 instruction
candidates** and no remaining state obligations. Search candidates and
completed Coq discharges remain separate counts.

## First checked sample snapshot

The [first checked sample ledger](research/progress-sample.tsv) combines audited
affine replay and closure-pilot proofs without double-counting their overlap:

| Status at the first checkpoint in the 1,024-family sample | Families |
| --- | ---: |
| Both bounds checked | **637** |
| Affine checker rejected; no other checked proof yet | 151 |
| No affine search certificate; no other checked proof yet | 236 |
| Of the 637 checked: linked to refined census coverage | **80** |

The affine replay proves 628 families; the closure pilot proves 76, with 67
in common. The pilot therefore adds nine distinct proofs, including seven
rejected affine certificates and two affine search failures. The 80 linked
families are the four original affine examples and the 76 pilot families.
At that checkpoint, 557 checked families still needed census links; the second
wave has attached all of them. These are sample counts, not the size of the
full queue or a population-rate estimate.

[`research/progress-summary.json`](research/progress-summary.json) records the
counts and evidence hashes. Reproduce with `python3 four/tools/progress.py
--check` after the builds in [PIPELINE.md](PIPELINE.md). Rejected checker calls
remain explicit investigation cases; rejection does not refute a bound.

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

The baseline affine search sampled 1,024 families, with 512 from each class.
Its original ledger is:

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

The four original affine completion theorems now have census links in
`AffineCloseout.v`. The closure pilot adds 76 more distinct families and a
combined `bootstrap_pipeline_coverage` theorem. All completions of those 80
family records are excluded from the refined residual. This does not remove
80 entire eight-step leaves or recompute the original structural counts.
The exploratory symmetry quotient still needs a coverage link before its
population counts can be used in the formal census.

The burndown has three separate milestones per family:

1. Search finds a candidate certificate.
2. Coq checks the state and instruction bounds, with a named completion theorem.
3. The exhaustive census consumes that theorem and removes the obligation.

Only the third milestone excludes a family from the certified remainder. Keep separate state
and instruction bound columns even though the current four proofs establish both.

## Next work

- [x] Enumerate the fixed 256-step residual queue and record input hashes.
- [x] Port the affine checker and validate four representative families.
- [x] Measure symbol orbits and blank-prefix shadow links; keep transports
  separate from proof discharge (see [GROUPING.md](GROUPING.md)).
- [x] Port n-gram, finite-end/history n-gram, and repeated-word sound checkers.
- [x] Kernel-check and census-link all 76 closure-pilot successes and the four
  original affine examples.
- [ ] Complete the broader escalation ladder on representative cores before
  treating survivors as difficult holdouts.
- [ ] Attach further accepted replay batches to census coverage; retain Coq
  rejections as checker investigation cases rather than counting them as solved.
- [ ] Measure search/checking cost, then run budgeted, resumable batches over the
  **610,336** unsampled families.
- [ ] Group the no-certificate cases by observed behavior, starting with the
  **98 `noshape`** examples; retain individual machine IDs and evidence.
- [ ] Extend checked closeout and deeper enumeration to the coverage proof,
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
