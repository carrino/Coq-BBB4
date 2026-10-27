# First supplementary burndown round

This round adds **131 instruction-bound families** and **254 state-bound
families** to the frozen 113-board campaign, counting each machine ID once.
The exact union is recorded in
[`next-burndown-summary.json`](research/next-burndown-summary.json).

Within the original 133,185-family comparison cohort:

| Bound | Previously outside the closeout | Newly covered | Remaining |
| --- | ---: | ---: | ---: |
| Instruction, with state coverage | 33,492 | 131 | **33,361** |
| State | 2,758 | 254 | **2,504** |

These are census-family counts. Each accepted board proves bounds for every
completion, membership in the original formal pending predicate, and exact
equality with its published inventory. The global BBB(2,4) upper bound remains
open, and the original census table weights are unchanged.

## What the agents checked

| Batch | New instruction families | New state families |
| --- | ---: | ---: |
| Repeated-word replay | 32 | 1 |
| Timeout recovery: finite, n-gram, and history methods | 93 | 11 |
| Supplied weighted state certificates | 0 | 240 |
| Capacity and per-instruction portfolio certificates | 5 | 1 |
| Existing exact champion, now attached to the census | 1 | 1 |

The six supplementary boards contain 131 distinct both-bound IDs and 371
state-covered IDs. Of the latter, 117 already had state proofs in the baseline;
the increment is therefore 254. The three-row repeated-word pilot and eight-row
weighted-state pilot are subsets of the larger batches and are counted once.

The champion entry transports the existing exact theorem to the canonical
reflected machine `1LB2RA1LA1RB_0RB2LB3LB1RA`. Its score remains
**205,770,076,433,044,242,247,860**. The new checker requires an explicit exact
singleton declaration and checks the reported score in binary while preserving
`scoreN` in proof types. This avoids evaluating the enormous score as unary
`nat`. Historical reports retain the champion as their generic-solver control.

All 32 repeated-word, 93 timeout, and 240 weighted-state replay candidates
passed without final-batch failures or timeouts. A representative repeated-word
comparison found direct replay faster than supplying the complete graph and
ranking witnesses, so the 32-row batch uses direct replay. The supplied-witness
pilot is retained as a checked experiment, with timings in
[`next-rw-direct-pilot.json`](research/next-rw-direct-pilot.json).

The capacity search tested 128 fresh residual IDs, excluding every previously
assigned queue ID and prior diagnostic samples. Its five successful candidates
then passed certificate, pending-membership, inventory, and kernel checks.
See [the capacity notes](research/next-capacity.md) for budgets and outcomes.

## Reproduce the proofs

With the repository's Coq toolchain on `PATH`, run from the repository root:

```bash
make -C four list-next-campaign
make -C four check-next-campaign
```

The dependency plan in
[`next-campaign-build.json`](research/next-campaign-build.json) rebuilds the
core and six new boards from tracked compact inputs, then checks their combined
coverage, pending-membership, and exact inventory theorems. It runs serially by
default. Proof replay needs no discovery search, LP solver, or old search logs.
Generated Coq, proof objects, runtime receipts, and large per-machine ledgers
remain under ignored `four/build/` directories. Portable adapters preserve the
published reports while recording current object hashes and audits locally.

The supplement has its own complete dependency audit. It does not rerun the
entire earlier 113-board campaign. To reconstruct and verify the combined
burndown lists after both campaigns have been replayed:

```bash
make -C four check-campaign
python3 four/tools/summarize_next_burndown.py
python3 four/tools/summarize_next_burndown.py --check
```

The summary checks both current audit receipt chains and their source/object
hashes before calculating the union. It writes the combined family lists,
remaining cohort IDs, newly covered IDs, and remaining candidate queue under
`four/build/next-burndown/`. Local audit receipt identities are excluded from
the portable summary.

## Continue the burndown

The remaining existing replay queue has **4,227 instruction candidates** and
**409 state obligations** among those same IDs:

- **2,801 repeated-word candidates**, including 124 state obligations.
- **1,426 timeout repeated-word candidates**, including 285 state obligations.

All 240 queued weighted-state certificates are now checked. Candidate counts
remain scheduling counts until their proofs pass. Assign work from
`four/build/next-burndown/queued.tsv` so completed pilot IDs are not retried or
counted twice. Keep bounded batches and per-row timeout records.

The next timeout batch can be selected reproducibly with:

```bash
python3 four/tools/check_next_timeout.py run \
  --batch rw256-v1 --modes rw --limit 256 \
  --timeout 20 --audit-timeout 900 --resume
```

For further discovery, the capacity pilot recorded 54 misses that cover seven
instruction targets in one orientation. Those offer a focused next experiment
with larger windows or complementary orientations. Preserve the distinction
between new candidates, checked family bounds, and the remaining exhaustive
census obligation.
