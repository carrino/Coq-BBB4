# Targeted refinement of capacity near misses

The first capacity pilot left 54 machines with seven certified instruction
targets in at least one abstract graph. Refining those machines to widths 3
and 4 closes **13 additional BOTH families**, including **one additional STATE
family**, relative to the first supplementary campaign. All 13 proofs include
all completions, pending-family membership, and exact checked inventories.
These IDs are disjoint from the 4,227 existing replay candidates.

The new boards contain seven ordinary n-gram certificates and six weighted
certificates. All passed Coq compilation and full recursive kernel audits.
The separate exact-inventory wrappers also passed a full recursive audit.
The precise descriptors are in `burn2-capacity-inventory-check.json`; the
deduplicated local increment is in `burn2-capacity-summary.json`. This batch
alone reduces the first supplement's remaining counts from 33,361 to 33,348
for instructions and from 2,504 to 2,503 for state. Other simultaneous batches
must be unioned by machine ID before publishing combined totals.

Discovery reused the previous per-target witnesses without changing them,
then tried width-3 and width-4 graphs in both orientations. The prefix remains
4,096 steps, with fuel 8,193 and 65 growth rounds. Each native orientation had
a two-second budget, each target LP a three-second budget, and each machine
a 90-second hard limit; one worker had a 2 GiB address-space cap. All 54 rows
completed in 177.012 summed worker wall seconds. There were no worker failures,
hard machine timeouts or LP target timeouts. The 186 graph events included
34 ranking-budget interruptions whose closed graphs were retained and 12
closure-open orientations. Native interruption status also permits stack
overflow, so it is not an exact count of timer expirations.

The 41 remaining misses are retained in the ignored discovery ledger. One
machine, `1LB0LB---3RA_3RB2RA3LB1RA`, produced 4,225-node closed graphs in both
orientations, exceeding the 4,096-node export cap. A subsequent single-machine
retry raised the cap to 8,192 and completed in 7.923 seconds without finding a
complete candidate. The bounded negative result is recorded in
`burn2-capacity-cap8192-search-report.json`; it adds no proof claim.

## Reproduce

With Coq on `PATH`, replay the compact certificates and exact census wrappers:

```bash
python3 four/tools/check_burn2_capacity.py
```

Once reports exist, the same command freshly compiles and audits their exact
frozen sources through the portable weighted adapter. It preserves published
reports and records current runtime evidence under `four/build/burn2-capacity`.
To preserve canonical proof objects as well, choose a separate directory:

```bash
python3 four/tools/check_burn2_capacity.py \
  --output-dir four/build/burn2-capacity-replay
```

Four isolated regression tests check portable paths and reject missing or
changed registries, missing boards, and altered bounds or theorem declarations:

```bash
python3 -m unittest discover -s four/tools -p test_check_burn2_capacity.py
```

Reconstructing historical discovery accounting additionally requires the
ignored earlier discovery ledgers, baseline remaining lists and original
audit receipts. With those preserved local artifacts present:

```bash
python3 four/tools/search_burn2_capacity.py run
python3 four/tools/summarize_burn2_capacity.py --check
```

Proof replay needs only tracked compact inputs and the compiled core. It does
not require the discovery LP solver, native graph binary, previous search
logs, or historical compiled-object hashes. Generated Coq remains ignored.
