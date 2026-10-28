# One additional history state proof

`1LB2RB3RB2RA_3RB3LA0LB1LB` has a certified state-quasihalting bound of 4096.
The proof includes original census membership, all-completion coverage and an
exact inventory. It adds one state family beyond the 667-family residual and
is disjoint from the separate 121-family entry-marker board. This package
makes no instruction-bound claim.

A bounded 16-family pilot found the certificate using window width 4, history
length 4, anchor 4096, fuel 32768 and 32 growth rounds. The successful native
evaluation took 0.043 seconds. Separate native controls also succeeded with
history 4 and fuel 16384, while history 3 with doubled fuel still rejected.
These controls guide further search; the Coq replay establishes the bound.

The three generated proof modules compiled in 5.965 seconds. Full recursive
`coqchk` checked all 269 dependency modules without reuse in 38.140 seconds.
Exact source regeneration, inventory, source/object hashes and the current
dependency snapshot were validated. A subsequent read-only resume preflight
reused all three objects and left 65 watched artifacts unchanged.

After `make -C four all`, replay from the repository root:

```bash
python3 four/tools/check_burn4_history_refinement.py \
  --resume --timeout 120 --audit-timeout 600
```

The required compact input, frozen search report, checked report and inventory
are the files named `burn4-history-refinement-pilot-` followed by
`proof-input.json`, `search.json`, `checked.json` and `machines.json`.
The descriptor is in the checked report under `descriptor`; its module is
`BBB24Burn4HistoryRefinement.HistoryInventory` and its inventory theorem is
`inventory_exact`.

Native executables, discovery logs and broader search queues are not required
for replay. Generated Coq and current audit receipts remain under ignored
`four/build/burn4-history-refinement-pilot/proof/`. Published evidence is
preserved; every replay finishes with a full recursive kernel audit.
