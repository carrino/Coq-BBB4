# Third-round history state proofs

The fixed input contains 1,072 remaining state obligations from the second
round's fresh-state cohort. It excludes the exact inventories of 873 weighted,
135 ordinary and nine diagnostic-history families already proved in that
round. `burn3-history-input-manifest.json` records the partition and hashes.
`prepare_burn3_history.py` reproduces this input without launching a search.

Two existing history-checker configurations found 378 disjoint candidates:

| Window width | History length | Attempted | Candidates | Native row seconds |
| ---: | ---: | ---: | ---: | ---: |
| 4 | 3 | 1,072 | 306 | 392.354 |
| 3 | 5 | 766 | 72 | 309.250 |

Both configurations use anchor 4096, fuel 16384 and 32 growth rounds, with a
two-second native budget per row. The second configuration runs only on
misses from the first. The discovery process uses one worker and a 2 GiB
address-space limit. Native results are untrusted search evidence.

All 378 candidates passed the Coq state checker, original census
pending-membership proofs, all-completion state bounds and exact inventory.
The state bound is 4096. This board makes no instruction-quasihalting claim.
The 95 four-row-or-smaller shards and their aggregate/inventory compiled in
2295.023 seconds. Full recursive `coqchk` checked
363 dependency modules with no reused modules in
1120.996 seconds. These are local timings, not portability
requirements.

This leaves 694 obligations in the 1,072-row input. The two searches rejected
622 of those normally; 72 encountered a timeout in one or both configurations.
Neither rejection nor timeout proves anything about the remaining behavior.
Global ledger totals require the separately audited census union.

## Reproduce the proof

Build the core with `make -C four all`, then run from the repository root:

```bash
python3 four/tools/check_burn3_history.py \
  --resume --timeout 300 --audit-timeout 2400
```

The compact input is `burn3-history-proof-input.json`; its candidate inventory
is checked against the frozen search-report hash. The published checked report
is `burn3-history-checked.json`, and accepted machines are in
`burn3-history-machines.json`. Native search executables and ignored discovery
logs are not required for proof replay. The module is
`BBB24Burn3History.HistoryInventory`, with exact-inventory theorem
`inventory_exact`.

Replays preserve published reports, input and generated source bytes. Resume
receipts pin the compiler and complete imported proof-object dependencies,
including generated shards. Every replay finishes with a full recursive audit;
current runtime evidence stays under ignored `four/build/burn3-history/proof/`.
`--select` is only for creating a previously absent compact input after a new
search and must not be used when replaying the published batch.
