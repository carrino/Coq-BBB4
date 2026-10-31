# Six additional state proofs from history refinement

The history4 continuation certifies six census families with a state-quasihalting
bound of 4096. Every family belongs to the frozen 545-family state residual;
removing this board alone leaves 539. The package makes no instruction-bound
claim. It includes exact inventory, original census membership and coverage of
all completions.

The native search reused a 32-family pilot and evaluated the remaining 498
families at window width 4, history length 4, anchor 4096, fuel 32768 and 32
growth rounds. The 530-family cohort produced six candidates, 504 completed
rejections and 20 timeouts in 272.497 aggregate row seconds. Fourteen previous
rejections and one previous timeout stayed separate. Native outcomes are search
evidence only.

All six candidates passed Coq replay in three cost-aware proof shards. Five
generated modules compiled in 72.480 seconds; full recursive `coqchk` checked
all 271 dependency modules without reuse in 71.905 seconds. A subsequent
read-only validation matched the complete current dependency snapshot, source
and object hashes, exact inventory and audit log. Five integrity tests cover
the shard partition, including missing, duplicated, reordered and substituted
families.

After `make -C four all`, replay from the repository root:

```bash
python3 four/tools/check_burn4_history4_continuation.py \
  --resume --timeout 600 --audit-timeout 2400
python3 -m unittest discover -s four/tools \
  -p test_burn4_history4_continuation.py
```

Portable replay requires the files with prefix
`research/burn4-history4-continuation-` and suffixes `proof-input.json`,
`shard-plan.json`, `search.json`, `checked.json` and `machines.json`, plus the
runner and its existing repository dependencies. No native executable or
discovery log is required. `--select` is a discovery-time operation and must
not be used when replaying this frozen package.

The descriptor is `descriptor` in the checked report, with module
`BBB24Burn4History4Continuation.HistoryInventory` and theorem `inventory_exact`.
Generated sources and new audit receipts remain under ignored
`four/build/burn4-history4-continuation/proof/`; accepted evidence is preserved.
These six proofs are separate from the frozen 30-board checkpoint and require
an aggregate census audit before its published totals are updated.
