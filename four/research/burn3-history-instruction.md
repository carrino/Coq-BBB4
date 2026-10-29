# Instruction upgrades from state-history certificates

The third-round state-history search produced 378 candidates. Reusing their
exact per-family parameters with the existing instruction-mode history checker
produced **160 additional instruction proofs**. Every accepted family has both
bounds at 4,096, with all completions covered, original census pending membership,
and an exact checked inventory.

All 160 IDs belong to the 378-family state-history board. Combining the boards
therefore adds 160 instruction obligations and does not add another 160 state
obligations. Their inventories are disjoint from the previous 20-board supplement,
the repeated-word and timeout-priority queues, and the two capacity instruction
proofs.

| Native instruction-mode result | Families |
| --- | ---: |
| Accepted and subsequently kernel-audited | 160 |
| Rejected within the search budget | 80 |
| Timed out after two seconds | 138 |

The first history configuration supplied 130 accepted families and the second
supplied 30. Both use anchor 4,096, fuel 16,384 and 32 growth rounds; their window
width/history depth pairs are 4/3 and 3/5. The new search changes only the checker
mode from state-only to both-bound. It does not modify the state proof artifacts.

The complete native input and results are in
[`burn3-history-instruction-plan.json`](burn3-history-instruction-plan.json) and
[`burn3-history-instruction-search.json`](burn3-history-instruction-search.json).
Rejections and timeouts are separate scheduling categories, not impossibility
results. No unresolved row is counted as a proof success.

## Replay

After `make -C four all`, run from the repository root:

```bash
python3 four/tools/check_burn3_history_instructions.py \
  --resume --timeout 300 --audit-timeout 2400
```

The compact input, published native result inventory, and existing
`AdvancedPipeline` proof sources suffice. The native discovery executable and
discovery logs are not needed. Do not use `--select` for normal replay; that flag
creates a missing initial compact input and refuses to replace a published one.

The runner checks the exact input/source inventory, compiles 40 four-family
shards plus the aggregate and exact-inventory wrapper, and performs a full
recursive kernel audit. Resume receipts include the compiler and imported proof
objects. Ordinary replay preserves the published report and writes current
runtime evidence under ignored `build/burn3-history-instruction/proof/` paths.

The original run compiled all 42 modules without failures in 1,913.375 seconds
and audited the complete 308-module dependency closure in 977.659 seconds,
with zero reused audit modules. The
[checked report](burn3-history-instruction-checked.json) records the descriptor,
95 consumed source pins, 42 generated object pins, and the recursive receipt.
The global BBB(2,4) upper bound remains open.
