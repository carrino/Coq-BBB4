# Third supplementary burndown round

This round adds **676 instruction bounds** and **405 state bounds** to the
[second checkpoint](BURN2.md). Its eight new boards extend the supplement to
28 boards, alongside the frozen original 113-board campaign.

| Bound | Covered in the 133,185-family cohort | Remaining | Remaining before this round |
| --- | ---: | ---: | ---: |
| Instructions | 101,690 | **31,495** | 32,171 |
| State | 132,518 | **667** | 1,072 |

Across all selected inventories, including families outside that cohort,
**124,892 families have both bounds** and **155,720 have a state bound**.
Every family theorem covers all completions and proves original pending
membership. The global BBB(2,4) upper bound remains open; no raw-table weight
subtraction is claimed.

| Method | New instruction bounds | Contribution to new state bounds |
| --- | ---: | ---: |
| Main repeated-word queue, 512 rows | 512 | 0 |
| Deeper state-history search | 0 | 378 |
| Instruction upgrades of those history certificates | 160 | 0 |
| Targeted history pilot | 2 | 0 |
| Paired-digit tail invariant | 1 | 0 |
| Adjacent-pair capacity invariant | 1 | 0 |
| Relaxed marker invariant | 0 | 27 |
| **Total** | **676** | **405** |

The 160 instruction-upgrade IDs are a subset of the 378 state-history IDs.
Their state gains are assigned to that state-history board in the table and
counted once in the exact union. The other new boards are disjoint. The
deduplicated report is
[`burn3-burndown-summary.json`](research/burn3-burndown-summary.json).

## Reproduce

With the [repository Coq toolchain](../docs/VERIFYING.md) on `PATH`, run from
the repository root:

```bash
make -C four list-burn3-campaign
make -C four check-burn3-campaign
```

The [build plan](research/burn3-campaign-build.json) replays compact frozen
inputs, preserves published evidence, and audits freshly compiled objects.
It runs no discovery search and needs no LP solver. Its default is one replay
worker; `CAMPAIGN_JOBS=2` permits two independent batches when memory allows.
The marker batch depends on the marker example's theorem package. All other
new boards depend only on the core.

To reconstruct the full union and remaining per-family lists, also replay the
original checkpoint and run the accounting check:

```bash
make -C four check-campaign
python3 four/tools/summarize_next_burndown.py \
  --supplement-manifest four/research/burn3-campaign-input.json \
  --supplement-report four/research/burn3-campaign-summary.json \
  --report four/research/burn3-burndown-summary.json \
  --output-dir four/build/burn3-burndown
```

Repeat the Python command with `--check` to compare every report and ledger
byte. Its delta fields compare against the original 113-board checkpoint;
subtract the second round's corresponding fields to recover this round's
increment. Generated Coq, proof objects, audit receipts and full ledgers stay
under ignored `build/` paths. Replay validates any reused audit receipt against
the current sources, objects, dependencies and runtime.

## Proof methods

The [history search](research/burn3-history.md) tried width 4/history 3 and then
width 3/history 5 on the exact 1,072-family state remainder, with anchor 4,096,
fuel 16,384 and 32 growth rounds. All 378 candidates passed state-only proofs.
The [instruction pass](research/burn3-history-instruction.md) reused each
candidate's configuration with the stronger instruction checker; all 160
accepted cases passed both-bound proofs. Its 138 native timeouts and 80
completed rejections remain separate search outcomes.

Three small handwritten developments address structural obstacles:

- The [tail invariant](research/burn3-tail-invariant.md) preserves seven phases
  of paired tape digits. For `1LB2LA1RB3RB_3RA1RB3LA1RA`, B1 last fires at
  configuration 9 and is absent from step 10 onward. The other seven
  instructions and both states recur. This proves exact instruction score 10.
- The [pair-capacity invariant](research/burn3-pair-capacity.md) counts adjacent
  tape pairs to supply a missing boundary condition for an existing binary
  rank. For `1LB2RA3RA0RA_1RA2LA0LB3LA`, all eight instructions recur, giving
  both bounds 0. The theorem includes checked local count deltas and padding.
- The [relaxed marker invariant](research/burn3-relaxed-marker.md) permits
  marked left moves that stay in B. Preservation and descent of the padded
  potential still imply recurrence. The example and a separate 26-family
  board prove 27 new state bounds at 0, with no instruction claim.

These sources have exact replay inputs, regression examples where applicable,
and independent mathematical and kernel review. They use the repository's
existing functional extensionality assumption. Existing core sources remain
unchanged; the handwritten modules are replayed in separate namespaces from
tracked source files.

The [targeted capacity history pilot](research/burn3-capacity-instruction.md)
contributes two additional instruction bounds using the existing checker.
The repeated-word tranche uses frozen input rows 384 through 895, disjoint
from the preceding tranches. Each of its 512 proofs includes exact inventory
and census membership.

## Remaining work

The existing replay queue contains **2,740 instruction candidates**: 1,905
from the main repeated-word lane and 835 from timeout recovery. It contains
no state obligations. The exact **667 state holdouts** are partitioned into
68 timeout-affected history searches and 599 completed rejections before new
retries. Wider searches, longer timeout budgets and stronger invariants remain
discovery work until their certificates pass kernel replay.
