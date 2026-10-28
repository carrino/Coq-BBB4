# Fourth supplementary checkpoint

Two audited boards add **122 state bounds** to the [third round](BURN3.md).
They add no instruction bounds and are disjoint from all earlier accepted
families. The complete supplement now has 30 boards.

| Bound | Covered in the 133,185-family cohort | Remaining | Remaining before this checkpoint |
| --- | ---: | ---: | ---: |
| Instructions | 101,690 | **31,495** | 31,495 |
| State | 132,640 | **545** | 667 |

Across all selected inventories, **124,892 families have both bounds** and
**155,842 have a state bound**. The exact union is recorded in
[`burn4-burndown-summary.json`](research/burn4-burndown-summary.json).
All completions and original pending membership are proved. The global
BBB(2,4) upper bound remains open, and raw census table weights are unchanged.

## Reproduce

With the [repository Coq toolchain](../docs/VERIFYING.md) on `PATH`, run from
the repository root:

```bash
make -C four list-burn4-campaign
make -C four check-burn4-campaign
```

The [29-step plan](research/burn4-campaign-build.json) includes all earlier
supplementary boards and runs no discovery searches. Its default is one
worker; `CAMPAIGN_JOBS=2` permits two independent batches when memory allows.
Handwritten sources and compact inputs are tracked; generated Coq and runtime
receipts stay under ignored `build/` paths. Published reports remain frozen.

Rebuild the original campaign as well to regenerate the full deduplicated
ledger and remaining lists:

```bash
make -C four check-campaign
python3 four/tools/summarize_next_burndown.py \
  --supplement-manifest four/research/burn4-campaign-input.json \
  --supplement-report four/research/burn4-campaign-summary.json \
  --report four/research/burn4-burndown-summary.json \
  --output-dir four/build/burn4-burndown
```

Repeat the Python command with `--check` to compare all report and ledger
bytes. Summary delta fields compare against the original 113-board campaign;
the difference from `burn3-burndown-summary.json` is this checkpoint's gain.

## New state proofs

The [entry-marker checker](research/burn4-entry-marker.md) proves 121 state
bounds at **0**. Every A-to-B entry establishes a marked cell at or to the
right of the head. B-to-B steps preserve that condition; capacity and a
decreasing padded potential force return to A. The existing one-state
reachability argument supplies B recurrence. A-only steps need not preserve
the marker condition. This is a complementary checker with its own entry
requirements; no general superset relation with the earlier marker checker
is claimed. Its theorem, 14 regression examples, exact inventory and full
recursive kernel audit passed independent review.

The [history refinement](research/burn4-history-refinement.md) proves state
bound **4,096** for `1LB2RB3RB2RA_3RB3LA0LB1LB` using width 4 and history
depth 4. A controlled native comparison found that increasing history depth
succeeds at the old fuel limit too, while increasing fuel alone does not.
Only the Coq-replayed certificate counts as proof. The one-row board passed
exact inventory, pending membership and a full recursive audit, and is
disjoint from the marker board.

The existing instruction replay queue still contains **2,740 candidates**
and no state obligations. The **545 state holdouts** are exact remaining
family IDs in this frozen ledger. Later budget retries and counter packages
belong to subsequent checkpoints.
