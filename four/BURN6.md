# Sixth supplementary checkpoint

Six audited boards add **63 instruction bounds** and **four state bounds**
to the [fifth checkpoint](BURN5.md). The supplement now has 41 boards.

| Bound | Covered in the 133,185-family cohort | Remaining | Remaining before this checkpoint |
| --- | ---: | ---: | ---: |
| Instructions | 101,766 | **31,419** | 31,482 |
| State | 132,651 | **534** | 538 |

Across all selected inventories, **124,968 families have both bounds** and
**155,853 have a state bound**. The exact deduplicated union is recorded in
[`burn6-burndown-summary.json`](research/burn6-burndown-summary.json).
Every family theorem covers all completions and proves original pending
membership. Raw census weights are unchanged. The global BBB(2,4) upper bound
remains open.

## New proofs

| Board | New instruction bounds | New state bounds | Instruction / state upper bound |
| --- | ---: | ---: | --- |
| [Swapped ternary entries](research/burn4-ternary-swapped.md) | 6 | 0 | 8 / 0 |
| [Instruction history retry, continuation](research/burn4-history-timeout8.md) | 16 | 0 | 4,096 / 4,096 |
| [Conjugacy reuse](research/burn5-structural-instruction.md) | 20 | 0 | 8,192 / 8,192 |
| [Paired-digit tail templates](research/burn5-tail-template.md) | 21 | 0 | 147 / 0 |
| [History closure pilot](research/burn4-history4-continuation-closure.md) | 0 | 1 | — / 4,096 |
| [History growth continuation](research/burn4-history4-continuation-growth64.md) | 0 | 3 | — / 4,096 |

These are upper bounds, not claims of exact instruction scores. All 63 new
instruction families already had state bounds. The four state additions are
disjoint from those families and from earlier state coverage.

The swapped ternary proofs check each actual blank-start prefix before
exchanging states in the suffix. State exchange alone is not a symmetry of
the blank-start problem. Symbol relabeling and reflection then reuse the
accepted counter theorem.

Refreshing the conjugacy source inventory exposed 20 more short prefix
intersections with already proved runs. Exact transport checks include the
time offset. Separately, the paired-digit template transports seven active
transitions while permitting a dormant tape suffix beyond a permanent marker;
all 21 concrete entries are checked. One overlapping candidate belongs only
to the conjugacy board.

The history experiments distinguish search-budget changes. Raising fuel
alone found no candidate in the initial closure pilot. Raising graph-growth
rounds from 32 to 128 found one; a 64-row continuation found three more. Only
their replayed certificates count. The accepted configuration uses width 4,
history depth 4, anchor 4,096 and fuel 131,072.

## Reproduce

With the [Coq toolchain](../docs/VERIFYING.md) on `PATH`, run from the repository
root:

```bash
make -C four list-burn6-campaign
make -C four check-burn6-campaign
```

The [40-step plan](research/burn6-campaign-build.json) replays all earlier
supplementary proofs and the combined coverage theorem. Its dependencies
explicitly build the original counter and tail packages before their
transports. `CAMPAIGN_JOBS=2` permits two independent proof batches. Native
discovery searches are unnecessary for replay.

Rebuild the original campaign as well to regenerate the full ledger and
remaining-family lists:

```bash
make -C four check-campaign
python3 four/tools/summarize_next_burndown.py \
  --supplement-manifest four/research/burn6-campaign-input.json \
  --supplement-report four/research/burn6-campaign-summary.json \
  --report four/research/burn6-burndown-summary.json \
  --output-dir four/build/burn6-burndown
```

Repeat the Python command with `--check` to verify every report and ledger
byte. Summary delta fields compare against the original 113-board campaign;
the difference from checkpoint five is this checkpoint's gain. The existing
replay queue retains **2,740 instruction candidates** and no state obligations.
Later growth searches and larger repeated-word batches remain outside this
frozen checkpoint until their proofs and aggregate audit pass.
