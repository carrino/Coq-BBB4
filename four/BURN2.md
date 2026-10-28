# Second supplementary burndown round

This round extends the [first supplement](NEXT_BURNDOWN.md) with repeated-word
replay, wider state searches, capacity refinements, conjugacy transport, and
history certificates. The exact per-family union is recorded in
[`burn2-burndown-summary.json`](research/burn2-burndown-summary.json).

The 14 new boards remove **1,190 instruction obligations** and **1,432 state
obligations** from the first supplement's remainder. The expanded supplement
contains 20 boards; together with the original 113-board checkpoint it gives:

| Bound | Covered in the 133,185-family cohort | Remaining | Remaining before this round |
| --- | ---: | ---: | ---: |
| Instructions | 101,014 | **32,171** | 33,361 |
| State | 132,113 | **1,072** | 2,504 |

Across all accepted inventories, including families outside that cohort, the
union contains **124,216 families with both bounds** and **155,315 with a state
bound**. These increments are deduplicated against the prior checkpoint:

| Method | New instruction bounds | New state bounds |
| --- | ---: | ---: |
| Main repeated-word queue | 384 | 124 |
| Timeout replay, including state priority | 591 | 285 |
| Capacity refinements and state follow-up | 13 | 6 |
| Wider weighted-state search | 0 | 873 |
| Ordinary n-gram successes from that search | 135 | 135 |
| Conjugacy transport | 67 | 0 |
| Diagnostic history search | 0 | 9 |
| **Total** | **1,190** | **1,432** |

Every accepted family theorem covers all completions and proves membership in
the original formal pending predicate. Family IDs are counted once. The global
BBB(2,4) upper bound remains open; the original census table weights are unchanged.

## Reproduce the proofs and inventories

With the [repository Coq toolchain](../docs/VERIFYING.md) on `PATH`, run from the
repository root:

```bash
make -C four list-burn2-campaign
make -C four check-burn2-campaign
```

The [dependency plan](research/burn2-campaign-build.json) rebuilds the first
supplement and this round from compact inputs. It does not run discovery searches
or require an LP solver. Each batch and the combined coverage theorem are audited.
Generated Coq shards and proof objects remain under ignored `four/build/` paths.
The portable replay checks frozen inputs, sources and inventories, preserves the
published reports, and records current execution receipts under `build/`.

After replay, run the input and inventory integrity regressions with:

```bash
python3 -m unittest discover -s four/tools -p 'test*burn2*.py'
```

To reconstruct the global union and remaining per-family lists, also replay the
frozen 113-board checkpoint:

```bash
make -C four check-campaign
python3 four/tools/summarize_next_burndown.py \
  --supplement-manifest four/research/burn2-campaign-input.json \
  --supplement-report four/research/burn2-campaign-summary.json \
  --report four/research/burn2-burndown-summary.json \
  --output-dir four/build/burn2-burndown
```

Repeat the Python command with `--check` to compare every generated ledger and
report byte. Outputs include separate instruction/state remaining lists, newly
covered IDs, and the remaining candidate queue. The summary's delta fields compare
against the original 113-board checkpoint; this round's increment is the difference
from [`next-burndown-summary.json`](research/next-burndown-summary.json).

## What changed in the search

The repeated-word batches prioritize the 124 state obligations in the main queue.
The timeout lane first replays two disjoint batches, then selects every remaining
state obligation from that queue. All selections retain exact input inventories.

The wider weighted-state search uses width 3 and anchor 4096 with the existing
weighted-state checker. It also extracts ordinary n-gram successes, which prove
both bounds. Candidates produced by both methods are assigned to one board.
See the [state search notes](research/burn2-state-notes.md) for parameters and
individual replay commands.

The conjugacy sweep expands its sources beyond the eight boards used by the
earlier sweep. It requires an exact finite configuration intersection after state
swapping and a checked transition-table relation. Replay reconstructs only the
64 source certificates needed for the 67 accepted transports. Increasing the
finite probe from 4,096 to 65,536 steps found no additional intersections among
the 887 unqueued table candidates. See the [transport notes](research/burn2-structural.md).

The capacity pass revisits 54 seven-target near-misses with wider windows and
combined orientations, certifying 13 families. A focused retry raising one
4,225-node graph's export limit to 8,192 found no additional candidate. Selected
instruction capacity and direct state-target ranking experiments on 32 fresh
state misses also found no complete candidates. These bounded negative results
do not rule out the methods; their theorem prototypes remain local research.
See the [capacity notes](research/burn2-capacity.md).

A final pass over the five remaining capacity cases with state obligations
extracts one already ranked instruction per state from their saved graphs.
All five pass the existing weighted-state checker using ordinary ranking alone.
The compact `burn3-capacity-state-*` evidence is included in this checkpoint;
no new recurrence theorem is needed.

Finite traces through one million steps split those 32 misses into 21 machines
with short runs in one state and 11 with longer excursions. A deeper history
search on the first group produced nine state proofs. Two repeated-word settings
on the second group produced none. Finite simulation guided the search; only the
replayed history certificates contribute to the proved totals. See the
[diagnostic notes](research/burn2-diagnostic.md) for parameters and replay.

## Continue the work

The existing candidate queue retains **3,252 instruction obligations**: 2,417
from the main repeated-word lane and 835 from timeout recovery. It contains
**no remaining state obligations**. The five capacity state holdouts are also
closed, so the **1,072 remaining state families** form one exact fresh-search
input. The next work is deeper history search on that set and continued
bounded replay of the instruction queue.

Remaining candidate certificates and remaining proof obligations are separate
ledgers. A successful discovery search moves a family into the replay queue;
only an exact, census-linked kernel proof removes its obligation.
