# Longer-history refinement: next1a

This package proves nonhalting and state quasihalting bound zero for **one
additional complete table**, using the unchanged
[historical-marker theorem](burn12-history-marker.md). Both states recur.

The exact table `1LB2LA1RB0RA_2RB1RA3LA3RB` uses history 19, width two,
and writer mask 3. Its graph has 322 contexts and 459 serialized edges.
It is the first cost-ordered singleton of two proposals selected by the
completed 39-family screen; the second singleton receives separate proof credit.

[Independent validation](burn17-history-next-native.json) reconstructs the
actual 4,096-step augmented anchors, decodes and re-encodes complete cell
histories, and checks every visible history-write/shift update, marker edge,
global capacity and B-recurrence oracle. Both proposals are absent from 74
frozen prior audited inventories. This table's largest encoded cell is
653,205,144,799,142,346 (60 bits). The largest possible encoded cell at history
19 is 658,812,288,346,769,699, below the extraction limit of 2^62.
Coq reconstructs the graph from the compact tuple; native diagnostics grant
no proof credit.

Compilation took 43.239 seconds. Full recursive `coqchk` audited 276 modules
with zero reuse in 65.610 seconds. No new generic theorem, instruction bound,
or global BBB(2,4) upper bound is introduced.

After replaying the historical-marker generic package, run with Coq on `PATH`:

```sh
python3 four/tools/check_burn17_history_next_native.py --check
python3 four/tools/check_burn12_history_marker_batch.py --batch next1a --timeout 600 --audit-timeout 1800
```

The [selection](burn12-history-marker-next1a-selection.json),
[compact input](burn12-history-marker-next1a-proof-input.json),
[checked report](burn12-history-marker-next1a-checked.json), and
[exact inventory](burn12-history-marker-next1a-machines.json) freeze this batch.
The copied [source input](burn17-history-next-source-input.json),
[completed search](burn17-history-next-source-search.json), and
[prior inventory pins](burn17-history-next-prior-inventories.json) preserve
native provenance. Generated sources and kernel receipts remain under ignored
build storage.
