# Longer-history refinement: next1b

This package proves nonhalting and state quasihalting bound zero for **one
additional complete table**, using the unchanged
[historical-marker theorem](burn12-history-marker.md). Both states recur.

The exact table `1LB2LB3RA0RB_2RB2RA3LA2LA` uses history 18, width two,
and writer mask 3. Its graph has 1,599 contexts and 3,401 serialized edges.
It is the second cost-ordered singleton of two proposals selected by the
completed 39-family screen; the first singleton has its own audit.

[Independent validation](burn17-history-next-native.json) reconstructs the
actual 4,096-step augmented anchors, decodes and re-encodes complete cell
histories, and checks every visible history-write/shift update, marker edge,
global capacity and B-recurrence oracle. Both proposals are absent from 74
frozen prior audited inventories. This table's largest encoded cell is
81,136,293,886,064,517 (57 bits), below the extraction limit of 2^62.
The source screen's maximum history 19 is also universally safe: its largest
possible encoded cell is 658,812,288,346,769,699.
Coq reconstructs the graph from the compact tuple; native diagnostics grant
no proof credit.

Compilation took 250.376 seconds. Full recursive `coqchk` audited 276 modules
with zero reuse in 171.398 seconds. No new generic theorem, instruction bound,
or global BBB(2,4) upper bound is introduced.

After replaying the historical-marker generic package, run with Coq on `PATH`:

```sh
python3 four/tools/check_burn17_history_next_native.py --check
python3 four/tools/check_burn12_history_marker_batch.py --batch next1b --timeout 600 --audit-timeout 1800
```

The [selection](burn12-history-marker-next1b-selection.json),
[compact input](burn12-history-marker-next1b-proof-input.json),
[checked report](burn12-history-marker-next1b-checked.json), and
[exact inventory](burn12-history-marker-next1b-machines.json) freeze this batch.
The copied [source input](burn17-history-next-source-input.json),
[completed search](burn17-history-next-source-search.json), and
[prior inventory pins](burn17-history-next-prior-inventories.json) preserve
native provenance. Generated sources and kernel receipts remain under ignored
build storage.
