# Closed-graph history refinement: closed3

This package proves nonhalting and state quasihalting bound zero for **3
additional complete tables**, using the unchanged
[historical-marker theorem](burn12-history-marker.md). Both states recur.

It is the exact sorted slice `[20, 23]` of 23 independently validated
proposals from a completed 55-family native screen. Candidates are ordered by
graph size, history length, window width and machine. This batch has
1,817–1,979 contexts per graph; all use width two. The other two
slices are separate packages, so each receives credit only after its own audit.

Independent validation reconstructs every actual 4,096-step augmented anchor,
decodes and re-encodes complete cell histories, and checks every visible
history-write/shift update and marker edge. Across the full 23-candidate source,
all 37,296 edges pass; the largest encoded cell uses 51 bits. Coq reconstructs
the graphs from compact tuples and does not consume serialized native nodes.
The native diagnostic grants no proof credit.

Compilation took 169.698 seconds. Full recursive
`coqchk` audited 278 modules with zero reuse in
122.701 seconds. No new generic theorem, instruction bound or
global BBB(2,4) upper bound is introduced.

After replaying the historical-marker generic package, run with Coq on `PATH`:

```sh
python3 four/tools/check_burn12_history_marker_batch.py --batch closed3 --timeout 600 --audit-timeout 1800
```

The [selection](burn12-history-marker-closed3-selection.json), [compact input](burn12-history-marker-closed3-proof-input.json),
[checked report](burn12-history-marker-closed3-checked.json), and [exact inventory](burn12-history-marker-closed3-machines.json)
freeze this batch. Copied source diagnostics preserve native provenance.
Generated sources and kernel receipts remain under ignored build storage.
