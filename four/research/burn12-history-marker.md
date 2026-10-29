# Historical-cell markers: first four state proofs

This package proves **four new state bounds of zero**: three complete machine
tables and one partial census family. It also establishes the generic theorem
for preserving a right-side marker determined by the instruction that most
recently wrote a tape cell.

A marker mask selects among the eight `(state, read symbol)` writer labels.
A written zero can be marked. An untouched blank, whose history is empty, is
always unmarked. The invariant is required during state-B episodes and is
carried by the actual augmented tape configuration. Every closed-graph edge
must either enter A, expose a marked cell in the next head/right window, or
leave an unmarked head during B so that a farther marker survives.

The proof preserves this invariant on the same augmented execution, pads its
left side with untouched blanks, and projects the existing capacity measure
onto the ordinary tape. The decreasing measure forces a return to A. Closedness
proves nonhalting, and conditional one-state reachability proves B recurrence.
Both states therefore recur, yielding a state bound of zero. The partial-table
case uses the same theorem without a global totality assumption.

| Machine | Last-writer mask | Table |
| --- | ---: | --- |
| `1LB2LB0LA1RB_3RB1LA3LB2RA` | 36 | Complete |
| `1LB0RB1RA3LA_2RB3LB0LB2LA` | 97 | Complete |
| `1LB2RB3LB2RA_3RB3LA0LB1LA` | 64 | Complete |
| `1LB0RA---0LB_1RB2RA3LB1LB` | 9 | Partial |

The exact inventory wrappers prove all-completion state bounds and original
census pending membership. This package makes no instruction-bound claim.

The native screen found 178 complete-table proposals; this pilot proves three
of them and one separately selected partial family. Every other proposal still
requires its own Coq replay. The first full audit checked 280 modules with
zero reuse, including nine regressions for blank/history boundaries and marker
preservation. Compilation took 27.145 seconds and the audit took
45.785 seconds. Only the existing functional-extensionality assumption appears.

Build the existing four-symbol core theories, then run from the repository root
with Coq on `PATH`:

```sh
python3 four/tools/check_burn12_history_marker.py --timeout 300 --audit-timeout 1800
```

The [compact input](burn12-history-marker-input.json),
[selection](burn12-history-marker-selection.json),
[checked report](burn12-history-marker-checked.json), and
[exact inventory](burn12-history-marker-machines.json) are portable.
The handwritten [theorem](../proof-sources/burn12-history-marker/HistoryMarker.v)
and [regressions](../proof-sources/burn12-history-marker/Regression.v) are kept
separate from the core. Coq reconstructs all candidate graphs; native graph
exports are unnecessary for replay. Generated sources and current receipts
remain under the ignored build directory.
