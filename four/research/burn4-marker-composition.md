# One complementary marker/history witness

`1LB1LA2RA3RB_2RB3RA0LB0LA` needs two different recurrence arguments. The
relaxed-marker conditions prove arbitrarily late A visits with marker set `{1}`
and symbol weights `(0,0,1,0)`. Its uniform `ore_auto_goal` B test fails.
A history graph with width 3, history 5, anchor 4096, exploration fuel 16384
and 32 growth rounds passes the B rank check but rejects the A rank check.
The composed theorem proves both states recur, giving state quasihalting bound
0. This package makes no instruction claim.

`mh_history_target_recur` uses the existing `Closure.closure_invariant` and
`Closure.rank_find` lemmas. The history checker verifies the simulated anchor,
seed, closed graph, seed membership and the requested target's rank. Starting
from that anchor, closure gives a covered configuration after any additional
N steps; the rank then reaches the target at an index at least `anchor + N`.
No prefix last-visit gate is needed for this unbounded recurrence result.
The marker side reuses `rmp_inv_steps` and `rmp_reaches_A` from the frozen
relaxed-marker package. Combining these separate A and B conclusions yields
state bound 0; totality supplies nonhalting and the census theorem covers every
completion of the exact family.

The nine concrete Coq examples include both positive obligations and negative
controls for uniform B reachability, the old combined marker checker, the A
history rank, a wrong marker set, insufficient capacity, zero width and empty
exploration. No core theory or earlier template is changed.

Replay requires the frozen `burn3-relaxed-marker` package first. From the
repository root, with the Coq 8.18 toolchain available:

```sh
python3 four/tools/check_burn3_relaxed_marker.py --timeout 300 --audit-timeout 1200
python3 four/tools/check_burn4_marker_composition.py --timeout 300 --audit-timeout 1200
```

The second command copies three frozen handwritten templates into
`build/burn4-marker-composition/proof`, generates an exact inventory wrapper,
compiles all four modules and recursively audits their complete dependency
closure. It reads the prior marker package without modifying it. Published
reports are immutable, all input/source pins are rechecked after audit, and
repeat audits produce fresh receipts.

The descriptor module is `BBB24Burn4MarkerComposition.Inventory`. The input,
selection and checked report use the `research/burn4-marker-composition-` prefix.
The selected ID lies in the 545-family residual after the 121 entry-marker and
one history-refinement discharges. This separate next-wave package is outside
the 30-board checkpoint. Concurrent later batches must be deduplicated by ID.

The published replay freshly audited all 276 dependency modules with
zero reuse in 90.648 seconds. Its exact contribution is one state family
and zero instruction families. Only existing functional extensionality appears
in the assumptions.
