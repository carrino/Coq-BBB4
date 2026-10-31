# Six counter families entered with exchanged states

This board adds six instruction-family discharges beyond the original ternary
counter and its seven direct templates. All six were already state-covered. The
proved common bounds are state 0 and instruction 8; 8 is an upper bound rather
than a claim about each family's exact score.

State exchange does not preserve the blank-start run. Instead, each table is
first normalized by a blank-preserving symbol permutation and reflection. Coq
checks its actual A-start prefix, taking 1, 4 or 8 steps, into a counter phase in
state B. Only the suffix is transported using `swap_stepn` and the six-transition
agreement theorem from `burn4-ternary-template`. The original ternary macro gives
unbounded returns, six recurrent instructions and two excluded instructions.
Existing symbol/reflection transport then gives the bounds for the original
machine. Undefined table entries are covered for every completion by
`NonHalt` and `extend_bounds`.

From `four/`, after the core theory build:

```sh
python3 tools/check_burn4_ternary_counter.py --timeout 300 --audit-timeout 1200
python3 tools/check_burn4_ternary_template.py --timeout 300 --audit-timeout 1200
python3 tools/check_burn4_ternary_swapped.py --timeout 300 --audit-timeout 1200
```

The final command replays the swapped-entry theorem, concrete board and exact
inventory, then recursively audits the complete dependency closure. The board
also proves each partial table was in the frozen pending census. Every input,
handwritten and generated dependency source, replay tool and current object is
pinned. Reruns preserve published reports and inventories.

The discovery screen separately considers state exchange, six blank-preserving
symbol permutations and reflection. It found these six entries after only 25
simulated steps total. The proof checks its own entries independently and keeps
trailing finite-list blanks exactly, including dormant suffix `[0]` in the first
row. The screen is diagnostic evidence, not a proof premise.
