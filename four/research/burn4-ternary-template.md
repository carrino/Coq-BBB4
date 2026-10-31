# Seven more ternary-counter families

This board adds seven instruction-family discharges beyond the original concrete
ternary counter. All seven were already state-covered. Its proved bounds are
state 0 and instruction 7; the instruction bound is a convenient common bound,
not a claim that every row has exact score 7.

The theorem imports the frozen counter's macro lemmas. It requires agreement on
exactly A0, A1, A2, A3, B1 and B2. An inductive sentinel invariant keeps B0 and B3
unreachable after counter entry, even when arbitrary symbols lie beyond the
sentinel. Finite executions therefore transfer from the original counter to each
new table. Positive block phases provide direct recurrence witnesses for all six
active instructions; no additional recurrence graph is needed.

The seven concrete entries are checked by Coq after 3 or 7 steps. The input keeps
finite-list trailing blanks exactly: the first table has dormant suffix `[0]`,
although the discovery screen trimmed that blank. Every future block return is
proved inductively with the original exact gap `3^(n+2)-2`. No long simulation is
used. Several tables leave B3 undefined; `NonHalt` and `extend_bounds` establish
the bounds for every completion of those partial tables.

`Board.small_sound`, `Board.was_pending`, and `Inventory.inventory_exact` tie the
proof to the seven distinct frozen-census rows. The generalized theorem uses
only the repository's existing functional-extensionality axiom.

From `four/`, after the core theory build:

```sh
python3 tools/check_burn4_ternary_counter.py --timeout 300 --audit-timeout 1200
python3 tools/check_burn4_ternary_template.py --timeout 300 --audit-timeout 1200
```

The first command supplies the frozen `Counter` and `Tail` dependency. The second
replays the template, concrete board and exact inventory, then recursively audits
the complete Coq dependency closure. It pins both handwritten theorem sources,
generated proof sources, input rows, replay tooling, and current proof objects.
A rerun keeps published reports and inventories unchanged and records a separate
current receipt. Discovery is reproducible with `screen_burn4_ternary_template.py`,
but is not trusted by the proof.
