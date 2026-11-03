# Persistent-context counter instruction proofs

One uniform symbolic proof closes these four exact historical instruction holdouts:

| Family | Canonical machine | State upper bound | Exact instruction score |
| --- | --- | ---: | ---: |
| `tr24-2699451765` | `1LB2LB3LB2RA_0RB3RA2LB1RA` | 0 | 2 |
| `tr24-2699785849` | `1LB2LB3LB2RA_1RB3RA2LB1RA` | 0 | 2 |
| `tr24-2700119933` | `1LB2LB3LB2RA_2RB3RA2LB1RA` | 0 | 2 |
| `tr24-2700454017` | `1LB2LB3LB2RA_3RB3RA2LB1RA` | 0 | 2 |

Each machine fires B0 for the last time at configuration index 1. After five
steps, its tape has the symbolic counter's permanent left sentinel, with the
B0 write symbol preserved behind that sentinel. The counter never reads this
older context. All seven other instructions recur arbitrarily late.

`ContextCounter.v` extends the unchanged earlier `TwosCounter.v` block macro to
preserve an arbitrary finite left context. `CounterEntry.v` proves that any
finite entry into this suffix inherits the recurrence and transient-instruction
bounds, then handles all four right-moving B0 choices with one quantified
write-symbol theorem. The blank-start behavior of the B0-erased auxiliary
machine is checked separately from its infinite suffix.

With Coq on `PATH`, replay the package after building its shared theory
prerequisites:

```sh
python3 four/tools/instruction_core_targets.py --build --jobs 2
python3 four/tools/check_instruction_counter_context.py
```

The generated board proves the bounds for every completion of each exact table,
checks original bootstrap membership and proves the precise four-row inventory.
Every replay runs full recursive stock `coqchk`, including the regressions. The
only assumption is the existing dependent functional-extensionality axiom.
This is a local census contribution; it does not prove a global instruction
maximum.
