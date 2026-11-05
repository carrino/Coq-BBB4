# Three-sentinel counter instruction proofs

The alternate permanent sentinel closes two more exact historical holdouts:

| Family | Canonical machine | State upper bound | Exact instruction score |
| --- | --- | ---: | ---: |
| `tr24-2700370496` | `1LB2LB3LB2RA_3RA3RA2LB1RA` | 0 | 2 |
| `tr24-4437624636` | `1LB2LB1LB3RA_1RA3RA3LB2RA` | 0 | 1 |

Both machines reach the same symbolic counter with a permanent S3 sentinel.
The direct machine enters after two steps; its B0 instruction fires for the last
time at configuration index 1. The second machine enters a reflected and renamed
version after three steps; its A0 instruction fires for the last time at index 0.
The other seven instructions recur arbitrarily late in each case.

`ThreeCounter.v` proves the new block and phase macros, retaining an arbitrary
finite tape context behind the sentinel. A positive block restores the S3
sentinel; a zero block changes it, so the proof and regression keep those cases
separate. `ThreeEntry.v` transports a finite prefix into the infinite symbolic
suffix. `ConjugateThree.v` proves the state, symbol and reflection transport
from arbitrary configurations, then checks the second machine's actual prefix.
No auxiliary machine is assumed to run forever from blank.

With Coq on `PATH`, replay after building shared theory prerequisites:

```sh
python3 four/tools/instruction_core_targets.py --build --jobs 2
python3 four/tools/check_instruction_counter_three.py
```

The portable driver reconstructs the unchanged earlier `TwosCounter.v`, compiles
all new sources and runs full recursive stock `coqchk` including regressions.
The board registers common bounds (state 0, instruction 2), covers every
completion, checks original bootstrap membership and proves the exact two-row
inventory. Separate theorems establish each exact instruction score and reject
the smaller bound. The only assumption is the existing dependent
functional-extensionality axiom. These are local census contributions, not a
global instruction maximum theorem.
