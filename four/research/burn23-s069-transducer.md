# S069: a crossing-parity invariant

Machine: `1LB2RA1LA1RB_2RB2LB3LB1RA`.

The proof establishes `NonHalt`, arbitrarily late visits to both states, and
`QHBound 0`. It makes no claim that every synthetic counter computation
terminates or that the finite main-cut return controls characterize the orbit.

Every right move writes 1 or 2, so the finite CTape left word remains over
`{1,2}`. No transition writes zero, so the right word contains no explicit zero.
Let `p` be the parity of the number of twos in the left word. The following
four-state transducer acts on `(machine state,p)` as it reads a symbol:

| symbol | A,0 | A,1 | B,0 | B,1 |
| --- | --- | --- | --- | --- |
| 0 | A,1 | A,0 | B,1 | B,0 |
| 1 | A,1 | A,0 | B,1 | A,1 |
| 2 | A,0 | A,1 | A,1 | B,1 |
| 3 | B,0 | B,1 | A,0 | A,1 |

Fold it across `head::right`, starting from the current state and left parity.
The predicted final **state** is invariant under every actual step and equals A
at the actual blank initial configuration. Coq proves the left-move equations
by exhaustive cases on the actual transition and the popped left symbol; right
moves and implicit blank padding preserve the same state directly. The
transducer is an algebraic invariant; its name does not assume that its
predicted crossing ever finishes.

At `B0` with empty right the prediction is B. Thus this permanent B drift is
excluded. The same argument excludes `A3` with empty right, whose next step
would enter that drift. From any B configuration satisfying the invariant,
finite induction on the left word reaches A: B1/B2 move left, B3 exits
immediately, and blank-left B1/B2 have finite local bounce proofs. An invariant
B0 configuration must have a nonempty nonzero right word, so one right step
reduces it to that finite-left case. Existing `ore_auto_goal` proves B recurs;
its theorem, the A-return induction, and the universal invariant give both-state
recurrence and `QHBound 0`.

The independent native checker validates all 20 left and 8 right algebra
cases, 122,936 finite one-step contexts (81,915 satisfy the invariant), 46,101
B-nonzero return controls, all admitted B0 controls in that context domain, and
4,096 actual blank-run steps. The longest finite return control is 14 steps.
Twelve negative controls include genuine blank B drift and unsafe boundary A3,
as well as the wrong B1/B2 parity and invalid left/right alphabets. These native
controls carry zero proof credit. Earlier bounded cut records remain in
`/tmp/s069-bounded-handoff.json` and `/tmp/s069-phase-parity.json`; the new
universal theorem does not depend on them.

The frozen proof input pins both source templates and the native selection
report. The native input pins a copied frontier source, avoiding a dependency
on the mutable current-holdouts file. `check_burn23_s069_transducer.py` creates
the exact-table wrapper, all-completions state board, and inventory, then runs a
fresh recursive `coqchk` including all 17 regression theorems. No instruction
bound, scoreboard update, publication, staging, or merge is part of this
package.
