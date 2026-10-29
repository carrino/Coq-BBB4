# S004/S005: four-phase unary counter

The two complete machines are
`1LB0LA1LB1RB_3RB3RA0RB2LA` (S004) and
`1LB0LA1LB1RB_3RB3RA2RB2LA` (S005). One Boolean parameter selects B2's
write, 0 or 2. The unconditional theorem `pu_sound` proves `NonHalt` and
`QHBound 0` for both values.

The former reachable-marker obligation in
`burn18-s004-s005-obligation.md` is bypassed by a narrower closed cut grammar.
The old obligation, conditional exploratory proof, and accepted packages are
unchanged.

At a cut the machine is B on a blank cell, with an empty finite left word and
right word `1 P^n T`. Here `P = 021002121`; `T` has four phases:

| Input T | Output T | Output n | Steps |
| --- | --- | --- | --- |
| empty | 02121 | n | 58n + 22 |
| 02121 | 02102121 | n | 58n + 30 |
| 02102121 | 0210021002121 | n | 58n + 70 |
| 0210021002121 | empty | n + 2 | 58n + 106 |

These are universal Coq theorems for every natural `n` and both B2 writes.
Combining them gives `pu_cycle`: a positive `232n + 228` steps returns to the
same blank-left cut with two more P blocks. The blank run enters the n=0,
empty-T cut after one step. Each cut has an A visit after two steps, so the
positive cycles provide arbitrarily late visits to both states.

The proof separates a 41-step forward transport of one P block from a 17-step
backward transport. The forward sweep retains top-left `33` and inserts
`Q = 1x3131x31` underneath, where x is the B2 write. The backward sweep
retains top-left `31`, consumes Q, and emits the rotated block `R = 002121021`
on the right. Its head is x: S004 uses A0 and S005 uses A2, whose transitions
are identical. Fixed terminal finishers take 16, 24, 64, or 100 steps with an
arbitrary untouched left context. A list-rotation identity restores P after
the backward sweep. All these statements compile with arbitrary contexts;
the grammar and timing are not extrapolations from finite traces.

Independent native verification checks 1,764 context-parametric sweep cases,
168 terminal cases, 136 phase cases and 34 full cycles for block counts 0..16.
It also confirms identical state/position trajectories for 8,192 actual blank
steps. Twelve negative controls include the unsafe broad-grammar words `121`
and `1212121`, genuine permanent blank-B tails, and an incorrect block-count
claim. Native controls carry zero proof credit.

The frozen native input pins a copied current-frontier list. The proof input
pins the native selection and both proof templates. The replay tool creates
two exact-table wrappers, the all-completions state board and inventory, and
runs a fresh recursive `coqchk` including all 16 regression theorems. There is
no instruction claim and no scoreboard, publication, staging, or merge change.

The unaccepted author revision was re-frozen after peer review found a native
metadata comparison bug: `terminal_phases` used a Python tuple while JSON
reloads it as a list. The checker now explicitly stores `list(TAILS)`, and
`--check` passes. All parsed control data and universal proof templates are
unchanged. The former audit report SHA
`733ce374bc934f8792ec7ab809c5366c79cc13ed39b16d4a6c31e8a4439b86fd`
is obsolete; that complete revision is preserved under the ignored build
folder `revision1-tuple-metadata`. The replacement report has a fresh recursive
audit and updated provenance pins.
