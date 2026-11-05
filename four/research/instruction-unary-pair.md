# Two unary-counter instruction proofs

The same theorem covers the two B2 writes of the existing S004/S005
four-phase counter. All eight instructions fire beyond every time bound, so
both state and instruction upper bounds are zero. Neither machine attains an
instruction quasihalting score: no instruction has a last firing.

| Exact family ID | Program, first move right | Instruction upper bound |
| :-- | :-- | --: |
| `tr24-3376288745` | `1RB0RA1RB1LB_3LB3LA0LB2RA` | 0 |
| `tr24-3569389297` | `1RB0RA1RB1LB_3LB3LA2LB2RA` | 0 |

The original [phase proof](../proof-sources/burn23-s004-s005-unary/UnaryPhases.v)
is rebuilt unchanged. Its `pu_cycle` returns to the same boundary with two
additional blocks. The new
[`pu_instructions_recurrent`](../proof-sources/instruction-unary-pair/UnaryInstructions.v)
first reaches a nonempty block, then supplies a symbolic prefix witness for
each of the eight instructions. This works for every block count and both B2
writes, rather than inspecting a finite sample of the blank trajectory.

The [board](../proof-sources/instruction-unary-pair/Board.v) proves each exact
table's original bootstrap membership and both bounds for every completion.
The replay generates a Coq inventory and checks it against the two recorded
machine IDs. The regression module also proves that neither table has any
instruction attainment.

With Coq on `PATH`, run from the repository root:

```sh
python3 four/tools/check_instruction_unary_pair.py
```

The recorded run recursively checked 267 modules with stock `coqchk`, including
the old and new regressions, with zero skipped or reused modules. Its only
assumption is the existing functional-extensionality axiom. Current replay logs
and receipts go under `four/build/instruction-unary-pair/`; tracked proof reports
and source pins remain frozen.
