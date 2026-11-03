# Generic boundary counter with a transient B2 instruction

Five tables from the frozen historical instruction holdout inventory share a
symbolic counter after a short, separately checked prefix:

| Exact family | Program (first move right) | Prefix steps | Counter parameter |
| --- | --- | ---: | ---: |
| `tr24-2541110977` | `1RB2RB3LA3RB_2LB1RA0LB1LA` | 40 | 1 |
| `tr24-2565248546` | `1RB2RB3LA3RB_2LB1RA1RA1LA` | 44 | 1 |
| `tr24-2589386115` | `1RB2RB3LA3RB_2LB1RA1RB1LA` | 36 | 1 |
| `tr24-2758349098` | `1RB2RB3LA3RB_2LB1RA3RA1LA` | 19 | 0 |
| `tr24-2806624236` | `1RB2RB3LA3RB_2LB1RA3LA1LA` | 64 | 1 |

Every table has state bound **0** and instruction bound **64**. These are upper
bounds; this packet does not claim that 64 is attained. The global instruction
maximum remains open.

`BoundaryKernel.v` generalizes the word-scanning and block-consumption argument
from the previously proved sparse boundary counter. Its B2 transition is an
arbitrary `option Trans`. With B0 set to `2RB`, the recurrent boundary has state
A, a blank under the head, a blank left half-tape, and the word
`(12)^m 1312` immediately to the right. The generic macro proves

```text
main(m) --[work(m) + 4]--> main(m + 1)
work(m) + 4 = 16 * 2^m
```

This avoids simulating the exponentially growing gaps. Seven instructions recur
arbitrarily late. For B2, the proof compares the actual suffix with the same
counter having B2 deleted. That auxiliary machine survives from every recurrent
boundary, so the actual suffix cannot fire B2. It **halts from blank**; the
proof uses it only after the actual checked prefix. A regression verifies this
distinction.

`Cases.v` checks the five finite prefix entries, proves the common bounds and
lifts them to every completion with `extend_bounds`. Original bootstrap
membership is checked in Coq. The generated `Inventory.v` checks that the exact
five packed17 tables equal this board. Every replay invokes full recursive stock
`coqchk`, including negative controls and the symbolic macros.

With Coq on `PATH`:

```sh
python3 four/tools/instruction_core_targets.py --build --jobs 2
python3 four/tools/check_instruction_boundary_counter.py
```

The only printed assumption is the existing dependent functional-extensionality
axiom. Native traces and nearby-table searches are discovery evidence only.
