# Instruction targets left by the capacity refinement

The capacity refinement left 41 instruction obligations. Unioning every saved
graph, width, orientation and capacity witness still leaves exactly one
uncovered instruction per family. Combining the existing witnesses therefore
cannot complete these instruction proofs by itself.

The [finite diagnostic report](burn3-capacity-instruction-diagnostics.json)
records each missing target, all per-graph witness flags, and exact simulation
observations through 4,096, 65,536 and 1,000,000 steps. The observations divide
the 41 cases into three useful search groups:

| Observation about the uncovered instruction | Families | Next approach |
| --- | ---: | --- |
| Observed after 65,536 steps, with at most 1,000 total firings | 36 | Counter or phase-return invariants; use saved traces to propose macro certificates |
| More than 1,000 firings within the finite budget | 3 | Refine local history or repeated-word abstractions |
| Last observed before the 4,096-step anchor | 2 | Strengthen the tail invariant to exclude the instruction |

These are finite observations. None establishes permanent extinction,
recurrence, or a quasihalting bound. In particular, many sparse-target machines
have very large gaps between firings; absence from a short simulation is weak
evidence of an eventual last firing.

## Two additional instruction proofs

A bounded pilot tried six existing history/repeated-word configurations on
the two early-last-observation cases and three frequent-target cases. History
width 4, history depth 3, anchor 4,096, fuel 16,384 and 32 growth rounds yielded
two candidates:

| Family | Previously missing target | Finite observation |
| --- | --- | --- |
| `1LB2RB1RA1RB_2RA3LB2LB0LA` | A0 | Last observed at configuration step 14 |
| `1LB2RB2RB2LA_3RA0LA0RB3LB` | A2 | Frequently observed |

Both passed the existing `AdvancedPipeline` history checker in instruction
mode, all-completion bounds, original census pending membership, exact board
inventory, and a full recursive kernel audit of 270 modules. Each now has both
bounds at 4,096. Relative to the previous checked inventories, the increment is
**two instruction obligations and zero state obligations**; their state bounds
were already known. This leaves 39 instruction obligations from this lane.

The accepted proofs use no new theorem. Generated Coq stays under ignored
`build/` paths. Replay after `make -C four all`, from the repository root:

```bash
python3 four/tools/check_burn3_capacity_instructions.py \
  --timeout 300 --audit-timeout 1200
```

The [checked report](burn3-capacity-instruction-checked.json) contains the board
descriptor, exact inventory, consumed source/input hashes and kernel receipt.
Replay preserves that report and records current execution evidence under
`build/burn3-capacity-instruction/proof/`.

## Remaining blockers

The other early-last-observation family,
`1LB2LA1RB3RB_3RA1RB3LA1RA`, last fired B1 at configuration step 9 in the finite
trace, but every tested abstraction still fails its instruction obligation.
It is a concrete target for a stronger tail invariant that rules out B1.

The two remaining frequent-target cases are
`1LB2RA2LA0LB_0RB3RA3RB1LA` (A2) and
`1LB2RA3RA0RA_1RA2LA0LB3LA` (B3). Both resisted all six pilot settings despite
many finite firings. Their saved target graphs should guide a more precise
abstraction or phase invariant.

The 36 sparse-target cases should be approached through their return phases.
For example, the observed final seven gaps for
`1LB2LB3LB2RA_3RA1RA1LB1RB` are
727, 2,185, 6,559, 19,681, 59,047, 177,145 and 531,439, fitting
`next_gap = 3 * gap + 4` on those observations. Such fits can guide certificate
discovery but are not proofs and are not used by the accepted checker.
