# Instruction neighbor closure batch

Eight neighbors of the symbolic counter and S030 instruction-tail machines pass the existing instruction closure checker at a common conservative bound of **65,536**. These are instruction upper bounds, with no claim of exact score or attainment.

| Family ID | Program (first move right) | Certificate |
| :-- | :-- | :-- |
| `tr24-2516595107` | `1RB2RB3LA1RA_1LB1RA0LA1LA` | hist width 3, history 5 |
| `tr24-3216579695` | `1RB2RB3LA0LB_1LB1RA3LA1LB` | hist width 3, history 5 |
| `tr24-69117432` | `1RB2LB1RA2RB_2LB3LA0LA0RA` | hist width 3, history 5 |
| `tr24-2516600020` | `1RB2RB3LA1RB_1LB1RA0LA1LA` | hist width 3, history 5 |
| `tr24-4969043888` | `1RB2RA1RA2RB_2LB3LA0RB3RA` | finite width 5 |
| `tr24-2516590194` | `1RB2RB3LA0LB_1LB1RA0LA1LA` | hist width 3, history 5 |
| `tr24-5268268147` | `1RB2RB3LA0LA_1LB1RA3LA3RA` | finite width 5 |
| `tr24-382906356` | `1RB2RA1LA2RB_2LB3LA3LB0RA` | hist width 3, history 5 |

The native search tried 172 bounded recipes on 62 exact historical holdout tables: six history certificates and two finite certificates succeeded. Native candidates and failed or timed-out attempts have no proof credit. The frozen search report preserves all outcomes.

Replay from the repository root, with Coq on `PATH`:

```sh
python3 four/tools/check_instruction_closure.py --name instruction-burn4
```

The batch passed a full recursive stock `coqchk` audit: **276 modules checked**, zero skipped or reused modules, in 93.221 seconds. The printed assumptions contain only the existing functional-extensionality axiom.

The unchanged closure replayer reconstructs the eight case proofs, all-completion bounds, original bootstrap membership and exact Coq inventory. The instruction burndown registry accounts for each exact family only once. Its global count supersedes the replayer's count relative to the original 28,653-row baseline.

The global instruction maximum theorem remains open.
