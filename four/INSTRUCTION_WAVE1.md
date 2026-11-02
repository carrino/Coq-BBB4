# First instruction worker wave

Five workers produced **24 new instruction proofs**, reducing the historical
hard-cohort inventory from **28,638 to 28,614**. They add no state coverage to
the completed state result. Every accepted family has an all-completion bound,
original bootstrap membership, an exact Coq inventory and a full recursive
kernel audit. Existing proof sources and frozen reports remain unchanged.

| Package | New instruction families | Bound | Recursive audit |
| :-- | --: | --: | :-- |
| First disjoint search packets | 6 | 65,536 | 274 modules, zero reuse |
| Additional 75-family pilot | 15 | 65,536 | 283 modules, zero reuse |
| S030 finite tail | 1 | Exact score 1,367,361,263,049 | 271 modules, zero reuse |
| Sparse boundary counter | 1 | Upper bound 0 | 268 modules, zero reuse |
| Counter with transient B0 | 1 | Exact instruction score 2 | 262 modules, zero reuse |

These audits skip no dependencies. Assumptions are limited to the existing
functional-extensionality axiom. An independent worker reviewed the table
identities, completion scope, inventories, sources, objects and audit receipts.

## Symbolic proofs

For S030, displayed with the first move right as
`1RB2RA1RA2RB_2LB3LA0RB0RA`, the last state occurrence and last instruction
occurrence differ:

| Quantity | Exact score, last index plus one |
| :-- | --: |
| State quasihalting | 1,367,354,345,129 |
| Instruction quasihalting | **1,367,361,263,049** |

The existing state proof reaches a symbolic binary tape. Two bounce macros
then prove the final B2 firing at index 1,367,361,263,048 and permanent B0
drift afterwards. Replay never simulates the trillion-step prefix. See the
[new instruction theorem](proof-sources/instruction-s030/InstructionTail.v)
and [case note](research/instruction-s030.md). This is an individual-machine
result, not a global instruction maximum theorem.

For `1RB2RB3LA3RB_1LB1RA3LA1LA`, an exact boundary-counter macro gives returns
to A0 beyond every finite horizon. Prefix witnesses between returns establish
recurrence of **all eight instructions**. Consequently no instruction has a
last firing: zero is an upper bound, with no attainment claim. The
[universal counter proof](proof-sources/instruction-sparse-return/BoundaryCounter.v)
uses no native graph or finite trace as a premise. See its
[case note](research/instruction-sparse-return.md).

For `1RB2RB3RB2LA_1LA3LA2RB1LA`, both states recur indefinitely but B0 fires
only at index 1. The [second counter proof](proof-sources/instruction-sparse-twos/TwosCounter.v)
therefore establishes state bound zero and exact instruction score **2**.
It deletes B0 in an auxiliary machine only for the suffix after the actual
two-step prefix. The erased machine halts from blank input; a regression checks
this distinction. Infinite execution of its counter suffix rules out later B0,
while the other seven instructions recur. See the
[case note](research/instruction-sparse-twos.md).

## Search accounting

The workers performed **551 bounded attempts on 181 distinct tables**:
21 native candidates, 275 rejections and 255 timeouts. All 21 candidates
subsequently passed Coq replay; the three symbolic proofs are separate.

The [canonical search ledger](research/instruction-wave1-search-ledger.json)
retains exact recipes, per-row budgets, outcomes and timings, with hashes of
the frozen producer reports. These observations route future work and earn
no proof credit by themselves. The
[wave summary](research/instruction-wave1-summary.json) retains completed
worker assignments, including the 160 unresolved families released for more
work. Claims are cleared when that work packet ends; recorded evidence stays
attached to the family IDs.

## Replay

With Coq on `PATH`, replay every accepted instruction batch from tracked
sources:

```sh
python3 four/tools/replay_instruction_proofs.py --list
python3 four/tools/replay_instruction_proofs.py --jobs 2
python3 four/tools/report_instruction_burndown.py --check
python3 four/tools/instruction_worklist.py
```

The replay command builds the complete shared dependency closure and runs
the registered proof drivers sequentially. Each driver performs a fresh full
recursive audit. For one package, use for example
`--only instruction-burn3`. Generated objects, receipts and logs remain under
`four/build/`; GitHub Actions replays every registered package.

The [accepted registry](research/instruction-accepted-batches.json) pins the
proof reports used for the current ledger. Each new proof inventory must be
distinct from the families already accepted. The global instruction census
assembly and maximum theorem remain open.
