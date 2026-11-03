# Generalizing the instruction counter proofs

The second instruction worker wave closes **22 more exact families**: **14**
through shared symbolic counter proofs and **8** through closure certificates
found among nearby tables. The historical hard-cohort worklist falls from
**28,614 to 28,592**, with **61** recorded instruction proofs in total. The
global instruction maximum is still open.

| Shared proof | New families | Instruction result | Proved statement |
| :-- | --: | :-- | :-- |
| Two B2 writes of one four-phase unary counter | 2 | All eight instructions recur; upper bound 0 | [`pu_instructions_recurrent`](proof-sources/instruction-unary-pair/UnaryInstructions.v) |
| Counter with arbitrary persistent tape context and B0 write | 4 | Exact score 2 | [`rb_instruction_attains`, `rb_instruction_bound`](proof-sources/instruction-counter-context/CounterEntry.v) |
| Boundary counter with an arbitrary transient B2 slot | 5 | Upper bound 64 | [`entry_instruction_bound`](proof-sources/instruction-boundary-counter/BoundaryKernel.v) and [five registrations](proof-sources/instruction-boundary-counter/Cases.v) |
| Counter reached after state/symbol relabeling and reflection | 1 | Exact score 1 | [`instruction_attains`, `instruction_bound`](proof-sources/instruction-counter-conjugate/ConjugateCounter.v) |
| Counter with a different permanent sentinel, and its relabeling | 2 | Exact scores 2 and 1 | [direct proof](proof-sources/instruction-counter-three/ThreeEntry.v), [transported proof](proof-sources/instruction-counter-three/ConjugateThree.v) |
| Nearby tables accepted by existing closure checkers | 8 | Upper bound 65,536 | [exact family list and replay](research/instruction-burn4.md) |

All fourteen symbolic cases have state upper bound zero. An upper bound of
zero for a machine whose instructions all recur does not assert attainment:
there is no last firing. The exact scores above separately prove a last firing
and a matching upper bound.

## What is reusable

The counter proofs establish a symbolic return between tape boundaries for
every counter size. Increasing gaps are handled algebraically. For example,
the boundary counter returns after `16 * 2^m` steps. Its proof never needs to
simulate those gaps at large values of `m`.

The persistent-context proof quantifies over tape cells behind a permanent
sentinel. A short prefix may leave a different write symbol there without
changing the later counter. One theorem therefore covers four different B0
writes. A separate sentinel generalization covers two further tables.

The erased-slot argument handles a transient instruction: delete that slot in
an auxiliary machine and prove that the auxiliary suffix runs indefinitely
from the actual prefix's endpoint. It follows that the real suffix cannot
fire the deleted slot. These auxiliary machines can halt from blank, so a
blank-start nonhalting premise would be incorrect. Regressions check that
distinction explicitly.

The relabeling argument transports runs at arbitrary configurations. Swapping
states changes the initial state, so blank-start equivalence alone would not
justify reuse. Each transported case checks its own actual blank prefix before
entering the transformed symbolic counter.

Exact family IDs remain distinct throughout. Parameterization and relabeling
share proof work; every newly closed table still has its own kernel-checked
bootstrap membership, all-completion bound and inventory entry.

## Replay and remaining work

With Coq on `PATH`, from the repository root:

```sh
python3 four/tools/replay_instruction_proofs.py --list
python3 four/tools/replay_instruction_proofs.py --jobs 2
python3 four/tools/report_instruction_burndown.py --check
python3 four/tools/instruction_worklist.py
```

Each package rebuilds its sources and invokes full recursive stock `coqchk`.
Previously published proof sources and reports remain unchanged. The only
assumption is the existing dependent functional-extensionality axiom.

The nearby-table search tried **172 recipes on 62 tables** with a one-second
budget per attempt. All eight candidates were replayed in Coq. Rejections and
timeouts remain visible in the worklist's neighbor-search ledger and receive
no proof credit. These searches selected related tables; their success rate is
not an estimate for the whole remaining inventory.

Next, look for other state-proof macros with recurring boundaries, identify
which instruction slots those macros avoid, and separate the actual finite
entry from the infinite suffix. The remaining global work also includes
assembling the complete instruction census into a universal upper-bound
theorem, then pairing it with the champion's lower bound.
