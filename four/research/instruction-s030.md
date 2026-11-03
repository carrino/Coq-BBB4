# S030: exact instruction score after the finite binary suffix

The family `1LB2LA1LA2LB_2RB3RA0LB0LA` (`tr24-44979812`) has exact instruction
quasihalting score **1,367,361,263,049**. Its last `B2` occurrence is at
configuration index **1,367,361,263,048**, under the repository's index-plus-one
convention. From the next configuration onward only `B0` fires.

In first-move-right form, the same machine is
`1RB2RA1RA2RB_2LB3LA0RB0RA`. The regression module proves the reflected table
and transports both attainment and the exact instruction upper bound through
the existing mirror theorem.

## Proof

The unchanged state proof supplies an exact symbolic configuration after
1,367,354,345,129 steps: state B at the back of a block of `a = 1,383,582`
twos, with two further twos on the right. Its finite state computation was
already proved by the source-pinned macros; this package does not simulate
that enormous prefix.

The new proof composes three existing universal sweeps:

1. `a` leftward `B2` steps erase the initial block.
2. A bounce across the first right-hand two takes `2a + 3` steps.
3. A bounce across the final two takes `2(a + 2) + 3` steps.

After **5a + 10 = 6,917,920** additional steps, the whole represented tape is
blank, the head reads zero, and the state is B. An induction over the blank
right suffix proves `B0` at every subsequent time. Determinism therefore
bounds the last occurrence of every instruction by the escape time.

A second universal macro stops one step earlier, at `B2`, proving attainment
of the same score. Binary `N` counts remain symbolic throughout the large
prefix and are converted through the original opaque count interface.

The [instruction theorem](../proof-sources/instruction-s030/InstructionTail.v)
exports `s30_instruction_exact`. The
[board](../proof-sources/instruction-s030/Board.v) proves every completion
satisfies both bounds at the conservative common value **2^41** and at the
champion score. The [inventory](../proof-sources/instruction-s030/Inventory.v)
proves the exact singleton table and original census membership. This supplies
one new instruction family and no new state coverage; it is not a global
instruction maximum theorem.

## Validation and replay

All five original state modules and the unchanged generic instruction-tail
helper were reconstructed from their accepted source pins. The four new
modules and ten new regression controls compiled. Full recursive stock
`coqchk` checked **271 modules**, with **zero reused/skipped modules**, in
42.728 seconds. Both the original and new regression modules are included.
The exact theorem and board theorem report only the existing
`FunctionalExtensionality.functional_extensionality_dep` assumption.

With Coq 8.18 on `PATH`, run from the repository root:

```sh
python3 four/tools/instruction_core_targets.py --build --jobs 2
python3 four/tools/check_instruction_s030.py --timeout 180 --audit-timeout 1800
```

Replay requires tracked source files, not native traces or old generated proof
objects. It uses one compilation worker, a 3 GiB address-space limit and a
64 MiB stack. It preserves the published report and writes current sources,
objects, assumption output and audit receipts under
`four/build/instruction-s030/`.

The [input](instruction-s030-input.json),
[checked report](instruction-s030-checked.json), and
[machine inventory](instruction-s030-machines.json) pin the proof package.
