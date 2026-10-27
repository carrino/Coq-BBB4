# A paired-digit invariant closes an instruction holdout

The total machine `1LB2LA1RB3RB_3RA1RB3LA1RA` has exact instruction
quasihalting score **10**. Instruction B1 last fires at configuration index 9;
the other seven instructions recur at arbitrarily large indices. Both states
therefore recur, and its state bound is 0.

The previously saved weighted graph certified recurrence of seven instruction
targets, but its abstraction also admitted B1. Simulation suggested B1 stopped
early; the new proof establishes permanent exclusion rather than extrapolating
from the finite trace.

## The invariant

At configuration 10, the machine is in B on a blank cell with left half-tape
`113`. From then on, a left marker `3` bounds a tape of digit pairs `(2|3)2`,
an already processed prefix of `1`s, and a blank right frontier. Seven explicit
phases describe the marker, digit scan, separator scan, two frontier phases,
turnaround, and left reset.

The reset phase tracks parity: the number of remaining `1`s plus the number of
already restored `2`s is even. Resetting therefore preserves the paired-digit
language; frontier extension adds two cells. Every B configuration has head
symbol 0, 2, or 3. The handwritten
[`TailInvariant.v`](burn3-tail-invariant/TailInvariant.v) proves preservation
under every step and B1 exclusion from configuration 10 onward. It also checks
the exact prefix and B1 firing at configuration 9.

The existing `InstructionPortfolio.wp_graph_check_sound` independently replays
the saved seven-target recurrence certificate. The
[`Closeout.v`](burn3-tail-invariant/Closeout.v) proof combines recurrence and
exclusion into `Bounds 0 10`, proves that instruction bound 9 is impossible,
extends the result to every completion, and links the family to the original
census pending predicate. This machine has no unspecified transitions.

## Replay

After building the core with `make -C four all`, run from the repository root
with the repository Coq toolchain on `PATH`:

```bash
python3 four/tools/check_burn3_tail_invariant.py \
  --timeout 300 --audit-timeout 1200
```

The runner uses the two tracked handwritten proof sources and a 1,265-byte
compact certificate. It generates four modules, checks the exact one-family
inventory, and performs full recursive `coqchk`. It preserves published input,
inventory and report files on replay; generated sources, objects and current
execution receipts remain in `four/build/burn3-tail-invariant/proof/`.

The new census increment is one instruction obligation and no state obligation,
since the state bound was already known. This local result does not establish
the global BBB(2,4) upper bound.
