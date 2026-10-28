# A concrete ternary counter closes a sparse instruction holdout

`1LB2LB3LB2RA_3RA1RA1LB1RB` now has **exact instruction score 4** and **state
bound 0**. Its B3 instruction fires for the last time at configuration step 3;
all six instructions other than B0 and B3 recur. This closes one instruction
obligation and adds no state obligation: the baseline `StateReach` board already
covers its state bound. This burn4 result is separate from the frozen burn3
publication checkpoint.

The missing instruction was A0. Finite observations showed rapidly increasing
gaps, but a three-million-step diagnostic exposed a small exact counter form.
After startup, successive A0 configurations are

```text
C(n) = ... 0  1  2^n  [A0]  0 ...
```

The head is on the blank immediately to the right of the block. Configuration
`C(1)` occurs at step 11. The
[counter proof](burn4-ternary-counter/Counter.v) establishes, for every `n`,

```text
C(n)  -- exactly 3^(n+2) - 2 steps -->  C(n+1).
```

The first return from the blank initial configuration is the separate
11-step startup. Subsequent checked examples illustrate the general theorem:

| Configuration | Firing step | Gap to the next return |
| --- | ---: | ---: |
| `C(1)` | 11 | 25 |
| `C(2)` | 36 | 79 |
| `C(3)` | 115 | 241 |
| `C(4)` | 356 | 727 |

The proof uses two concrete macros. In state B, a leftward scan converts a block
of 2s to 1s; the sentinel 1 then turns the head right into state A. Processing
`n` consecutive 1s to the right of that sentinel produces `n` consecutive 2s
and returns A to the following cell. Its work satisfies

```text
G(0) = 0
G(n+1) = 3*G(n) + 2*n + 5
G(n) + n + 3 = 3^(n+1).
```

Two increment-and-reset passes and the final A3 move establish the induction.
The initial A0 reset costs `n+2` steps, followed by `G(n+1)`, giving the stated
gap. The proof explicitly establishes positive gaps and a sequence of firing
times at least as large as its index. A0 therefore fires arbitrarily late; no
simulation horizon or assumed return-time bound is involved.

The [tail proof](burn4-ternary-counter/Tail.v) preserves a simple sentinel
invariant from step 4. In state A, the nearest-first left stack is a nonempty
word over `{1,2}` ending in 1. In state B, the head followed by the left stack
has that property. Thus B can read neither 0 nor 3 after step 4. The prefix
checks include B0 at step 1 and B3 at step 3, and the latter is proved to be
B3's exact last firing.

The [closeout](burn4-ternary-counter/Closeout.v) combines A0 recurrence with
five independently checked witnesses from the saved 159-node graph: A1, A2,
A3, B1, and B2. It proves both bounds, rejects instruction bound 3, covers all
completions, and checks membership in the original pending census. An exact
inventory theorem identifies this one machine.

Replay after `make -C four all`, from the repository root:

```bash
python3 four/tools/check_burn4_ternary_counter.py \
  --timeout 300 --audit-timeout 1200
```

The [input](burn4-ternary-counter-input.json) pins a 793-byte graph bundle.
The runner pins the handwritten templates and consumed helpers, regenerates
five Coq files under `build/burn4-ternary-counter/proof/`, and preserves
published evidence on replay. The
[checked report](burn4-ternary-counter-checked.json) records 4.387 seconds for
compilation and a full recursive audit of 269 modules with no reuse in
36.537 seconds. Only the existing functional extensionality assumption remains.
The macro induction, sentinel invariant, closeout, runner, exact inventory,
source/object pins, and complete audit closure were independently reviewed.
