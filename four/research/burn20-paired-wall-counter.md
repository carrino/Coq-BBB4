# S050: a paired wall counter with parity phases

This isolated package proves `NonHalt` and `QHBound 0` for the exact frozen
S050 table:

```text
1LB2LB1LA1RA_3RB3LA3LB0RB
```

Its code vector is `[5;9;4;6;15;12;13;3]`. The native controls and proof runner
check this vector and frozen-checkpoint membership. A separate Coq wrapper
proves complete-table equality, exact census inventory, and the bound for
every completion of the recorded family.

Write `P=30`. A selected `wc_main n` configuration has A scanning blank,
an empty right tail, and nearest-first left word:

```text
1^4 P^(4n+2) 0
```

The actual blank tape reaches `wc_main 0` in 149 steps. The universal return
adds four `30` pairs and costs exactly `416n+577` steps. Thus every return is
positive, giving arbitrarily late A visits. The next step visits B. Totality
proves nonhalting; recurrence of both states proves `QHBound 0`.

The selected return combines three parity phases. Here `stage(a,p)` denotes
A on blank with left word `1^a P^p 0` and empty right tail:

| Start | Return | Steps |
| --- | --- | --- |
| `stage(4,p)` | `stage(3,p+1)` | 21 |
| `stage(3,2k+1)` | `stage(3,2k+2)` | `52k+63` |
| `stage(3,2k+2)` | `stage(4,2k+4)` | `156k+285` |

With p=`4n+2`, the first phase reaches an odd wall length, the second an even
wall length, and the third returns to the selected class. The Coq phase
lemmas retain an arbitrary right tape context; their final A configuration
reads that context. The selected cycle uses the empty context, so A reads
blank at each phase boundary.

The core finite scans use right word `W=3211`. A 20-step program consumes two
left `30` pairs and emits one W. The return scans consume one W in 32 or 58
steps, adding two left pairs. Separate 23-, 38-, 35-, 57-, and 114-step
boundary programs close the phases. Every such program is universally
quantified over its wall length and right tape context. The long scans are
proved by induction on the number of pairs or emitted W words.

The physical wall boundary matters. After a left prefix `11`, the first wall
cell is 3 when pairs remain and 0 at the end. An arbitrary symbol cannot
replace this guard: a negative regression changes it to 1 and invalidates
the 32-step return macro. The core proves the programs for every wall word
`P^p 0`; it does not assume a finite native trace is universal.

The fourteen Coq regressions check actual blank entry, both parity-phase
boundaries, context scans, both turns, nonblank outer contexts at the finish,
the four-one phase's context read, the missing guard, and exact A3 identity.
Computed concrete fixtures use Coq's checked VM computation; the universal
library lemmas and return induction are separately proved in the core.

Reproduce from the repository root with Coq 8.18 available on `PATH`:

```sh
python3 four/tools/check_burn20_paired_wall_counter_native.py --check
python3 four/tools/check_burn20_paired_wall_counter.py
```

Native controls check the macro formulas in short arbitrary contexts, the
wall-length scans and parity phases, and sixteen complete selected returns.
Their cost metadata is derived from the native cost functions and checked
against the Coq formulas by the proof runner. Native controls provide no
proof credit. The runner compiles the core, regressions, exact-table wrapper,
all-completion state-zero board, and exact census inventory, then performs a
fresh recursive kernel audit including the regressions. Generated sources
and objects remain under `four/build/burn20-paired-wall-counter/proof`.

The only axiom reported for the core theorem is the repository's existing
functional extensionality axiom from finite-tape lifting. No instruction
bound or global census closeout is claimed. Holdout credit requires
independent review and tracker registration. Earlier accepted packages
remain unchanged.
