# S040: eleven walls around one supported word

This isolated package proves `NonHalt` and `QHBound 0` for the exact frozen
S040 table:

```text
1LB2LA3RA0RB_2RB2RA3LA1LB
```

Its complete code vector is `[5;8;14;3;11;10;12;5]`. Native controls and the
proof runner verify exact frozen-checkpoint membership and this vector.
The Coq wrapper separately proves complete-table equality, the state bound
for every completion, and an exact census inventory.

Let `P=332330202020332330`, written nearest-first. A selected `s40_main n`
has A scanning 0, an empty right word, and left word `P^n22`. The actual
blank tape reaches `s40_main 0` in three steps. The universal return is:

```coq
forall n,
 csteps s40_tm (1056*n+577) (s40_main n) =
 Some (s40_main (S n)).
```

Every return has positive duration, giving arbitrarily late A visits. The
following step visits B. Totality proves nonhalting, and recurrence of both
states proves `QHBound 0`.

There are eleven finite terminal walls. At phase i, A scans 0, the left
word is `P^n F_i`, and the right word is empty. The phase costs are:

| i | F_i | Steps |
| --- | --- | --- |
| 0 | 22 | `96n+5` |
| 1 | 203 | `96n+11` |
| 2 | 20332 | `96n+31` |
| 3 | 33233222 | `96n+43` |
| 4 | 332330322 | `96n+51` |
| 5 | 3323303303 | `96n+81` |
| 6 | 3323302233022 | `96n+47` |
| 7 | 33233020333022 | `96n+69` |
| 8 | 332330202033032 | `96n+87` |
| 9 | 3323302020223303 | `96n+55` |
| 10 | 33233020202033303 | `96n+97` |

Each row reaches the next wall with the same n. The final row reaches wall
22 with n increased by one. Their exact sum is `1056n+577`. The core proves
each row for every natural n and arbitrary right context r: its final A
configuration reads the first cell of r. The selected cycle uses r empty,
so every phase again scans blank. No physical blank padding is silently
removed from an exact configuration.

The common left scan starts B on the nearest cell of `P^n` and consumes one
P word in 66 steps, emitting `E=131133131313131133` to the right. This scan
is proved by induction for arbitrary left and right contexts. The eleven
finite wall programs take 3 through 93 steps and return to the emitted
right word. They use the implicit blank beyond the finite wall and are
universally quantified over the unread right context.

Two right gates restore the P words. From B reading `E^n1r`, the first
gate reaches A reading r, prepending `P^n2` to the left context, in `30n+1`
steps. From A reading the same word with a supporting 2 on the left, the
second gate prepends `P^n33` in `30n+3` steps. Both statements quantify over
arbitrary remaining left and right contexts.

The right scan itself uses `H=E[1:]1` and `V=P[1:]3`. Starting A on 2, it
consumes H in 30 steps and prepends V. The identities `E^n1=1H^n` and
`3V^n=P^n3` restore the original P orientation. A separate 30-step B entry
handles the first emitted block. All unbounded scans are induction proofs;
finite native traces are not used as universal certificates.

The gate guards are necessary. Removing the supporting 2 from the A gate,
or changing the terminal right tag 1 to 0, invalidates the claimed return.
The 28 Coq regressions include these negative controls, both gate boundary
cases, arbitrary scan contexts, all eleven zero-word phase boundaries,
a positive last phase, actual blank entry and the first three returns,
and exact A3/B3 target-state checks. Concrete fixtures use checked VM
computation; the universal scans, gates, phases, and recurrence are proved
separately in the core.

Reproduce from the repository root with Coq 8.18 available on `PATH`:

```sh
python3 four/tools/check_burn27_s040_word_cycle_native.py --check
python3 four/tools/check_burn27_s040_word_cycle.py
```

The 25,116 native controls independently replay finite wall programs,
short arbitrary scan/gate contexts, every phase, complete returns, blank
entry, and negative guard/table cases. The pinned programs JSON records
wall endpoints and word data. Cost metadata is derived from the tested
functions and checked against the Coq formulas by the proof runner. These
native controls provide no proof credit.

The runner pins the frozen checkpoint, selection report, program data,
templates, source dependency closure, and generated objects. It compiles
the core, regressions, exact-table wrapper, all-completion board, and exact
inventory, then performs a fresh recursive kernel audit including the
regressions. Generated sources and objects remain under
`four/build/burn27-s040-word-cycle/proof`.

The only axiom reported for the core theorem is the repository's existing
functional extensionality axiom from finite-tape lifting. This package
claims one state family and no instruction family. Independent review and
tracker registration are separate. Earlier accepted and frozen partial
packages remain unchanged.
