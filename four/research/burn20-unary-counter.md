# S011: a unary counter with an alternating terminal bit

This isolated package proves `NonHalt` and `QHBound 0` for the exact frozen
S011 machine:

```text
1LB0LB2RA2LA_2RB2RA3LB1RB
```

The code vector is `[5;1;10;8;11;10;13;7]`. Native controls and the proof runner
check frozen-checkpoint membership and this exact table; the generated Coq
wrapper separately proves complete-table equality and exact census inventory.

A selected configuration has state A scanning blank, a blank right tail, and
the nearest-first left word `2 1^(2n) 2`. The actual blank tape reaches the
case n=0 in three steps. The universal return theorem is:

```coq
forall n,
 csteps uc_tm (8*n*n + 12*n + 7) (uc_main n) =
 Some (uc_main (S n)).
```

Thus every return adds two 1s. The positive exact cost gives arbitrarily late
A visits, and the next step visits B. Totality proves nonhalting; recurrence
of both states proves `QHBound 0`.

For n>0, three initial steps reach A scanning 3 with a finite left-hand run
of 1s. An intermediate configuration has a supporting 2 on the left, k
remaining 1s, m further 3s on the right, and a terminal bit 0 or 1. One
iteration consumes one left 1, adds one right 3, and toggles that bit. It
costs `4m+7` steps. The universal drain lemma repeats this k times in exactly
`2k²+4mk+5k` steps, for arbitrary surrounding finite tape contexts.

The initial number of iterations is odd, so the terminal 1 becomes 0. With
no left 1s remaining, the separate finish lemma grows the selected unary
word and returns A to blank. The finish case with terminal 1 is invalid and
is covered by a negative regression. The case n=0 is checked directly.

All scans are proved for arbitrary finite contexts. A scans 3s in three
steps per cell using an actual supporting left 2; B scans left over 2s and
right over 3s in one step per cell. The eleven Coq regressions check actual
entry, empty and nonempty growth, the iteration and odd drain in nonblank
contexts, the zero-length drain, the finish boundary, the wrong terminal
bit, missing support, and the exact A2 transition.

Reproduce from the repository root with Coq 8.18 available on `PATH`:

```sh
python3 four/tools/check_burn20_unary_counter_native.py --check
python3 four/tools/check_burn20_unary_counter.py
```

The native controls check local macro formulas in short arbitrary contexts
and the complete return formula for n=0 through 15. Their cost metadata is
derived from the same native cost functions used for the controls. They
provide no proof credit. The proof runner compiles the core, regressions,
exact complete-table wrapper, all-completion state-zero board, and exact
census inventory, then performs a fresh recursive kernel audit including
the regressions. Generated sources and objects remain under
`four/build/burn20-unary-counter/proof`.

The core theorem reports only the repository's existing functional
extensionality axiom from finite-tape lifting. No instruction bound or global
census closeout is claimed. Holdout credit requires independent review and
tracker registration. Earlier accepted proof packages remain unchanged.
