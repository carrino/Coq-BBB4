# Conjugate counter with one transient initial instruction

The exact family `tr24-2819321740` has canonical table
`1LB2LB1LB3RA_2RA3LB3RA1RA`; its reflected form is
`1RB2RB1RB3LA_2LA3RB3LA1LA`.

`BBB24CounterConjugate.ConjugateCounter.instruction_attains` and
`instruction_bound` prove the exact instruction score **1**. A0 fires only at
configuration index 0. The other seven instructions recur beyond every time
horizon. Both states recur, giving state upper bound zero without an attainment
claim at zero.

The proof reuses the unchanged symbolic `TwosCounter.v` macros. It proves run
transport under state swapping, the blank-preserving symbol permutation
`(0,2,3,1)`, and reflection at arbitrary configurations. The actual first three
steps reach the transformed nonblank counter boundary. No blank-start
nonhalting premise for the source or erased source is assumed: the regression
explicitly checks that the erased source halts from blank.

The all-completion theorem is
`BBB24CounterConjugate.Inventory.small_sound : BoardSound 0 1 board`.
`Inventory.sound` raises both bounds to the champion score. `was_pending` checks
original bootstrap membership and `inventory_exact` identifies this one exact
family. Replay rebuilds the original counter and its regressions from frozen
sources, compiles the new proofs, and recursively checks both proof roots and
all dependencies with stock `coqchk`:

```sh
python3 four/tools/check_instruction_counter_conjugate.py
```

Only the existing functional-extensionality assumption is used. This closes one
historical instruction holdout; it does not provide a global instruction census
or maximum theorem.
