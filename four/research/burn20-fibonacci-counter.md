# S022: a Fibonacci counter with two unary blocks

This isolated package proves `NonHalt` and `QHBound 0` for the exact frozen
S022 table:

```text
1LB1RA1LB2RB_3RB3LA3LB2RA
```

Its code vector is `[5;6;5;11;15;12;13;10]`. The native controls and proof
runner check that exact table and frozen-checkpoint membership. A separate
Coq wrapper proves complete-table equality and exact census inventory.

A selected `fc_main m n` configuration has A scanning blank, an empty right
tail, and the nearest-first left word:

```text
2^(2m) 1 2^(2n+1) 3
```

The first block can be empty. The second block has positive odd length. The
actual blank tape reaches `fc_main 1 0` in 24 steps. The universal return is:

```text
main(m,n) -> main(n+2,m+n)
steps = 8mn + 12n² + 20m + 44n + 37
```

Equivalently, physical block lengths `(a,b)=(2m,2n+1)` map to
`(b+3,a+b)`, preserving their even/odd parities. Every cost is positive,
so induction yields arbitrarily late selected A returns. The next step
visits B. Totality proves nonhalting; recurrence of both states proves
`QHBound 0`.

The proof uses finite scans and a drain over an explicit unary parameter.
B walks left over 2s, writing 3s. A consumes right-hand `33` pairs, writing
`22`. Separate wall and open-boundary lemmas retain the physical distinction
between a terminal left 3 and the implicit blank beyond a represented word.
All these scan lemmas quantify over arbitrary finite surrounding contexts.

An intermediate `fc_Q m n k` configuration has A on 2, nearest-first left
word `2^(2m) 1 2^(2n+1)`, and right word `3^(2k+1)`. Two phase rounds consume
two cells from the second left block while growing the other block and the
right block:

```text
Q(m,n+1,k) -> Q(m+1,n,k+1)
steps = 8m + 16n + 34
```

`fc_drain` repeats this exactly n times, reaching `Q(m+n,0,k+n)` in
`8mn+12n²+22n` steps. The separate `fc_Q_finish` lemma closes the remaining
one-cell block and returns to `main(k+2,m)`. Parity determines whether a
boundary phase reaches A on 1 or on 2; the proof checks those branches
explicitly.

The fourteen Coq controls check actual blank entry, an admissible empty first
block, the first actual growth, context scans, both wall/open boundaries,
a positive and a zero-length drain, the finish branch, and exact A3 identity.
A negative parity control starts with left word `[2;1;3]`; after 27 steps it
reaches B on blank with an empty right tail. B then drifts right, so the
parity conditions cannot simply be dropped. A second negative control
changes the physical left wall.

Reproduce from the repository root with Coq 8.18 available on `PATH`:

```sh
python3 four/tools/check_burn20_fibonacci_counter_native.py --check
python3 four/tools/check_burn20_fibonacci_counter.py
```

Native controls check the universal macro formulas on short arbitrary tape
contexts and complete returns for 64 parameter pairs. Their cost coefficients
are derived from the same native cost functions used by the controls, then
checked against the Coq formulas by the proof runner. Native controls provide
no proof credit. The runner compiles the core, fourteen regressions, exact
table wrapper, all-completion state-zero board, and exact census inventory,
then performs a fresh recursive kernel audit including the regressions.
Generated sources and objects remain under
`four/build/burn20-fibonacci-counter/proof`.

The only axiom reported for the core theorem is the repository's existing
functional extensionality axiom from finite-tape lifting. No instruction
bound or global census closeout is claimed. Holdout credit requires
independent review and tracker registration. Earlier accepted packages
remain unchanged.
