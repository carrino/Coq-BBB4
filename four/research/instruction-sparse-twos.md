# A sparse A1 return and exact instruction score two

`1LB2LB3LB2RA_1RA3RA2LB1RA` (`tr24-2699702328`) has state upper bound zero
and exact instruction score **2**, including every completion of its table.
Displayed with its first move right, the machine is
`1RB2RB3RB2LA_1LA3LA2RB1LA`.

The former capacity diagnostics left A1 unresolved. Its finite return times
selected this counter proof, but no simulation result is a formal premise.
The main configurations have state A, head 1, blank right tape, and left tape
`2^n 1`, with the nearest cell first. A universal recursive A2 sweep takes
`F(n)=4·2^n−1` steps for positive `n`. A complete main cycle grows `n` by one
in `16·2^n−5` steps. Two exact initial steps reach the `n=0` main configuration;
its first cycle reaches `n=1` at step13. Induction gives arbitrarily late main
returns. Their explicit prefixes prove recurrence of seven instructions.

B0 is different: it fires at step1 and never again. The counter macros are
proved for an arbitrary B0 transition, including an undefined one. The variant
with B0 deleted has an infinite run from the actual configuration at step2.
Finite-run extension and determinism therefore exclude B0 in the actual suffix.
This argument does not assert that the deleted-slot machine is nonhalting from
the blank tape: a regression explicitly checks that it halts there at step2.

The seven recurrence proofs and B0 exclusion give `QHBoundTr 2 actual`; the
last B0 occurrence also proves `AttainsTr actual 2`. Both states recur, yielding
state bound zero. Registration proves exact table equality, original bootstrap
membership, every completion, and the exact singleton inventory. Regressions
cover arbitrary contexts, exact counter gaps and entries, deleted-slot behavior,
the required positive-block/sentinel conditions, and rejection of instruction
bound1. No axioms are added; only the existing functional-extensionality
assumption is imported.

After building the shared instruction dependencies, reproduce with Coq on PATH:

```sh
python3 four/tools/check_instruction_sparse_twos.py
```

Tracked templates are under `proof-sources/instruction-sparse-twos/`. The replay
driver compiles the proofs and exact board, then performs a full recursive audit
including regressions. Generated files and fresh receipts remain below
`four/build/instruction-sparse-twos/`; frozen reports are preserved. This adds
one instruction family and no state coverage, not a global instruction maximum.
