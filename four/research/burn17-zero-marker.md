# A binary counter with one moving zero marker

The complete machine `1LB2LB0LB1RA_2RB2RA3LB0RA` has a kernel-checked state
quasihalting bound of zero. Both states recur arbitrarily late. This package
registers one exact census family; aggregate integration is separate.

A main configuration is in A with a blank right tail. The left word is either
an even-length block of `2`s, or `p 0 2^b`, where `p` contains only `1` and `2`,
`b` is positive, and `length(p)+b` is even. The head is the binary value of the
positions containing `2`, modulo three, with the nearest position having
weight one. The blank run reaches the two-cell maximal block at step 3.

The first nonmaximal bit increments through `2^k1 → 1^k2`. When the unique
zero follows a nonempty maximal prefix, `2^(k+1)0 → 1^k02` moves the marker
one cell toward the head. Both operations increase the binary value by one,
rotate the head `0→1→2→0`, and cost twice the carried prefix length plus two.
The sweep and increment lemmas quantify over arbitrary outer tape contexts.

When the marker reaches the boundary, the parity condition forces an even
suffix of `2`s. Its checksum forces head zero, and a three-step expansion
replaces the marker with two `2`s. Carrying beyond an even maximal block
creates a single marker with the required parity. These cases give a closed
invariant with a strictly positive next macro from every main configuration.

The grammar is essential. The synthetic left word `[0,2]` with head `2`
satisfies the checksum but reaches B on a blank right tail in three steps;
B then continues forever. Coq proves that this seed violates the grammar.
Both the escape and its exclusion are imported regressions.

Positive chaining establishes arbitrarily late A returns and original
nonhalting. Each return enters B on its next step, so B also recurs.
Native controls checked 21,168 arbitrary-context increment/marker macros,
48 outer carries, and 5,463 grammar configurations. These provide provenance
only; the universal Coq proofs establish the result. Eight regressions are
included in the inventory's full recursive kernel audit.

After building the core, run from the repository root:

```sh
python3 four/tools/check_burn17_zero_marker_native.py --check
python3 four/tools/check_burn17_zero_marker.py --timeout 600 --audit-timeout 3600
```

The report `research/burn17-zero-marker-checked.json` pins exact sources,
objects and inventory. The proof uses core BBB24 modules only, introduces
no new axioms, changes no accepted source or runner, and makes no instruction
bound claim.
