# Binary countdown by a decreasing rank

The complete machine `1LB1RB0LB2RA_1RB3LB2LB3RA` has a kernel-checked state
quasihalting bound of zero. Both states recur arbitrarily late. The package
registers one exact census family; aggregate integration is separate.

An internal configuration has a fixed `3` boundary on its left, a nonempty
word of `0` and `2` cells, then a terminal `1`. Read the word as a binary
number, least significant digit first, with `2` representing one. The
universal macro `0^k2 → 2^k0` decreases that number by exactly one and
preserves the word's length. It costs two steps for `k=0`, otherwise
`4*k+6` steps. Once the number is zero, the remaining nonempty zero word
becomes a block of `2` cells and exits with head `3` in `3*length+4` steps.

Coq proves termination by well-founded induction on the binary value.
The sweep lemmas quantify over arbitrary outer tape contexts; the proof
does not need to run an exponentially long cycle. A main configuration
has head A0 and left tape `2^n31`, with `n≥1` and blank right tail. Entering
the countdown and then taking one A3 step grows that block by one. The
actual blank tape reaches `n=1` at step 7.

The nonempty requirement is essential. An empty bit word puts A on the
terminal `1`, immediately entering B on a blank right tail. Two regressions
record that excluded case. Positive completed macros establish unbounded
A0 returns and original nonhalting; each return enters B on its next step,
proving B recurrence as well.

Native controls checked 7,056 decrement/finish macros with arbitrary outer
contexts of length at most two, plus all 254 nonempty binary words of length
at most seven. These are provenance only. Eight regressions are explicitly
imported into the inventory and included in its full recursive audit.

After building the core, run from the repository root:

```sh
python3 four/tools/check_burn17_binary_rank_native.py --check
python3 four/tools/check_burn17_binary_rank.py --timeout 600 --audit-timeout 3600
```

The report `research/burn17-binary-rank-checked.json` pins the exact sources,
objects and inventory. The proof uses core BBB24 modules only and introduces
no new axioms. It changes no accepted proof or runner and makes no instruction
bound claim.
