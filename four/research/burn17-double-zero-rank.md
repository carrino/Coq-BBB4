# Binary rank at a double-zero boundary

The complete table `1LB0RA0LB2RA_1RB3LB2LB1LA` has a kernel-checked state
quasihalting bound of zero. Both states recur arbitrarily late. The package
registers one exact census family; aggregate registration is separate.

The countdown starts in B scanning the nearer of two zero boundary cells.
To the right is a word of `0` and `2` cells followed by terminal `1`. Interpreted
as a binary number, least significant digit first and with `2` representing
one, the word decreases by exactly one under `0^k2 → 2^k0`. This machine's
exact decrement cost is `4*k+8` steps. Once the word is all zero, it becomes
a `2` block and exits in A with head `3` after `3*length+7` steps.

The proof reuses the frozen BinaryRank module's pure bit encoding, value,
decomposition and arithmetic lemmas. It proves every machine-specific sweep
and boundary transition independently. Well-founded induction on the binary
value handles arbitrarily large countdowns without simulating them.

Unlike the earlier boundary convention, an empty bit word is safe here.
The two zero boundary cells and terminal `1` are required; negative controls
demonstrate failures when either condition is changed. The sweep lemmas
quantify over arbitrary outer contexts.

A main configuration is A0 with blank right tail and left tape `2^n00`,
where `n≥1`. Entering the countdown and then executing one A3 step grows the
block by one. The actual blank run reaches `n=1` at step 9. Positive macro
lengths give unbounded A0 returns and original nonhalting; the next step from
each main configuration enters B, proving B recurrence directly.

Native controls checked 7,056 local macros and all 255 binary words of length
at most seven, including the empty word. They supply provenance only. Eight
regressions are imported into the inventory and included in its full recursive
kernel audit.

After building the core and the frozen `burn17-binary-rank` package, run from
the repository root:

```sh
python3 four/tools/check_burn17_double_zero_rank_native.py --check
python3 four/tools/check_burn17_double_zero_rank.py --timeout 600 --audit-timeout 3600
```

The checked report `research/burn17-double-zero-rank-checked.json` pins the
dependency report, exact sources, objects and inventory. No new axiom or
instruction-bound claim is introduced, and no accepted proof is changed.
