# Binary carry with pairs20 and22

The complete machine `1LB2LB0LB0RB_2RB3RA3LB2RA` has a kernel-checked state
quasihalting bound of zero. Both states recur arbitrarily late. This package
registers one exact census family; aggregate integration is separate.

The left tape encodes binary digits, nearest first, as `20` and `22`. The
boundary head is the binary value modulo three, and the right tail is blank.
The actual blank tape reaches the one-digit maximum at step 5. Empty digit
words are also safe.

A nonoverflow increment clears `k` maximal pairs and bumps the next zero
pair in `4*k+4` steps. Its universal macro preserves arbitrary outer contexts.
The binary value increases by one, rotating the head `0→1→2→0`.

An all-maximal word has checksum zero or one. It never has checksum two.
Both overflow cases cost `4*n+5` steps for `n` digits and grow by one digit.
Head zero produces digits `0^n1` with head one. Head one, which requires a
nonempty word, produces `1 0^(n-1)1` with head zero. The latter skips a
counter value but preserves the invariant. Regressions exclude applying the
head-zero overflow to an all-maximal word with head two.

These universal macros give a strictly positive next main configuration.
Positive chaining proves original nonhalting and arbitrarily late A visits.
Every main configuration enters B on its next step, proving B recurrence
and hence state bound zero.

Native controls checked 10,584 arbitrary-context increments, 21 boundary
overflows, and all 8,191 binary words through twelve digits. These provide
provenance only; the universal Coq proofs establish the result. Eight imported
regressions are included in the full recursive kernel audit.

After building the core, run from the repository root:

```sh
python3 four/tools/check_burn17_paired_zero_counter_native.py --check
python3 four/tools/check_burn17_paired_zero_counter.py --timeout 600 --audit-timeout 3600
```

The checked report `research/burn17-paired-zero-counter-checked.json` pins
sources, objects and exact inventory. The proof uses core BBB24 modules only,
introduces no new axioms, changes no accepted source or runner, and makes no
instruction-bound claim.
