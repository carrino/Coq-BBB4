# Binary prefix with three terminal forms

The complete machine `1LB2LB0LB2RB_1RB2RA3LB1RA` has a kernel-checked state
quasihalting bound of zero. Both states recur arbitrarily late. This package
registers one exact census family; aggregate integration is separate.

A main configuration has a binary prefix encoded by pairs `12` and `22`,
followed by a terminal `11`, `21`, or `2`, and a blank right tail. The terminal
values are respectively two, zero, and one. With `n` prefix digits, the head
is the prefix's little-endian binary value plus `2^n` times the terminal value,
modulo three. The blank run reaches the empty prefix and terminal `21` at
step 3.

An ordinary increment clears `k` maximal prefix pairs and bumps the next
zero pair in `4*k+2` steps, rotating the head. The universal macro quantifies
over arbitrary outer tape contexts and over the second cell of the bumped
pair. When the prefix is all maximal, three terminal cases close the invariant:

- Terminal `11` forces head two. It becomes `21` with a zero prefix and head
  zero in `4*n+2` steps.
- Terminal `21` forces head zero or one. Head zero produces prefix `1 0^n`
  and terminal `2` in `4*n+5` steps. Head one requires `n>0` and produces
  prefix `0 1 0^(n-1)` and terminal `2` in `4*n+9` steps. Both end with head zero.
- Terminal `2` becomes `11` with a zero prefix in `4*n+4` steps, rotating
  the head.

The proof derives each checksum restriction and proves each machine-specific
macro. It does not infer a universal transition from a finite trace. The
wrong-head terminal-21 regression records both a failed synthetic transition
and the theorem excluding that head from valid maximal prefixes.

Strictly positive closed main macros give arbitrarily late A returns and
original nonhalting. Every main configuration enters B on its next step,
proving B recurrence and hence state bound zero.

Native controls checked 42,336 arbitrary-context increments, 54 outer macros,
and all 6,141 prefix/terminal configurations through ten prefix digits. They
provide provenance only; the universal Coq proofs establish the result.
Eight imported regressions are included in the full recursive kernel audit.

After building the core, run from the repository root:

```sh
python3 four/tools/check_burn17_terminal_pair_counter_native.py --check
python3 four/tools/check_burn17_terminal_pair_counter.py --timeout 600 --audit-timeout 3600
```

The checked report `research/burn17-terminal-pair-counter-checked.json` pins
sources, objects and exact inventory. The proof uses core BBB24 modules only,
introduces no new axioms, changes no accepted source or runner, and makes no
instruction-bound claim.
