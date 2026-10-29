# S044: binary counter with a finite auxiliary count-up

The exact complete machine `1LB2LB0LB0RB_2RB1LB3LB2RA` has a kernel-checked
proof of nonhalting and state quasihalting bound zero. Both states recur
arbitrarily late. Independent review and census registration are separate.

The main configuration has a blank right tail. Left pairs, nearest first,
encode binary digits as `20` and `22`; the head is the binary value modulo
three. The actual blank tape reaches the one-digit maximum at step six.
The empty word is safe as well.

The nonoverflow macro clears an arbitrary run of maximal pairs and bumps the
next zero pair, preserving arbitrary outer contexts. It increases the value
by one and rotates the boundary head. All-maximal words have head zero or
one; checksum two is excluded arithmetically. Head-one overflow grows the
word with its existing linear macro.

Head-zero overflow uses an auxiliary count-up between a fixed far-left 2 and
a terminal 1. Auxiliary pairs are `02` and `22`. A carry increments their
binary value while preserving word length; the natural rank
`2^length(ds)-1-value(ds)` strictly decreases. The all-maximal auxiliary word
finishes in A with the standard main-word encoding restored. Well-founded
induction proves a finite positive overflow duration for every word length.
The native timing formula is diagnostic; the universal termination proof
uses the decreasing rank.

The main macros preserve the checksum and give a strictly positive return
from every main configuration. Chaining them proves nonhalting and
arbitrarily late A visits. Every main configuration enters B on its next
step, which gives B recurrence and hence state bound zero.

[Native controls](burn18-s044-counter-native.json) cover 8,191 main words
through twelve digits, 10,584 arbitrary-context increments, 3,528 auxiliary
context increments, 1,022 auxiliary drains, and 21 overflow controls. They
provide finite provenance. The Coq proof supplies universal correctness.
Eleven imported regressions cover actual blank entry, arbitrary contexts,
carry, both overflows, the empty word, and invalid boundary applications.

Compilation took 4.841 seconds. Full recursive `coqchk` checked 263 modules
with zero reuse in 41.515 seconds, including the regression module. The
proof introduces no new axioms, changes no accepted sources, and makes no
instruction-bound or global BBB(2,4) bound claim.

The [proof input](burn18-s044-counter-proof-input.json),
[checked report](burn18-s044-counter-checked.json), and
[exact inventory](burn18-s044-counter-machines.json) pin this one family.
Sources are [S044Counter.v](../proof-sources/burn18-s044-counter/S044Counter.v)
and [Regression.v](../proof-sources/burn18-s044-counter/Regression.v).
Reproduce with Coq on `PATH`:

```sh
python3 four/tools/check_burn18_s044_counter_native.py --check
python3 four/tools/check_burn18_s044_counter.py --timeout 600 --audit-timeout 1800
```
