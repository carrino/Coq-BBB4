# S020: a closed binary-token counter grammar

The exact complete machine is `1LB0RB1LA3RA_1RB3LA2LB2RA` (code
`4338317776`). The new proof establishes `NonHalt` and `QHBound 0`, hence
the exact all-completion state census family. It makes no instruction claim.

Write finite words in physical order to the right of the head, and put

```
P = 1312       Z = 1111       O = 3213
E = 1321       G(m) = 322 P^m 1311.
```

A main cut `C(n,bits,T)` has state A, blank head and left half-tape, and
right word `322 P^n 111 enc(bits) T`. Binary digits are little endian;
`enc(0)=Z`, `enc(1)=O`. The terminal tag `T` is either `E` or `G(m)`.
Every finite binary word, including the empty word, is admitted. There is
no parity condition or relation between `n` and the binary value.

The three universal rules, with all parameters arbitrary natural numbers,
are:

```
C(n,1^j 0 ds,T) -> C(n+1,0^j 1 ds,T)     in 64n+114+16j steps
C(n,1^j,E)      -> C(0,1 0^n,G(j))       in 54n+26j+147 steps
C(n,1^j,G(m))   -> C(n+1,0^j 1 0^m,E)   in 64n+16j+22m+152 steps.
```

The first rule is stronger: its untouched suffix is an arbitrary symbol
list. The proof factors each traversal into context-parametric local
steps, inductive forward/backward sweeps, and a ten-step true-token carry
with a six-step rewind. The two overflows use separate fixed terminal
steps and repeated-block inductions. The inductive word grammar is closed
under these three positive-length returns. These are universal Coq
theorems, rather than extrapolations from finite runs.

The exact blank configuration reaches `C(0,[1],E)` after 176 steps.
Positive grammar returns therefore give arbitrarily late A visits; the
next transition from each main cut visits B. The machine is total, so it
also never halts. This proves the quiet-state bound zero without assuming
the reachable right-marker condition from the earlier open obligation.

The regression source includes both overflows, an increment outside the
previous parity hypothesis, the empty binary word, and the false broad
grammar's escape from right word `31311` after 29 steps. Two unsafe bare
left-3 boundaries escape after three steps. A universal B0/blank-right
drift theorem proves these negative boundaries permanent.

The separate native checker independently decodes the transition text and
checks 540 finite macro instances, the exact blank entry, and the three
negative escapes followed by 65 drift steps each. It grants zero proof
credit. Its input uses a copied frontier list, never the mutable live
tracker. All native and proof inputs, templates and replay-tool sources
are frozen by hashes. Replay requires the public theory source closure
and this package's own artifacts; no historical object-byte identity or
unrelated accepted report is required.

Replay from the repository root with Coq 8.18:

```sh
export PATH=/workspace/.opam/census/bin:$PATH
python3 four/tools/check_burn30_s020_counter_native.py --check
python3 four/tools/check_burn30_s020_counter.py --timeout 600 --audit-timeout 1800
```

The formal driver compiles all five modules freshly, then runs full
recursive `coqchk`, including the regression module, with no reused
receipt. The checked report records the audit and source closure.
Only the existing functional-extensionality axiom is used.

The author replay passed: five modules compiled in 4.943 seconds in total;
the fresh recursive audit checked 265 modules, reused zero modules, and
took 42.744 seconds. Independent review and registration belong to the
coordinator.
