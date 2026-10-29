# S074: returns for every finite binary word with an even number of ones

For `1LB2RB0LA1RB_2RB3RA1LA0LB` (code `527720261`), both states recur
arbitrarily late. This package proves `NonHalt` and `QHBound 0`, contributing
one state family and zero instruction families.

Let `C(w)` be A0 with empty left tape and finite right word `w`. The preserved
cut grammar consists of every word over `0,1` with an even number of `1`s.
The executable grammar predicate rejects `2,3`, leaves its parity bit
unchanged on `0`, toggles on `1`, and accepts only an even final parity. The
original blank configuration is `C(empty)`, so no finite simulation is needed
to establish entry.

The return proof has two finite inductions. A three-step bootstrap enters A
at the first symbol of `w`, with left wall `32`. If the next symbol is `1`,
even parity guarantees a second `1` after a finite zero run. Reading
`1 0^n 1` in `n+2` steps adds left block `3 2^(n+1)` and returns to A at the
remaining word. That word is shorter and still has even parity. This is the
forward word-length induction.

At a zero or the empty word, a finite wall unwinds back to `C`. The main
context-preserving wall merge is

```text
A0, left 3 2^(a+1) 3 2 l, right r
  -> A0, left 3 2^(a+1) l, right 11r       in 4a+8 steps.
```

Both outer contexts `l,r` are arbitrary. A single wall block has the base
program

```text
A0, left 3 2^(a+1), right r
  -> C(0^a 101r)                           in a+3 steps.
```

For a nonempty list of wall blocks, merging the first two combines their
zero-gap parameters and removes one block. Wall-length induction proves
that the full output is `0^(sum gaps) 101 1^(2k) r`, where `k` is the number
of removed blocks. The output prefix has an even number of ones. A positive
recursive cost function records every merge and base step.

These programs prove that every accepted `C(w)` has a positive finite return
to another accepted `C(w')`. A constructive induction on a desired time
horizon chains enough positive returns to obtain an arbitrarily late A0 cut.
Every cut enters B one step later. Both states therefore have unbounded
visits, excluding every final state visit. Totality independently proves
nonhalting. No compact algebra template or numerical ruler interpretation is
assumed by this proof.

The parity guard is essential. The synthetic odd word `C([1])` enters B0
with a blank right tape after four steps, and a universal drift theorem proves
permanent subsequent B motion. A second regression rejects a wall missing
its required `2` cell. Neither synthetic seed is claimed to occur on the
original orbit.

The hypotheses were recorded before formalization. Native provenance contains
16,019 controls: 1,024 accepted cut words of length at most 10, arbitrary
contexts for the scan/merge programs, finite wall unwinds and both boundary
negatives. It also independently reproduces the first 64 original returns,
including the observed ruler gaps. Native observations receive zero proof
credit. Eight imported regressions and the universal proofs are included in
the recursive kernel audit.

Finite programs, grammar closure and positive returns are closed under the
global context. Lifted recurrence and census results use only the repository's
existing functional extensionality assumption. Generated wrappers prove the
exact encoded table, exact inventory, original pending census membership and
the state bound for every completion. No instruction-family claim is made.

From the repository root with the census Coq environment on PATH:

```sh
python3 four/tools/check_burn29_s074_even_counter_native.py --check
python3 four/tools/check_burn29_s074_even_counter.py
python3 four/tools/check_burn29_s074_even_counter.py --check
```

The checked report pins hypotheses, proof input, native provenance, templates,
generated sources, objects and the full recursive audit receipt. Accepted
packages, shared trackers and checkpoint-59 publication remain unchanged.
