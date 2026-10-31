# Return through a preserved rightmost marker

The complete machine `1LB2RA0LB1RA_1RB3LB2LB0RA` has a kernel-checked state
quasihalting bound of zero. Both states recur arbitrarily late. This package
registers one exact census family; aggregate integration is separate.

The invariant concerns the head and right half-tape. Its rightmost nonzero
symbol is `1` or `3`, or the entire suffix is blank and the state is A. All
eight transitions preserve this condition. A0 creates a fresh `1` on the right
before entering B. A2 can enter B only when another marker remains to its
right. A1 and A3 may leave a blank suffix while moving right in A. B1 preserves
a last `1` by writing `3` and moving left, even though it stays in B.

Every B configuration reading a nonzero symbol returns to A, independently
of the right context. The proof uses induction on the finite left tape.
B1 and B2 move into a shorter left context. When B2 encounters a blank, a
three-step bounce produces B1 on a shorter left context. Empty-left cases
reading `1`, `2`, and `3` return in respectively three, six, and one steps.
A B0 configuration with a marker to its right walks through any leading
zeros and reaches a nonzero symbol. These lemmas quantify over arbitrary
finite contexts.

Thus every reachable configuration returns to A. Totality supplies a valid
prefix of every length, and the invariant plus return lemma extends each
prefix to an A visit. The independent core one-state checker proves that
every A episode returns to B, giving B recurrence as well. Nonhalting follows
from totality. No unbounded countdown simulation is needed.

The marker condition is essential. A synthetic isolated A2 with left `[0]`
and a blank right tail reaches blank-right B0 in two steps. B0 then moves
right forever, writing `1`. The universal drift lemma and a regression prove
this excluded behavior. The initial blank configuration satisfies the
invariant directly; another regression checks the actual step-7 A0 entry
with left tape `101`.

Native controls checked 2,331 invariant-preserving steps, 1,323 B returns on
nonzero symbols, and 1,134 B0 returns with a right marker. They provide
provenance only; the Coq invariant and finite-context induction establish
the universal result. Eight imported regressions are included in the full
recursive kernel audit.

The initial three-block counter hypothesis and the stronger marker hypothesis
were recorded before formalization in `burn18-s065-rightmost-hypotheses.json`.
The proof uses the stronger marker invariant; the earlier finite parameter
grid does not supply proof credit.

After building the core, run from the repository root:

```sh
python3 four/tools/check_burn18_s065_rightmost_native.py --check
python3 four/tools/check_burn18_s065_rightmost.py --timeout 600 --audit-timeout 3600
```

The checked report pins exact sources, objects and census inventory. The proof
uses core BBB24 modules only, introduces no new axioms, changes no accepted
source or runner, and makes no instruction-bound claim.
