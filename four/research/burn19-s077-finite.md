# A finite prefix ending in permanent B motion

The complete machine `1LB2RB3LA2RA_3RB3LA0LB1LB` has exact state score
2,501,552. Its last A visit is at configuration index 2,501,551; from the next
configuration onward it remains in B. The census package uses the convenient
upper bound `2^22 = 4,194,304`, below the existing champion. It registers one
exact state family; aggregate integration is separate.

Coq evaluates two compact Boolean predicates from the blank initial tape.
One checks that step 2,501,552 is in B, reading zero, with an entirely blank
right tail. The other checks that step 2,501,551 is in A. Both use binary N
input counts converted internally to the ordinary CTape step count. The proof
receives no ending tape or intermediate trajectory from the native replay.
The computed propositions are proved by `vm_compute; reflexivity` and checked
again by the full recursive kernel audit.

A separate universal theorem proves that B0 with a blank right tail moves
right forever, writing `3`. The theorem allows arbitrary finite left tapes
and explicit zero padding on the right. Combining it with the checked prefix
proves every later configuration is B, the exact last A visit, and the exact
index-plus-one state score. Totality proves nonhalting. Binary count lemmas
transport the result to the census bound and to the existing champion bound
without expanding those bounds as giant unary numerals.

An independent Python parser and sparse-tape replay confirms the finite
prefix and its last A visit. At escape the head is at position 6 and nonzero
support is `[-2741,5]`, containing 2,747 cells. Only compact counts, selected
checkpoints and a digest are retained; no generated trace or ending word is
stored in the proof input. The native replay and 1,155 synthetic drift controls
provide provenance only. Eight imported regressions cover blank padding,
nonzero right tails, the distinction between B0 and B3, and both finite
certificates.

After building the core, run from the repository root:

```sh
python3 four/tools/check_burn19_s077_finite_native.py --check
python3 four/tools/check_burn19_s077_finite.py --timeout 600 --audit-timeout 3600
```

The runner caps address space at 3 GB. The initial isolated finite-prefix
pilot used approximately 474 MB and completed in 1.1 seconds. The checked
report pins exact sources, objects, census inventory and recursive audit
receipt. The proof uses core BBB24 modules only, introduces no new axioms,
changes no accepted source or runner, and makes no instruction-bound claim.
