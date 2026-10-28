# S012: a rightmost-one invariant

The exact complete machine `1LB0RA0LA0LB_3RB2RA2LB1LB` has a kernel-checked
proof of nonhalting and state quasihalting bound zero. Both states recur
arbitrarily late. Independent review and census registration are separate.

The invariant concerns the whole finite `head :: right` word. In B its last
nonblank symbol is 1. In A it may also be entirely blank. The inductive marker
definition admits explicit trailing zeros and arbitrary earlier symbols.
The actual blank tape satisfies the A case, and a universal one-step proof
preserves the invariant for every finite left context and right suffix.

An A0 step creates a new 1 to the right of the new B head. A2 and A3 cannot
be the rightmost nonblank under the invariant, so their left moves preserve
the existing rightmost 1. A1 and B1 can consume that last marker while moving
right into A; the newly exposed all-blank A suffix is allowed. The remaining
B transitions preserve the last 1.

Two finite inductions force returns from B to A. Induction on the left tape
handles every nonzero B head. B1 exits immediately. B2 scans left through
twos; a zero boundary gives a three-step bounce to the B3 induction case.
B3 writes 1 and continues left, with a constant exit at a blank left boundary.
Induction on the right suffix then handles B0: each initial zero moves right,
and the marker ensures a nonzero symbol is eventually encountered. The
existing one-state oracle separately proves universal returns to B.

Totality and these return theorems give arbitrarily late visits to both
states. No symbol-capacity weights or serialized history graphs are needed.
The universal negative control `r12_B0_drift` proves that B0 with an empty
right tail instead remains in B forever, even if the left tape contains a 1.
That configuration is excluded by the invariant.

[Native controls](burn18-s012-rightmost-native.json) cover 19,380 admitted
one-step configurations, 21,483 arbitrary nonzero-B returns, 2,295 marked-B0
returns, 4,096 actual blank-tape transitions, and negative blank-right drift
cases. These finite controls are provenance. The universal Coq proofs supply
the result. Eleven imported regressions check blank entry, trailing zeros,
both left and right return boundaries, and incorrect marker conditions.

Compilation took 4.890 seconds. Full recursive `coqchk` checked 265 modules
with zero reuse in 40.892 seconds, including the regression module. This
isolated proof introduces no new axioms, changes no accepted sources, and
makes no instruction-bound or global BBB(2,4) bound claim.

The [proof input](burn18-s012-rightmost-proof-input.json),
[checked report](burn18-s012-rightmost-checked.json), and
[exact inventory](burn18-s012-rightmost-machines.json) pin the one family.
Sources are [RightmostOne.v](../proof-sources/burn18-s012-rightmost/RightmostOne.v)
and [Regression.v](../proof-sources/burn18-s012-rightmost/Regression.v).
Reproduce with Coq on `PATH`:

```sh
python3 four/tools/check_burn18_s012_rightmost_native.py --check
python3 four/tools/check_burn18_s012_rightmost.py --timeout 600 --audit-timeout 1800
```
