# S057: finite prefix followed by permanent B

The exact complete machine `1LB2LB1RB1RA_1RB3LA3RA2LB` has kernel-proved
state quasihalting score **2,333,909**. Its last A visit is at configuration
index 2,333,908, and every configuration from index 2,333,909 onward is in B.
The census inventory uses the conservative bound **2^22 = 4,194,304**.
Independent review and registration are separate.

Coq recomputes two small Boolean certificates from the actual blank tape.
One verifies A at index 2,333,908. The other verifies B with a zero head and
an entirely blank right suffix at index 2,333,909. The certificate does not
consume a native final tape or native trace.

The universal `sd_B_drift` theorem handles arbitrary finite left tapes and
arbitrary explicit blank padding on the right. B0 writes 1, moves right and
stays in B; the new head is again zero and the remaining suffix is blank.
Induction proves permanent B for every later time. Together with the checked
preceding A visit and the index-plus-one convention, this gives
`AttainsSt tm 2333909` and a matching `QHBound`. Totality proves nonhalting.
The conservative inventory bound is transported through binary `N` and is
proved below the existing champion bound. No global BBB(2,4) value theorem
or instruction-bound claim is introduced.

An [independent Python replay](burn21-s057-native.json) checks all 2,333,909
transitions and agrees with the separately captured C++ discovery result.
The final native head is at position 13, with nonblank support `[-3327,12]`
and 3,340 cells to its left. Native checkpoints and tape hashes are diagnostic
provenance; the formal result uses Coq's own computation and drift proof.

Twelve imported regressions cover both computed cuts, exact attainment,
empty and padded blank right tails, arbitrary left tapes, and rejected
nonblank tails, incorrect states, nonzero heads and halting results. A
nonblank right tail can return to A, so the blank-tail premise is essential.

Compilation took 7.698 seconds. Full recursive `coqchk` checked 265 modules
with zero reuse in 40.860 seconds, including every regression. The proof
introduces no new axioms and changes no accepted source.

The [proof input](burn21-s057-drift-proof-input.json),
[checked report](burn21-s057-drift-checked.json), and
[exact inventory](burn21-s057-drift-machines.json) freeze this one family.
Sources are [RightBlankDrift.v](../proof-sources/burn21-s057-drift/RightBlankDrift.v)
and [Regression.v](../proof-sources/burn21-s057-drift/Regression.v).
Native provenance includes the [input](burn21-s057-native-input.json),
[captured discovery row](burn21-s057-source-result.json), and
[captured discovery source](burn21-s057-source-probe.cpp).

Reproduce with Coq on `PATH`:

```sh
python3 four/tools/check_burn21_s057_native.py --check
python3 four/tools/check_burn21_s057_drift.py --timeout 600 --audit-timeout 1800
```
