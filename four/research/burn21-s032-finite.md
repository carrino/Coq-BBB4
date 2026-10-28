# S032: finite state score from a compressed cut transcript

For `1LB2LA1RA2RB_2RB3LB0LB1LA` (code `1684925051`), the original blank run
enters B0 with a blank right half-tape at step `67093892759901295`.
State A occurs at the preceding step and never occurs again. The package
proves this exact state score, `NonHalt`, `QuasiHaltsSt`, the convenient state
bound `2^56 = 72057594037927936`, and the bound by the current champion.
It contributes one state family and zero instruction families.

The proof does not simulate the large finite prefix. It uses 53 instances of
universal cut rules. Write `C(a,r)` for A0 with blank left half-tape and right
word `2^a r`; write `Q(m,r)` for A at the first cell of `r` with `m` ones on
its left. `CutMacros.v` is an unchanged copy of the previously frozen local
cut library. `BinaryBridge.v` transports its arithmetic through binary `N`.
`Trace.v` composes the instantiated edges. Counts stay opaque and long
repeated tape blocks remain symbolic throughout.

The reset cuts `C(2,3^n 1)` have successive run lengths

```text
2, 13, 1423, 8902, 22263, 139152, 347888, 869728,
2174328, 5435828, 13589578, 33973953.
```

At step `67093892229058240`, the original run reaches
`C(530843041,[3])`. The universal exposed-three rule proves that this cut
enters B0 with right tail empty after `530843055` further steps. The ending
left word is `2 :: 1^530843044`; it is expressed as a symbolic repeat, never
materialized. Universal B0 rightblank drift supplies all later visits to B.
The bootstrap rule supplies the final A visit one step before the escape.
The original blanket recurrence hypothesis was therefore false; the local
negative guard identified the eventual actual behavior.

The native report is provenance only. A separate sparse direct simulator
checks the original prefix through step 491443 at all 17 listed cut
checkpoints and checks 13 exposed-three boundaries. Coq independently proves
all 53 finite transitions and the infinite drift suffix. Eight imported
regressions cover actual entries, arbitrary right context, the essential
blank-left guard, the Q bridge, exposed-three behavior, original escape,
exact last A, and the uniform bound.

Generated wrappers prove equality with the exact encoded transition table,
exact inventory identity, original pending census membership, and the state
bound for every completion. The machine is already complete, and the
completion argument uses its proved nonhalting behavior. The recursive audit
starts at the exact Inventory module and includes all eight package modules,
including regressions, with zero reused modules. Finite cut and trace
lemmas add no axioms; lifted state theorems use the repository's existing
functional extensionality assumption.

From the repository root, with the census Coq environment on PATH:

```sh
python3 four/tools/check_burn21_s032_finite_native.py --check
python3 four/tools/check_burn21_s032_finite.py
python3 four/tools/check_burn21_s032_finite.py --check
```

The checked report pins proof inputs, templates, generated sources, objects,
and the full recursive audit receipt. Frozen research and accepted proof
packages remain unchanged. Aggregate tracker updates and independent review
are separate from this isolated proof package.
