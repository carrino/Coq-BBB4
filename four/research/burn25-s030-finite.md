# S030: exact finite state score from two right-word phases

For `1LB2LA1LA2LB_2RB3RA0LB0LA` (code `44979812`), the original blank run
visits A for the last time at step `1367354345128`. Its exact state score is
`1367354345129`. The package proves `NonHalt`, `QuasiHaltsSt`, the exact score,
the convenient bound `2^41 = 2199023255552`, and the bound by the current
champion. It contributes one state family and zero instruction families.

Define `Q(a,w)` as A at the first symbol of finite right word `w`, with
nearest-first left word `3 2^a`. Empty `w` means a blank head and empty right
tape. The left marker and finite block are explicit; there is no arbitrary
nonblank outer left context. The right context `r` in these rules is arbitrary:

| Input | Output | Steps |
| --- | --- | --- |
| `Q(a,0r)` | `Q(1,1^a01r)` | `a+5` |
| `Q(a,11r)` | `Q(a+5,r)` | `6a+18` |
| `Q(a,101r)` | `Q(a+6,r)` | `6a+19` |
| `Q(a,empty)` | `Q(1,1^a01)` | `a+5` |

The universal pair induction consumes `2n` ones in
`n*(6a+3)+15n^2` steps and increases `a` by `5n`. Universal A2 left sweeps,
B2 left sweeps and B0 right sweeps prove the individual rules. A B bounce
moves through a finite zero block and consumes its next `2`; two bounces
suffice for the pair and `101` programs.

The complete cut word is essential. It alternates between `1^m0 1^c` and a
plain `1^m` phase. An unconditional unary family would omit the plain phase
and lose the terminal boundary. The pre-formalization hypotheses record this
phase distinction and the selected finite candidate.

`Trace.v` composes 34 universal macro instances after the three-step original
entry. At step `1367354345127` the original run reaches
`Q(1383582,[1])`. One step later it is A3 with left `2^1383582` and right `[2]`.
After the next step it is B and every cell of the entire tape is either
`0` or `2`. Both B transitions on that alphabet remain in B and preserve the
alphabet. Induction proves the full infinite suffix, including both motion
directions and implicit blank cells. The last A visit is therefore the A3
step, rather than a later B0 blank-boundary checkpoint.

All large counts remain opaque binary `N` transports; repeated words remain
symbolic. No million-cell ending tape or trillion-step primitive trace is
constructed or trusted. The finite trace lemmas are closed under the global
context. Lifted state and census results use only the repository's existing
functional extensionality assumption.

The native report is provenance only. An independent sparse direct simulator
checks the original prefix through step 92898 at 14 cut checkpoints. There
are 4,577 context, bulk, binary-suffix and missing-sentinel controls. Eight
imported regressions cover the original entry, all three arbitrary right
contexts, the plain phase, the unsafe singleton boundary, universal B motion
on binary tapes and the exact last A.

Generated wrappers prove equality with the exact encoded transition table,
exact inventory identity, original pending census membership, and the state
bound for every completion. The machine is complete; completion extension
uses its proved nonhalting behavior. The recursive audit starts at Inventory
and includes all eight package modules with zero reused modules.

From the repository root with the census Coq environment on PATH:

```sh
python3 four/tools/check_burn25_s030_finite_native.py --check
python3 four/tools/check_burn25_s030_finite.py
python3 four/tools/check_burn25_s030_finite.py --check
```

The checked report pins hypotheses, proof inputs, native provenance,
templates, generated sources, objects and the recursive audit receipt.
Accepted packages and shared trackers remain unchanged. Independent review
and aggregate integration are separate from this isolated proof package.
