# S009: the frozen run-counter sibling

This package proves `NonHalt` and `QHBound 0` for the exact frozen S009 table:

```text
1LB0LB1LA3RB_3RB3RA1RB2LB
```

Its code vector is `[5;1;4;15;15;14;7;9]`. In particular, A3 is **3RB**.
The exploratory table with A3=3RA is a different machine outside the frozen
holdout cohort. Its earlier complement-transducer probe earns no holdout
credit. Both the native controls and Coq regressions explicitly distinguish
those transitions; the proof runner pins and checks the frozen 78-machine
checkpoint as well as the exact census inventory.

Selected configurations have A scanning blank, a blank right tail, and the
nearest-first left word `3 enc(bits) 3`, where false is `11` and true is `33`.
Every finite bit word is admissible. The actual blank tape reaches the
empty-word configuration in three steps.

| Bit word | Next bit word | Steps |
| --- | --- | --- |
| `true^n false tail` | `true^n true tail` | `16n+16` |
| `true^n` | `false^(n+1)` | `4n+7` |

The first branch sets the first false bit, retaining the lower true bits and
remaining context. Overflow grows an all-false word by one bit. Both costs
are positive, so the universal return induction gives arbitrarily late A
visits. The next step visits B, and totality establishes nonhalting. Thus
both states recur and `QHBound 0` follows.

The finite scans are proved directly for this exact table. With a 3
immediately left of A scanning 2, three transitions move A right and leave
two 3s behind: A2 writes 1 and moves left in A; A3 writes 3 and moves right
in B; B1 writes 3 and moves right in A. Repeating this supported scan and
combining it with the universal B left/right scans gives the first-false
branch. All-true overflow uses a separate boundary macro. The library is
isolated from the earlier S006 package and does not change its sources.

The twelve Coq regressions check the actual blank entry, empty-word and
padded overflow, first-false runs in arbitrary outer context, a longer carry,
a supported A scan, missing support/boundary cells, a nonblank tail, a malformed
pair, and the explicit 3RB-versus-3RA target distinction.

Reproduce from the repository root with Coq 8.18 available on `PATH`:

```sh
python3 four/tools/check_burn20_run_sibling_native.py --check
python3 four/tools/check_burn20_run_sibling.py
```

The native controls check all 511 bit words through length eight and local
macros over short arbitrary contexts. They also reject the wrong 3RA table
using the supported three-step scan. They provide no proof credit. The proof
runner compiles the core, regressions, exact complete-table wrapper,
all-completion state-zero board, and exact census inventory, then runs a
fresh recursive kernel audit including the regressions. Generated sources
and objects remain under `four/build/burn20-run-sibling/proof`.

The only axiom reported for the core theorem is the repository's existing
functional extensionality axiom from finite-tape lifting. No instruction
bound or global census closeout is claimed. Holdout credit requires
independent review and tracker registration.
