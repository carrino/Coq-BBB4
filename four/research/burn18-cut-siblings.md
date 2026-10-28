# Two regular-cut siblings

This isolated package proves nonhalting and a state bound of zero for both
complete machines:

- S027: `1LB2LA0RA2LB_3RB1LA0RB3RA`
- S031: `1LB2LA1RA2LB_3RB1LA0RB3RA`

The core proof is parameterized by the symbol written by A2, either 0 or 1.
After the first blank-tape step, B scans a blank with the single symbol 1 on
its right. At selected B returns, the head and left side contain only 0 and
3, the right side contains only 1 and 2, and the number of right-hand 1s is
strictly greater than the number of 3s in the head and left side. Implicit
blank padding has no effect on either count.

The surplus supplies a first right-hand 1. For arbitrary surrounding tape
contexts, the proof establishes the following exact macros. Here `l` and `r`
are arbitrary finite words; the tape is displayed left-to-right, with the
head in brackets, and the left context `l` is implicit in the display.
The Coq representation stores that left context nearest cell first.

| B head | First right block | A2 write | Cost | Return |
| --- | --- | --- | --- | --- |
| 0 | `1 r` | either | 3 | B moves one cell left; right becomes `2 1 r` |
| 0 | `2^(n+1) 1 r` | either | `n+4` | B is at the right end of `0^n 3 l`; right becomes `1 1 r` |
| 3 | `1 r` | either | 3 | B moves one cell left; right becomes `2 2 r` |
| 3 | `2^(n+1) 1 r` | 0 | `n+4` | B is at the right end of `0^n 3 l`; right becomes `1 2 r` |
| 3 | `2^n 1 r` | 1 | `2n+3` | B moves one cell left; right becomes `2^(n+2) r` |

Each macro has positive cost and preserves the alphabets and strict surplus.
The B0 scan reaches A after `n+2` steps when the first 1 follows `n` twos;
B3 reaches A in one step. Universal B returns therefore establish arbitrary-
time visits to both states, hence `QHBound 0`. Totality separately establishes
`NonHalt`.

Strictness is necessary. The invalid cut with B on 3 and a single right-hand
1 has equal counts. In three steps it becomes B on blank with only two twos
on its right; B then crosses the finite word and drifts into blanks. The
regression file checks this boundary, the actual blank entries, arbitrary
context controls, both A2 branches, and a corrupted first-two block.

Reproduce from the repository root with Coq 8.18 on `PATH`:

```sh
python3 four/tools/check_burn18_cut_siblings_native.py --check
python3 four/tools/check_burn18_cut_siblings.py
```

The native controls are provenance only. The proof runner compiles the core,
ten regressions, both exact complete-table wrappers, the all-completion
state-zero board, and its exact census inventory. It then performs a fresh
recursive kernel audit of the inventory, including the regressions. Generated
sources and objects stay under `four/build/burn18-cut-siblings/proof`.

The only axiom reported for the core theorem is the repository's existing
functional extensionality axiom from the finite-tape lifting library. The
package makes no instruction-bound or global census-closeout claim. Holdout
credit requires independent review and tracker registration.
