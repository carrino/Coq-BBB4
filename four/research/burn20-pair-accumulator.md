# S075: a two-block pair accumulator

This isolated package proves `NonHalt` and `QHBound 0` for the exact frozen
S075 table:

```text
1LB2RB0LA2RA_1RB3LB2LB2RA
```

Its code vector is `[5;11;0;10;7;13;9;10]`. The native controls and proof
runner verify frozen-checkpoint membership and this complete table. The Coq
wrapper separately proves table equality, an all-completion state-zero
board, and an exact census inventory.

Write `P=12`. A selected configuration has A scanning blank, an empty right
tail, and nearest-first left word:

```text
2^a 1 P^b       a >= 1, b >= 1
```

The actual blank tape reaches `(a,b)=(4,2)` in 68 steps. A universal return
maps `(a,b)` to `(a+3,a+b)` and costs exactly
`6a²+20a+9+8(a+1)b` steps. Every return has positive duration and preserves
the positive block lengths. These returns give arbitrarily late A visits;
the following step visits B. Totality proves nonhalting, and recurrence of
both states proves `QHBound 0`.

The Coq definition `pa_main m n` uses physical block lengths `a=m+1` and
`b=n+1`, so its return is `(m,n) -> (m+3,m+n+1)`, with exact cost
`6m²+40m+8(m+2)n+51`. The blank entry is `pa_main 3 1`.

The finite drain uses `G(p,q,k)`: A scanning 3, left word `21 P^p`, and
right word `3^q 2^k 1`, where `p,k` are positive. Its three phases are:

| Start | Return | Steps |
| --- | --- | --- |
| selected `(a,b)` | `G(b,0,a)` | `a+8b+7` |
| `G(p,q,k+1)`, `k >= 1` | `G(p+1,q+1,k)` | `8p+4q+24` |
| `G(p,q,1)` | selected `(q+4,p+1)` | `8p+5q+27` |

Induction on `a-1` closes the drain. Its intermediate return is proved for
arbitrary natural `q` and positive `p`; no growth estimate or finite graph
certificate is assumed.

The central restoration lemma starts B on the nearest cell of a nonempty
finite left word `P^p`, with any right context `r`. In `8p+5` steps, it reaches
A reading the first cell of `r`, with left word `21 P^p`; the entire right
context is preserved. The proof uses the blank boundary beyond the finite
pair word. It scans B left over pairs, executes a five-step boundary turn,
and inductively scans A back over `32` pairs with a six-step supported
program. The supporting A3, B0, A2, B1, B2, and pair scans retain arbitrary
left and right contexts where their statements allow them.

A shared increment lemma handles a next tag of either 1 or 2. Both B1 and
B2 move left in B; B1 writes 3, and B2 retains 2. The tag-2 case continues
the drain. The tag-1 case leaves a final finite A3 sweep to blank. The
shared lemma is universally quantified over its right suffix.

The positivity restrictions matter. A zero-length leading 2 block fails
the selected main return, and an empty pair word fails restoration. The
nineteen Coq regressions include these negative controls, both tag cases
with nonblank suffixes, the smallest legal loop and finish boundaries, the
actual blank entry and first two returns, and exact A3/B1 target-state
checks. Concrete fixtures use Coq's checked VM computation; the universal
macros and recurrence are separately proved in the core.

Reproduce from the repository root with Coq 8.18 available on `PATH`:

```sh
python3 four/tools/check_burn20_pair_accumulator_native.py --check
python3 four/tools/check_burn20_pair_accumulator.py
```

The 22,104 native controls test exact scans, arbitrary contexts of length
at most two, both increment tags, finite drains, positive returns, actual
entry, and negative guard/table controls. Cost metadata is derived from
the tested cost functions and checked against the Coq formulas by the
proof runner. Native controls supply no proof credit.

The runner pins the frozen input, native selection, templates, complete
source dependency closure, and generated objects. It compiles the core,
regressions, exact-table wrapper, all-completion board, and exact inventory,
then runs a fresh recursive kernel audit including the regressions.
Generated artifacts remain under `four/build/burn20-pair-accumulator/proof`.
The only axiom reported for the core theorem is the repository's existing
functional extensionality axiom from finite-tape lifting.

This package claims one state family and no instruction family. Independent
review and tracker registration are separate. Earlier proof packages are
unchanged.
