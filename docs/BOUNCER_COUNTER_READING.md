# A sync bouncer counter in the residue, read off the tape

_John, 2026-07-27, on `1RB0RB_1LC1RA_1RA0LD_0LB0LD`: "this one is surely a
bouncer counter."  It is, and measuring it names a gap in `LapDecider` more
precisely than five waves of overflow-shape work did._

## The machine sits in BOTH residues

* it is in our `D_remaining`;
* it is in the **BBB(4) holdout list** -- one of the 27 genuine mxdys holdouts
  (`tools/census_holdouts_kept.txt`).

So it is hard for everyone, and it is NOT a quick win.  Its value is
structural.

## What our tools say: nothing

    ovfshape.py        -> "-/no-anchor"
    alphabet_infer.py  -> no inferable family

Both recognizers are blind to it.  John read it off a spacetime diagram in
seconds.

## What it actually does (measured)

Sampling at the canonical phase (state A on a blank cell), splitting the tape
into the leading run of 1s and everything right of it:

| t | bouncer length | region right of the bouncer |
|---:|---:|---|
| 14 | 3 | `01` |
| 46 | 6 | `0101` |
| 94 | 9 | `010001` |
| 150 | 12 | `010101` |
| 226 | 15 | `01000001` |
| 306 | 18 | `01010001` |
| 402 | 21 | `01000101` |
| 506 | 24 | `01010101` |
| 634 | 27 | `0100000001` |
| ... | ... | ... |
| 2026 | 51 | `010000000001` |

Three facts fall straight out:

1. **The bouncer is `3n`** -- exactly linear in the increment count.
2. **The counter widens at `n = 2, 3, 5, 9, 17`** -- gaps `1, 2, 4, 8`, i.e.
   DOUBLING.  That is the overflow, and it is `a + b + 1 = 2^n` from the wiki's
   `C'(a,b,n)`: one overflow costs `2^n` increments.
3. **The middle digits are a plain binary counter.**  Reading `01` as digit 1
   and `00` as digit 0, low digit nearest the bouncer: `n = 5,6,7,8` give
   `0,1,2,3`; the next width gives `0..7`.

So this is the sync bouncer counter of
`wiki.bbchallenge.org/wiki/Inductive_Proof_System`, verbatim: *"both a bouncer
and a counter on the tape, and the lowest digit of the counter is adjacent to
the bouncer"*; increment per bouncer period; overflow restructures the bouncer.

## Why `LapDecider` cannot see it -- the precise gap

Our symbolic side is

    sside = pre ++ rep u (a*j + b) ++ post ++ X

and **`j` is the CARRY-RUN LENGTH** (`cview p = (j, Some q0)` counts p's
trailing 1-digits), i.e. a LOCAL index.  This machine's bouncer is `3p` --
affine in the counter's **GLOBAL VALUE**.

`sside` can say *"this side carries `j` copies of a block."*  It cannot say
*"this side's length is proportional to the value the OTHER side encodes."*
Two coupled quantities, one index.

That is a sharper statement of the residue's wall than "the overflow costs
`Theta(2^j)`".  The cost is a SYMPTOM: the bouncer must be re-swept once per
increment, and there are `2^n` increments per overflow, so the overflow is
exponential *because* the two quantities are coupled.

## What has the missing expressiveness

`Inductive.v`'s tape language carries counter-VALUED sides as first-class
constructors:

    side_binary      (d1 : list Sym) (n : nat_expr)
    side_binary_Pos  (c : ...)       (n : nat_expr)
    side_binary_dec  (c : ...)       (len n1 n2 : nat_expr)   <- C'(a,b,n)

`side_binary_dec` carries THREE counts -- `(n, a, b)` -- which is exactly the
pair-of-complementary-counters this machine runs, and `config_SBC` wires its
increment and overflow rules together.  Our 25 alphabets encode a value as a
WORD (`E p`), but the lap that consumes them is indexed by `j`, not `p`, so the
coupling is inexpressible on our side.

## What to do with this

* **Do not use this machine as a test case for the `config_SBC` hint** -- it is
  a genuine mxdys holdout, so the hint presumably fails on it too.  Pick
  bouncer-counter-shaped machines that are NOT in the holdout list.
* **Measure the class.**  Nobody has counted how many residue machines are
  bouncer+counter rather than plain counters.  The signature is cheap: a
  leading run affine in the increment index, and a region beyond it whose width
  jumps on a doubling schedule.  The measurement above is ~20 lines.
* **The `j` vs `p` gap is the thing to design against.**  A second index -- a
  side whose length is affine in the counter VALUE, not the carry index --
  is a smaller ask than the nested lap and would cover this whole class.

## Standing note

Hand-inspection is now 23-for-23 across waves 8-15.  Both recognizers returned
"nothing here" on a machine whose structure is obvious in a picture.  Ask early,
ask with a tape.
