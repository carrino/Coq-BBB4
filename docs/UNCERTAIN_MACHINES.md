# Machines I am genuinely uncertain about — hand-inspection queue

_Wave-12 session.  Everything else in the current burn-down is either boarded
or diagnosed-mechanical; these are the cases where I do NOT trust my own
classification and where the wave-8/9 rule ("hand-inspection is 11-for-11")
applies.  Ranked by how much rides on the answer._

---

## 1. The wall-inner nest — 12 machines (HIGHEST VALUE, most uncertain)

```
0RB0RD_1LA1RC_1RD1LC_0LC1RA        M0RB1LC_1LA1RB_0LD0LA_1RA1LB
0RB0RD_1RC---_1RD1LC_0LC1RA        M0RB1LC_1LA1RB_0LD0LA_1RA1LD
1RB---_1RC1LB_0LB1RD_0RA0RC        M1RB0LD_1LC1LB_1LD1RC_0RC1LA
1RB---_1RC1LB_0LB1RD_1RA0RC        M1RB1LC_0LA0LD_1LD1RC_0RC1LB
1RB0RD_1RC---_1RD1LC_0LC1RA
1RB1LA_0LA1RC_0RD0RB_1LB1RA
1RB1LA_0LA1RC_0RD0RB_1LB1RD
1RB1RA_1RC1LB_0LB1RD_1LA0RC
```

**What I measured.**  On `1RB---_1RC1LB_0LB1RD_0RA0RC` (anchor `Cc p =
(B, Ip p ++ [S1;S0], S0, [S0])`), inside the K = 4 outer overflow lap the
blank-head snapshots that decode as `Ip v ++ [S1]` read:

```
  t= 23  v=32  wall=0        t= 71  v=18  wall=2
  t= 27  v=16  wall=2        t= 81  v= 9  wall=4
  t= 37  v= 8  wall=4        t=105  v= 2  wall=8
  t= 43  v=34  wall=0        t=115  v=40  wall=0
  t= 47  v=17  wall=2        t=119  v=20  wall=2
```

Three interleaved marches at once: `v = 32,33,34,…` at wall 0, `v = 16,17,18,…`
at wall 2, `v = 8,9,10` at wall 4 — each march running at half the rate of the
one above it, with the far-side wall length growing 0, 2, 4, 8, …

**Why I am uncertain.**  Three readings fit the data and they need different
machinery:

1. a **two-parameter inner anchor** `Cin (v, wall)` — the wall is a second
   index and the composition is a double induction;
2. a **mis-set OUTER anchor**: the `v = 32,33,34,…` march at wall 0 could be
   the real counter one cell over, in which case the "exponential overflow" is
   an artifact of reading the tape at the wrong offset and these are ordinary
   affine machines (this is exactly the wave-9 §2 trap: *check the anchor
   variant before believing the verdict*);
3. genuine **three-level recursion** (counter inside counter inside counter),
   which would be new structure and worth a hand-authored reference board.

I can't separate these from step counts alone, and guessing wrong costs a
whole template.  This is the one where I'd most want your eye.

## 2. Wall + exponential overflow — 68 machines (composition, unproven)

Exemplars (full list: the `overflow laps not affine` rows of
`wls_L.json` / `wls_R.json`):

```
0RB0RD_0LC1RD_1RB1LC_0LA0RB   ov(K=2..5) = 76, 128, 228, 424   ratios 1.68 1.78 1.86
0RB1LA_1RC1LB_0LB1RD_0LA0RC   ov = 68, 120, 220, 416           ratios 1.76 1.83 1.89
0RB1RC_1LA1LC_0LD0RA_1RA1LD   ov = 48,  84, 152, 284           ratios 1.75 1.81 1.87
1RB1LA_0LA0RC_0LD1RB_1RC1LD   ov = 66, 118, 218, 414           ratios 1.79 1.85 1.90
```

Wall-anchored (so `emit_wall`'s interior fits) but the overflow cost doubles
(ratio → 2), so they need the IXP inner counter AND the wall in one board.
My guess is this is just the two templates composed — but it is a guess: if
the inner counter's own far side moves (as in §1) it is the same nest, not a
composition.  **Cheap check that would settle it:** run
`find_inner_anchor` on 2-3 of these and see whether the inner far word is
constant across the march.  Worth doing before anyone writes the template.

## 3. Diagnosed-mechanical (NOT uncertain — listed so they aren't re-derived)

These I am confident about; they need work, not judgement:

* **IXP inner-split (9)** — the inner lap closes (traced
  `1RB1LA_0LA1RC_0LD0RB_1LA1LD`: closes at t = 28) but its stop/turn is a
  3-step `A→B→B→C` sequence, not the outer's `STPI(1)+TRN(1)`.  Fix: free the
  inner `nSTP`/`nTRN` instead of reusing the outer's.
* **Erase-ripple wall shape (7 + the Jp exemplar)** —
  `M1RB---_0LC0LA_1LB1RD_1LC0RD` and 6 siblings crash `emit_wall` with a
  `'RET'` KeyError because their ripple deposits `S0`, not `S1`.  This is the
  *erase/rebuild* wall shape I already derived and validated step-exactly on
  `1RB0LB_1LA0LC_0LB0RD_1RD0RC` (interior `ER^j . ST . RB^k . CL`, 113 values
  checked; overflow with a left-open stop, K = 2..5).  Second wall template,
  fully measured, just not emitted.
* **Wall count-offsets (172)** — `cR/cT/cRo/cTo` hard-coded to `(2,1,1,0)` in
  `emit_wall.check_shapes`; the sweep measured `(4,2,3,1)` and `(3,1,2,1)`
  variants.  Parameterizing the offsets is a few lines.
* **IXP pop-variant combos (34)**, **far-mutating P1i (6)** — see
  `docs/WAVE12_IXP.md` §3.

## 4. Still deferred to stable hardware (unchanged, do not start here)

The champion `1RB1LD_1RC1RB_1LC1LA_0RC0RD` (needs `exists B, QHBound B` +
a 32.8M-step prefix) and the carry-shifted one-off
`0RB1LC_1LC0LC_0RD1LA_1RD1RB` (anchor `Cc (p, k)` with a frame offset).
Both are compute-bound, not judgement-bound.
