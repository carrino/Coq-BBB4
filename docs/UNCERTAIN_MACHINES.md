# Machines I am genuinely uncertain about — hand-inspection queue

_Wave-12 session (§1 corrected after John's reading).  Everything else in the current burn-down is either boarded
or diagnosed-mechanical; these are the cases where I do NOT trust my own
classification and where the wave-8/9 rule ("hand-inspection is 11-for-11")
applies.  Ranked by how much rides on the answer._

---

## 1. ~~The wall-inner nest~~ — RESOLVED: mis-set anchor, they are plain counters

**Status: my classification here was WRONG.**  John identified
`1RB---_1RC1LB_0LB1RD_0RA0RC`, `0RB0RD_1LA1RC_1RD1LC_0LC1RA` and
`0RB0RD_1RC---_1RD1LC_0LC1RA` as "just a regular counter with a 1 to the
left of each bit, msb on the left".  Verified, and it holds for the whole
bucket — reading (2) below (mis-set anchor) was the right one.

Re-anchored measurement over all 12, uniform with no exceptions:

| | |
|---|---|
| anchor | `Cc v = (E, Ip v ++ [S1], S0, [])` — tail `[S1]`, far EMPTY |
| edge `E` | B / C / A per machine |
| anchor snapshots in 40k steps | 1356–1365 |
| interior lap | **affine, `8 + 4j`** on every one of the 12 |
| overflow `2^K-1 -> ?` | **affine, `4K + 3` steps** (measured 15, 19, 23, 27 for K = 2..5) |

There is **no inner counter and nothing exponential** in these machines.
What I measured as "three interleaved marches at wall 0 / 2 / 4" was one
counter seen through an anchor that was two cells too long: `derive_tail`
returned tail `[S1;S0]` + far `[S0]` (its synthetic blank) instead of the
true tail `[S1]`, and my overflow probe then searched for a configuration
the machine never visits, so it ran on far past the real lap and reported
a doubling cost.  **The lesson is the one already in COUNTER_CLOSEOUT §5
and WAVE9 §2 — check the anchor variant before believing a verdict — and I
did not apply it.**

### What actually blocks them (the real, smaller problem)

The counter does not step through every value: the reachable anchors are
`{1} ∪ [4,7] ∪ [16,31] ∪ [64,127] ∪ …`, i.e. `[2^(2k), 2^(2k+1)-1]`.
Interior laps are `p -> p+1`, but the overflow is

```
  3 -> 8      7 -> 16      15 -> 32      31 -> 64        (2^K-1  ->  2^(K+1))
```

— it adds **one more pair** than `Pos.succ` does (`Ip (2^(K+1))` is
`rep [S1;S0] (K+1) ++ [S1]`, where `Ip (Pos.succ (2^K-1))` would be
`rep [S1;S0] K ++ [S1]`).  So `glue_neverqh tm Cc p0`, which requires a lap
`Cc p -> Cc (Pos.succ p)` for EVERY `p`, does not apply on the nose: the
anchor family needs a reindexing (or a glue variant) whose successor is
`p+1` inside a block and `2p+2` at a block end.

That is a small, well-posed question — and the one worth your view: is it
better to reindex the family (enumerate the reachable values) or to add a
`glue` variant taking a per-p successor function?  Either way it is a
fraction of the work I thought this bucket needed, and it is affine
throughout.

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

**Measured since (`find_inner_anchor` on three of them): this bucket SPLITS.**

| machine | wall | inner-anchor candidates | reading |
|---|---|---|---|
| `0RB0RD_0LC1RD_1RB1LC_0LA0RB` | `[1]` | one, far `[1]` | inner far CONSTANT → a genuine wall × IXP **composition**, mechanical |
| `0RB1LA_1RC1LB_0LB1RD_0LA0RC` | `[1]` | far `[1,1]`, `[1,1,1]`, … | inner far GROWS → same nest as §1 |
| `0RB1RC_1LA1LC_0LD0RA_1RA1LD` | `[0,1]` | far `[1,0,1]`, `[1,1,0,1]`, … | inner far GROWS → §1 nest |

So the 68 must be partitioned by that test before any template is written:
the constant-far members compose the two existing templates; the growing-far
members are §1 and should wait for your verdict there.  Do NOT template the
whole bucket as one family.

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
* **Wall count-offsets (172)** — `cR/cT/cRo/cTo` are `(2,1,1,0)` in the
  emitted template; the sweep measured `(4,2,3,1)` and `(3,1,2,1)` members
  too.  I first assumed this was a gate constant and tried relaxing the
  check — it is not: the offsets appear in the proof script's `rep` algebra
  (`replace (2 * S j) with (S (S (2*j)))`, the `pair_fold` count, the
  `rep_dbl` folds), so each offset family needs its `change`/`replace` lines
  generated from the constants.  Real work (~20 lines of template macros),
  still mechanical, no judgement needed.
* **IXP pop-variant combos (34)**, **far-mutating P1i (6)** — see
  `docs/WAVE12_IXP.md` §3.

## 4. Still deferred to stable hardware (unchanged, do not start here)

The champion `1RB1LD_1RC1RB_1LC1LA_0RC0RD` (needs `exists B, QHBound B` +
a 32.8M-step prefix) and the carry-shifted one-off
`0RB1LC_1LC0LC_0RD1LA_1RD1RB` (anchor `Cc (p, k)` with a frame offset).
Both are compute-bound, not judgement-bound.
