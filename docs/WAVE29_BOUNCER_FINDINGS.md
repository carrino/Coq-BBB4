# Wave-29B: the `no anchor` bucket measured, and the wall-indexed bouncer built

_Branch `claude/bouncer-noanchor-4-2-94gn4v`, 2026-07-29.  The 19 rows of the
`no anchor` bucket are the only ones in the residue on which EVERY route has
returned nothing for eight waves: `anchors()`, `restscan`'s tolerant reader
(every alphabet x every tail split x every far), and `regscan`'s chase all
report no anchor family.  John's read of `0RB0LD_1LA1LC_0LD0LC_1RD1RB`
(WAVE29_FINDINGS.md section 6) says why —_

> "keeps bouncing back and forth with c and d states.  then when it passes the
> wall on the right it moves the wall over one and heads back left and then
> goes back to bouncing"

_— **the counter is not a word, it is the wall position.**  This wave measures
the bucket against that read, and then builds it._

## 1. The one-line result

**7 new boards, all first render, all funext-only.**  `D_remaining`
**266 → 259**; core undecided **181 → 174**.

* **3** — the bucket's `1RB---` rows, quasihalters closed by `QHBound` via
  `LapGlueAbs.glue_qh_abs` (§5).
* **3** — the wall-bounce class `*_1LA1LC_0LD0LC_1RD1RB`, never-quasihalters
  closed by `LapGlue.glue_neverqh` (§6).
* **1** — the same class MIRRORED, `0RB1RC_1RC0LB_0RD0RC_1LD1LA` (§6b),
  transferred by `Mirror.mirror_never_qh`.

Two new files, both mine: `tools/counters/bouncecert.py` (the reader, §2) and
`theories/Counters/BounceGlue.v` (two sections, §5/§6), plus
`theories/Tests/CountersBounce_Corruption.v`.  **No existing library was
touched** — not `LapDecider`, not `LapGlue*`, not `SkipGlue`, not
`NestedLapLift`, not `QuadGlue`, not `MeasureGlue`, not `WrapBouncer`.
`BounceGlue` is axiom-free; every board's `Print Assumptions` is
`functional_extensionality_dep` only.  Nothing under `theories/Census/`
touched and `census_cache --check` MATCH throughout.

**The prediction in the prompt held: no new library Coq was needed, and
`MeasureGlue` was not needed either.**  Both boarded classes have a wall that
moves exactly one cell per bounce and a bounce cost affine in the wall index,
so the bounce COUNT is explicit in the anchor and plain induction suffices —
`WrapBouncer`'s situation, not `BounceCounter`'s.  `MeasureGlue.mrun` is for
the rows in §7, where the region between the walls does carry its own count.

## 2. The reader: `tools/counters/bouncecert.py`

Measures the only things that are actually on the tape, and assumes no
alphabet anywhere:

* **turnarounds** — every direction reversal, with column and state;
* **frontiers** — leftmost/rightmost column ever visited and the times each
  advances.  The frontier that advances RARELY is the macro index; the one
  that advances every bounce is the micro one.  A machine on which they
  advance together is single-LEVEL and is reported as such;
* **regimes** — consecutive bounce cycles segmented by their per-cycle
  `(colL step, colR step)`.  This is a threshold-free segmentation, and on
  John's exemplar it separates the two things that are visibly different on
  the tape — a 3-step drift ripple `(-1,-1)` and the bounce proper `(-2,+1)`
  — without either being named in advance;
* **the wall** — the turnaround column that moves by a fixed step per cycle;
* **the cost law** — the phase's cycle-cost sequence, split at its own
  measured drift/bounce boundary and fitted affine (and quadratic) in the
  wall index, with the **coverage** of the fit reported: an affine suffix
  that accounts for 3% of a phase's steps is not that phase's law;
* **the wall-indexed families** — the two turnaround configurations fitted as
  `pre ++ rep u k ++ post`, by exact insertion-point search over consecutive
  members, in the WALL index and in both senses (`k` and `m-k`, because a
  bouncer's far side shrinks while its near side grows);
* **the macro anchor** — the configuration at each phase boundary (§4).

`--emit` renders and compiles the `BNC_*` boards; every gadget is
differentially validated against the raw simulator first (the bounce and
terminal over an `(a,r)` grid, the collapse at every `n = 3..40`, the lap at
every `j = 1..59`, and the boot against the blank-tape replay).  The kernel
re-checks all of it.

## 3. The bucket, measured (all 19)

`bouncecert.py --all --steps 200000`.  `lv` = levels; `wall`/`step` = which
turnaround column marches and by how much per cycle; `pro` = the phase's
prologue length in cycles; `cost law` and `cov%` = the affine fit in the wall
index and the share of the phase's steps it covers.

    spec                           lv turns phase frontier  wall step  pro cycles cost law     shape        cov% kind
    0RB0LD_1LA1LC_0LD0LC_1RD1RB     2  1445     5 1k+1         R    1   26     27 6k+8         drift+affine   93 plain
    0RB0RB_1LA1LC_0LD0LC_1RD1RB     2  2170     5 1k+1         R    1   53     27 6k+8         pro+affine     90 plain
    0RB0RD_1LC1RB_1RA0LC_1LB0LC     2 66959    12 1k+1         R    1 3199    129 const 5      pro+affine      3 counter
    0RB0RD_1LC1RB_1RA0LC_1LD0LC     2 66959    12 1k+1         R    1 3199    129 const 5      pro+affine      3 counter
    0RB1LA_1LA1LC_0LD0LC_1RD1RB     2   817     5 1k+1         R    1    1     40 6k+8         drift+affine   95 plain
    0RB1LB_1LC1RC_1RD0LA_0RC1RB     2 77999   181 -2k-2        R    0    0      1 none         irregular     100 counter
    0RB1LC_1LC0RD_1RD0LC_1LA1RB     2 67420    15 -1k-1        R   -2 12478   127 const 4      pro+affine      0 counter
    0RB1LC_1LC1RD_1LA0LC_0RD1RB     2   888    15 -1k-1        R    1    0      2 none         irregular     100 counter
    0RB1RC_1RC0LB_0RD0RC_1LD1LA     2  2167     3 -1k-1        L   -1   53     27 6k+5         pro+affine     94 plain
    1RB---_1LC0RB_1LD1RB_1LC1RB     1   893   446 1k+1         R    1    0    298 2k+c         affine        100 plain
    1RB---_1LC1RD_1LB1RD_1LB0RD     1   893   446 1k+1         R    1    0    298 2k+c         affine        100 plain
    1RB---_1LC1RD_1LB1RD_1LC0RD     1   893   446 1k+1         R    1    0    298 2k+c         affine        100 plain
    1RB0RB_1LC0RC_1RA0LD_0LB0LC     2 98688     6 none         R    1    0     35 none         irregular     100 counter
    1RB0RB_1LC1LD_0LC1RA_0LD0RA     2 100003   15 1k+1         R  -11    0      1 none         irregular     100 counter
    1RB0RD_1LC0LB_1LD0LB_1RD0RA     2 33337    14 2k+1         L    0    0      1 none         irregular     100 counter
    1RB0RD_1LC0LC_1LD0LB_1RD0RA     2 33337    14 2k+1         L    0    0      1 none         irregular     100 counter
    1RB1LB_1LC0RD_0LB1LA_0LA1RA     2 77998   182 2k+1         R    1    0      5 none         irregular     100 counter
    1RB1LD_1RC1RB_1LC1LA_0RC0RD     2   832     9 -1k-1        R    2    1     94 10k+13       drift+affine   99 plain
    1RB1RD_1RC0LD_1LB0RA_1LC0LC     2 132132    5 none         L   -1    0      1 none         irregular     100 counter

The three questions the prompt asked, answered:

* **Is the wall monotone, and does it move by exactly one cell per cycle?**
  **13 of 19 move the wall by exactly ±1 per bounce cycle**, John's read
  verbatim.  Of the rest: `1RB1LD` (the champion) moves it by 2,
  `0RB1LC_1LC0RD` by −2, and four have no single dominant regime at all.
* **Is the cycle cost affine in the wall position?**  **8 of 19 are plain
  bouncers** — the cost is affine in the wall index over ≥90% of the phase's
  steps.  The remaining 11 are bouncer COUNTERS, and §7 measures what they
  count.
* **The turnaround configurations, indexed by the wall.**  On the plain 8 they
  are exactly `pre ++ rep u k ++ post` in the wall index.  On John's exemplar,
  inside one macro phase, measured:

      R-turn:  (StB, rep [S1] (3k+3), S1, rep [S1] (K-k))
      L-turn:  (StD, [],              S0, rep [S0] (3k+1) ++ rep [S1] (K-k))

  — one index growing, one shrinking, which is why the plain
  single-insertion fit reports the left side of the L-turn as "no family":
  it is a genuine TWO-index side, and the reader says so rather than
  forcing it.  That two-index shape is exactly `wM a r` below.

## 4. The macro ANCHOR: all 19 do rest, and it is not a word

The single most useful measurement of the wave, and the reason eight waves of
enumeration came back empty.

**Every one of the 19 rests, once per macro phase, at a configuration with the
head just off one end of the written region and NOTHING on the other side.**
`bouncecert.py --spec S --anchors`, and in the `--all` table:

    spec                           st  block law  blocks                kind    the last one
    0RB0LD_1LA1LC_0LD0LC_1RD1RB    B   x3         0, 3, 9, 27, 81       solid   1^81
    0RB0RB_1LA1LC_0LD0LC_1RD1RB    B   x3         0, 3, 9, 27, 81       solid   1^81
    0RB1LA_1LA1LC_0LD0LC_1RD1RB    B   x3+3       0, 3, 12, 39, 120     solid   1^120
    0RB1RC_1RC0LB_0RD0RC_1LD1LA    A   x3         9, 27, 81             solid   1^81   (mirrored)
    1RB1LD_1RC1RB_1LC1LA_0RC0RD    AD  none       3, 8, 17, 32, 57, 98  solid   1^98
    1RB---_1LC0RB_1LD1RB_1LC1RB    B   1k+1       1, 2, 3, 4, 5, 6      shaped  0^j 1
    1RB---_1LC1RD_1LB1RD_1LB0RD    BD  1k+1       1, 2, 3, 4, 5, 6      shaped  0^j 1
    1RB---_1LC1RD_1LB1RD_1LC0RD    BD  1k+1       1, 2, 3, 4, 5, 6      shaped  0^j 1
    1RB0RB_1LC1LD_0LC1RA_0LD0RA    B   1k+1       1, 2, 3, 4, 5, 6      shaped  0^j 1
    0RB1LB_1LC1RC_1RD0LA_0RC1RB    B   3k+3       3, 6, 9, 12, 15, 18   shaped  100011000110001100000000001
    1RB1LB_1LC0RD_0LB1LA_0LA1RA    AB  none       1, 3, 6, 9, 12, 15    shaped  100000000000011000110001
    1RB0RD_1LC0LB_1LD0LB_1RD0RA    AB  none       1, 5, 7, 9, 11, 13    shaped  1001111111111111110
    1RB0RD_1LC0LC_1LD0LB_1RD0RA    AB  none       1, 5, 7, 9, 11, 13    shaped  1001111111111111110
    0RB0RD_1LC1RB_1RA0LC_1LB0LC    BD  none       0, 2, 4, 5, 6, 9      shaped  11111111111111111110111111
    0RB0RD_1LC1RB_1RA0LC_1LD0LC    BD  none       0, 2, 4, 5, 6, 9      shaped  11111111111111111110111111
    0RB1LC_1LC0RD_1RD0LC_1LA1RB    C   none       3, 4, 7, 8, 13, 14    shaped  0^10 1^...
    0RB1LC_1LC1RD_1LA0LC_0RD1RB    A   none       2, 4, 7, 9, 15, 17    shaped  1^11 0 (110)^...
    1RB0RB_1LC0RC_1RA0LD_0LB0LC    BC  none       1, 5, 14, 29, 41, 51  shaped  1^...
    1RB1RD_1RC0LD_1LB0RA_1LC0LC    BCD none       3, 8, 28, 32, 70      shaped  1^...

**A perfectly good anchor family exists on every row.**  What does not exist
is a family of the shape every reader in this tree looks for,

    Cc p = (q, E p ++ tail, S0, far)

with `E` a digit alphabet, because the resting configuration is not a digit
word — on five rows it is a SOLID BLOCK, whose "value" is a length and not a
numeral, and on the rest it is a fixed shape whose only varying part is one
run length.  This is a REPRESENTATION gap, exactly like WAVE29 §2a's
`LSTOP` gap one level up, and not a search gap.  Widening the alphabet table
cannot close it; indexing the family by the wall does.

## 5. The three `1RB---` rows: `BounceGlue.EraseFill`, QHBound

Done first, as the prompt ordered, and they validated the whole route in one
sitting.  `StA`'s `S1` transition is undefined, so `StA` fires once at
configuration index 0 and the other three states are closed under the table:
they genuinely quasihalt, and the tier is `QHBound` via
`LapGlueAbs.glue_qh_abs`, never `glue_neverqh`.  `WrapBc_R.v` is the
precedent and the shape is the same one level simpler.

The three-state core, with the roles READ OFF THE TABLE and never assigned
(`bouncecert.roles`): one **eraser** `E` sweeps right over ones writing zeros
(`E1 -> 0RE`) and turns at the blank frontier (`E0 -> 1LX`); two **fillers**
`X`, `Y` sweep back left over the zeros writing ones and ALTERNATING with
each other (`X0 -> 1LY`, `Y0 -> 1LX`); a one turns them back
(`X1 = Y1 -> 1RE`).  The alternation is a parity fact the sweep carries and
nothing downstream reads, which is what `fill_sweep`'s existential over
`{X, Y}` expresses.

    mkB j = (E, (repeat S0 j ++ [S1], S0, []))

— the head on the blank frontier, `j` erased cells behind it, the surviving
wall cell at the far end.  One bounce is

    mkB (S i)  -->  mkB (S (S i))   in exactly 2*i+5 steps

so the macro lap IS the micro lap, there is no inner phase, and the whole
machine is one `csteps` chain.  All three boot at index 4 and take
`QHBound 1`, lifted to the census tier by `qhbound_mono`.

Role assignment differs between them — the eraser is `StB` on the first and
`StD` on the other two — and the abstract section does not care.  The two
`_1LB0RD` / `_1LC0RD` rows differ in ONE transition (which filler the
frontier turn enters) and, as the prompt predicted for such pairs, the second
boarded with no new work.

## 6. The wall-bounce class: `BounceGlue.WallBounce`, `glue_neverqh`

`*_1LA1LC_0LD0LC_1RD1RB` with row A one of `0RB0LD`, `0RB0RB`, `0RB1LA` —
three rows that differ ONLY in row A, and John's exemplar is the first.  Here
the tape is one solid block with the head inside it, the wall IS the head's
own column, and it marches out one cell per bounce while the block grows by
two on the far side:

    wA n   = (B, (repeat S1 n, S0, []))            head just off the near end
    wM a r = (B, (repeat S1 r, S1, repeat S1 a))   head inside: r of rebuilt
                                                   run behind, a of wall ahead

    wM (S a) r  -->  wM a (r+3)     in exactly 2*r+5 steps
    wM 0     r  -->  wA (r+3)       in exactly 2*r+5 steps

**The terminal is the same derivation as the bounce, read at `a = 0`** —
which is why they cost the same, and why one lemma (`wrun`, stated over an
opaque right tail `X`) proves both.  That was not designed; it fell out of
reading the landing off the machine rather than assuming it, and it halved
the section.

The only thing that differs across the three machines is the COLLAPSE, the
one place `StA` appears: it walks the solid block from its near end to its
far end **leaving the tape unchanged** (each cell is cleared and rewritten),
at 3, 5 and 1 steps per cell respectively, and a fixed tail turns the walk
into the first bounce:

    wA n --> wM (n-2) 3   in 3n+2 steps   (0RB0LD)
    wA n --> wM (n-2) 3   in 5n+2 steps   (0RB0RB)
    wA n --> wM (n-1) 3   in  n+7 steps   (0RB1LA)

Composed with `a` bounces the macro lap is `wA n --> wA 3n` on the first two
and `wA n --> wA (3n+3)` on the third — block sizes 3, 9, 27, 81, … and
3, 12, 39, 120, ….  Every state recurs inside one lap (`StB` at index 0,
`StA` at 1, `StC` and `StD` inside the first bounce), so the closer is
`LapGlue.glue_neverqh` directly: Bounce_8's pattern on a family indexed by
the wall instead of by a counter.

`bouncecert.wroles` reads `(Bq, Cq, Dq)` off the table — `Bq` turns at the
wall, `Cq` erases the run leftward with a self-loop, `Dq` fills it back
rightward — and refuses any machine whose roles do not land on
`(StB, StC, StD)` in that order, because the board's visit case-split is
written in state order.  That restriction costs exactly one row, §7's
`0RB1RC`.

### 6b. The same class, mirrored: `0RB1RC_1RC0LB_0RD0RC_1LD1LA`

Anchor `(StA, ([], S0, repeat S1 n))`, blocks 9, 27, 81 — §6's `x3` macro law
with the block on the RIGHT, so every lemma runs on the mirrored table and
`Mirror.mirror_never_qh` transfers the conclusion back (the wave-9 route, no
new theory).  Its bounce and terminal are bit-for-bit §6's and
`BounceGlue.WallBounce` proves them unchanged; its roles are
`(Bq, Cq, Dq) = (StA, StC, StD)` with `StB` the drift, which the section does
not care about.

**One measured thing differs, and it is one cell.**  Its wall turn writes
`S0` where §6's writes `S1`:

    §6   tm Bq S0 = 1 L Aq      the drift walks the block with the head ON it
    §6b  tm Bq S0 = 0 L Aq      the drift walks it with the head in the GAP

so the ripple is `(Bq, (S1 :: S1 :: L, S0, R)) --> (Bq, (S1 :: L, S0, S1 :: R))`
against §6's `(Aq, (S1 :: L, S1, R)) --> (Aq, (L, S1, S1 :: R))` — and note
the PEEL: the step that turns the walk around reads the cell below the head,
and the un-peeled form does not name it, so the sweep does not derive without
one unit peeled into the prefix.  The standing lesson at the smallest possible
scale, four waves running.

Collapse `wA n --> wM (n-2) 3` in `5n+2` steps, the same law as `0RB0RB`'s.
The board is a second template (`bouncecert.wemit2`), not new theory; the
emitter reads the discriminator off the table and refuses rather than guessing.

## 7. What did not board, measured

### 7a. `1RB0RD_1LC0LB_1LD0LB_1RD0RA` and `_1LC0LC_` are GRAY-CODE COUNTERS

**This corrects a ranking made earlier in this same wave.**  On the strength
of their turnaround signature — left turnaround PINNED at column −3, right
turnarounds running the ruler sequence 1, 3, 1, 5, 1, 3, 1, 7, … — these two
were ranked as bouncer counters needing `MeasureGlue`.  Measured off an
absolute-coordinate dump, they are not bouncers at all.  The ruler sequence
was real; it is a Gray code's carry depth, not a nested bounce.

The dump (`spacetime.py --lo -6 --hi 14`) shows bits on ODD columns only,
every even column blank at every rest, and the head resting at column −1 —
inside the word, on its own blank cell.  Decoding the word above that cell,
MSB at the far end:

    v(k) == 2 * gray(k+1)            33335 / 33335   both machines
    wall-adjacent bit == k mod 2     33335 / 33335   both machines

exact, no exceptions, over a 400k-step replay (`gray n = n XOR (n >> 1)`).
Taking the EVEN sub-family (`k` odd, `p = (k+1)/2`) makes the wall-adjacent
bit constant and the word exactly `GpCounter.Gp p = bits (gray (2p))` —
the tree's own wave-13 Gray fixpoint — written one bit per two cells:

    Cc p = (StB, ([S0; S1], S0, exp0 (Gp p)))      exp0 x = S0 :: x :: nil

verified cell-for-cell against the simulator at `p = 1..40`.  **And the lap is
AFFINE in the carry index**: measured cost `4j + 20` where `j` is the number
of trailing ones of `p`, i.e. `MonoCounter.cview`'s own `j` —

    j = 0 1 2 3 4        cost = 20 24 28 32 36

so `LapDecider` expresses it as it stands.  This is John's wave-27 §4b read
("like a grey code where it counts up and down") landing on a second class,
and the machinery already exists: `theories/Counters/GpCounter.v` and
`tools/counters/emit_graycert.py`, whose docstring records that the Gray lap
is affine in the carry index and needs no new soundness surface.

`emit_graycert --spec` reports `no Gray anchor` on both, for two reasons that
are both representation, not search: its `Gp` is one cell per bit (these are
two, blank-interleaved), and it offers no fixed frame to the LEFT of the head
(these have `[S0; S1]`).

**The build, specified.**  `GpCounter`'s three decomposition lemmas
(`cview_some_G`, `cview_some0_G`, `cview_none_G`) already do the Gray
arithmetic; push them through the interleave `dbl (a :: w) = S0 :: a :: dbl w`
(which distributes over `++` and sends `rep [S0] j` to `zz j`, the run of `j`
blank PAIRS) and the lap becomes three concrete runs.  All three are verified
against the raw simulator at `j = 0..8`, with the tail OPAQUE where the lemma
says it should be, and the costs are exact:

    branch          run                                                   cost
    ----------------------------------------------------------------------------
    cview (S j,None)  (Q,(F,S0, S0::S1::zz j ++ [S0;S1]))
                   -> (Q,(F,S0, S0::S0::zz j ++ [S0;S1;S0;S1]))          4j+24
    cview (S j,Some)  (Q,(F,S0, S0::S1::zz j ++ S0::S1::S0::x::Y))
                   -> (Q,(F,S0, S0::S0::zz j ++ S0::S1::S0::negs x::Y))  4j+24
    cview (0,  Some)  (Q,(F,S0, S0::S0::S0::x::Y))
                   -> (Q,(F,S0, S0::S1::S0::negs x::Y))                     20

with `Q = StB` and `F = [S0; S1]`; `Y` is opaque on the two interior branches
and the overflow branch runs against blank, exactly as `GpCounter`'s lemmas
predict.  `negs` is `GpCounter`'s own single-cell flip.  Note the overflow
branch's [j] is the LEMMA's [j], one less than the count of trailing ones —
mixing the two is what made the first attempt at these runs miss by 4 steps.

Everything else is the pattern §5 and §6 already use: a sweep induction over
`zz j`, three branch lemmas, `LapGlue.glue_neverqh`.  **This is the next
wave's first item, ahead of everything else in §7.**

The two rows are one class in the useful sense — same anchor family, same
`4j+20` lap law, same 33,335 rests, same decode — but NOT the same machine:
they differ in `C1` (`0LB` vs `0LC`), that transition IS exercised, and their
trajectories diverge at step 21.  So the second is a genuine second board, not
a duplicate, and it should be checked rather than assumed once the first
lands.

### 7b. The two rows whose macro anchor is arithmetic

    0RB1LB_1LC1RC_1RD0LA_0RC1RB    blocks 3, 6, 9, 12, 15, 18, ...   (+3)
    1RB1LB_1LC0RD_0LB1LA_0LA1RA    blocks 1, 3, 6, 9, 12, 15, ...    (+3)

The macro index is arithmetic, not geometric, so the anchor family is
`Cc p = shape (3*p)` with no `Fixpoint` at all — cheaper than anything §6
needed.  What stops them today is that their macro lap is not one regime:
their phases hold ~180 turnarounds each with no single dominant column step.
They were measured the way §7a was, and the answer is a clean NEGATIVE:
over every blank-head rest family (the three largest have 262, 204 and 202
members), decoding at stride 1, 2 and 3, at every base offset, in both
directions, **nothing gives a run of 8 consecutive values and nothing matches
`gray(k)` or `2*gray(k)`.**  So they are not counters under any of the reads
that worked elsewhere in this bucket, and the +3 macro law is the only
regularity in hand.  They are also NOT a mirror pair despite identical family
sizes — their tape-width signatures diverge — so they are two rows, not one.
The next probe worth running on them is a 3-cell digit alphabet, since +3 per
macro phase is what a 3-cell digit would look like.

### 7c. `0RB0RD_1LC1RB_1RA0LC_1LB0LC` and `_1LD0LC` — John's "bouncer counter"

Wave-27 §4b's third read, and the measurement agrees with it exactly.  The
phase is a rightward DRIFT of period 3 interleaved with occasional long left
sweeps.  The longest cycle in phase `k` costs 9, 11, 15, 23, 39, 71, … —
**differences 2, 4, 8, 16, 32, so the envelope is `2^k + 7`**.  That is a
DOUBLING inside the macro phase: a genuine bouncer counter, and the clearest
`mrun` customer in the bucket.  The two rows differ in one transition, measure
identically down to the step, and are one class.

### 7d. The rest

`0RB1LC_1LC0RD_1RD0LC_1LA1RB` (wall step −2, an affine tail covering 0% of
the phase), `0RB1LC_1LC1RD_1LA0LC_0RD1RB` (anchor `1^11 0 (110)^k`, blocks
2, 4, 7, 9, 15, 17 — an alternate-octave pattern like WAVE26 §8b's register),
`1RB0RB_1LC0RC_1RA0LD_0LB0LC` (phase envelopes 8, 15, 27, 35, 43, 67 — no
clean law under either segmentation; measure it again before designing for
it), `1RB0RB_1LC1LD_0LC1RA_0LD0RA` (macro anchor
`0^j 1`, blocks 1,2,3,…, the §5 shape but with all four states live), and
`1RB1RD_1RC0LD_1LB0RA_1LC0LC`.

**`1RB0RB_1LC1LD_0LC1RA_0LD0RA` is the bucket's one true `MeasureGlue`
customer.**  Its macro anchor is literally `mkB j` — §5's family,
`(StB, (repeat S0 j ++ [S1], S0, []))`, blocks 1, 2, 3, … — but its lap is not
§5's `2i+5`.  Measured:

    mkB j --> mkB (j+1)   in   2^(j+2) - 1 steps
    j =  1   2   3   4    5    6
    n =  7  15  31  63  127  255

so the lap runs a COMPLETE binary count over the `j` cells it just cleared,
and the dump shows exactly that: the head clears the region, then walks it
building `11`, `011`, `101`, `111`, … before the frontier advances.  That is
`MeasureGlue.mrun` with the abstract state = the inner word and
`mu = BounceCounter.cval` (the value of the complement, "each increment
decrements it by exactly one" — that file's own words), and it is the first
row in this bucket that genuinely needs it.  The macro family is already
written: `BounceGlue.mkB`.

### 7e. Deferred, per the prompt

`1RB1LD_1RC1RB_1LC1LA_0RC0RD` (the champion) and
`0RB1LC_1LC0LC_0RD1LA_1RD1RB` are deferred to stable hardware.  The champion
is measured anyway and is a PLAIN bouncer — wall step 2, cost `10k+13`,
coverage 99%, solid-block anchors 3, 8, 17, 32, 57, 98, 167 — so when it is
taken it should be cheap.

## 8. Do-not-retry, extended

* **Searching this bucket for a digit-alphabet anchor family.**  Re-confirmed
  from the other side: the resting configurations ARE regular and ARE a
  family (§4), they are simply not digit words.  On five rows the rest is a
  solid block of ones, whose "value" is a length; a numeral alphabet cannot
  express a length.  Do not widen `ENCDATA`; index the family by the wall.
* **Assuming the bucket needs `MeasureGlue`.**  Measured: 8 of 19 are plain
  bouncers whose bounce count is explicit in the anchor, all 7 boarded here
  needed plain induction only, and two more (§7a) are not bouncers at all but
  ordinary affine Gray-code counters.  Reach for `mrun` when the phase's cost
  sequence fails the affine fit WITH COVERAGE (§2), not before.
* **Reading a machine's MECHANISM off its turnaround signature.**  MEASURED
  AND REFUTED this wave, on this wave's own ranking: `1RB0RD_1LC0LB_*` has a
  pinned wall and a ruler-sequence turnaround pattern, which reads as a nested
  binary count inside a bounce.  It is a Gray-code counter with no bounce in
  it at all, and one absolute-coordinate dump said so.  The turnaround
  sequence tells you the machine bounces; it does not tell you what it is
  counting.  Dump the tape.
* **Ranking a regime by how many cycles it holds.**  Measured: on the rows in
  §7c the drift ripple is 3,199 cycles and the bounce is a handful, and
  ranking by run length picks the drift every time.  Rank by the STEPS the
  regime accounts for.
* **Reading an affine suffix of a phase's cost sequence as the phase's law.**
  Measured: `0RB1LC_1LC0RD` has an exactly affine suffix of 127 cycles
  covering 0% of the phase.  Always report the coverage.
* **Decoding the two `+3` arithmetic rows (§7b) at stride 1, 2 or 3.**
  MEASURED AND REFUTED: every blank-head rest family, every base offset, both
  directions, no consecutive run of 8 and no `gray` match.  Try a 3-cell digit
  before anything else there.
* Standing: everything in WAVE29 §5, WAVE28 §4, WAVE27 §5, WAVE26 §6,
  WAVE25 §6, WAVE24 §7, WAVE18 §5, WAVE16 §5.

## 8b. The bucket, re-ranked for the next wave

1. **The two Gray rows (§7a)** — the build is specified to the exact run,
   cost and opacity of all three branches, and `GpCounter` does the
   arithmetic.  Two boards, no new theory.
2. **`1RB0RB_1LC1LD_0LC1RA_0LD0RA` (§7d)** — the one true `MeasureGlue`
   customer, macro family already written (`BounceGlue.mkB`), lap
   `2^(j+2)-1`, measure `BounceCounter.cval`.  One board.
3. **`0RB0RD_1LC1RB_1RA0LC_1L*0LC` (§7c)** — John's bouncer counter, envelope
   `2^k+7`, the second `mrun` customer.  Two boards, one class.
4. **The `+3` pair (§7b)** and the four rows in §7d — measure first; the
   stride-1/2/3 decode is already refuted on the `+3` pair.
5. Deferred (§7e): the champion and `0RB1LC_1LC0LC_0RD1LA_1RD1RB`.

## 9. Standing lessons, confirmed again

* **MEASURE THE BUCKET BEFORE DESIGNING FOR IT.**  The prompt predicted "no
  new library Coq" and asked that it be checked early; it was, and it held.
  The reader also refuted a design the bucket's name invites — that these
  machines have no anchor at all.  They all have one.
* **READ THE LANDING OFF THE MACHINE.**  The `WallBounce` section is half the
  size it was first drafted at, because the terminal turned out to be the
  bounce read at `a = 0` rather than a separate derivation.  That is visible
  only in the measured configurations, never in a failure print.
* **Peel before anything else, still.**  Both sections' sweeps are stated
  with one unit peeled into the prefix (`wce` destructs `r`, `bce`'s `r = 0`
  case is the head landing straight on the wall), and neither derives
  otherwise.
* **A one-row difference is one class.**  Both predicted pairs held: the two
  `1RB---_1LC1RD_1LB1RD_*` rows and the three `*_1LA1LC_0LD0LC_1RD1RB` rows
  boarded off the same section with only their collapse differing.  The
  `0RB0RD_1LC1RB_1RA0LC_1L*0LC` pair measures identically down to the step
  (§7c) and will board together.
