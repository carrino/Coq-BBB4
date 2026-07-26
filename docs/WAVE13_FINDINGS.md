# Wave-13 — the emitter era ends: one checker, 119 boards, and a named next build

_Branch `claude/lapdecider-residue-reduction-989ggx`, off merged wave-12.  This
wave finished `theories/Checkers/LapDecider.v`, made certificate DERIVATION
mechanical, and boarded 119 machines with it.  Read §4 (what this wave got
wrong) and §6 (the next build) before starting anything._

## 1. Scoreboard

| | |
|---|---:|
| boards this wave | **119** (`LAPC_*`, all through the ONE checker) |
| `D_remaining` | 1,385 → **1,266** |
| frozen rows settled | 3,890 / 5,156 (**75.4%**) |
| new soundness surface | `LapDecider.v` + `LapCertGlue.v`, both **axiom-free** |
| board axiom footprint | `functional_extensionality_dep` only (sampled 6, plus every board compiled) |
| closeout | `audit.py` OK — tables partition the frozen list exactly |
| census | `census_cache --check` = MATCH at every commit; `theories/Census/` untouched |

The 119 break down `Jp/mirror` 66, `Jp` 23, `Ip/mirror` 18, `Ip` 3, plus 9
hole-machines re-derived after a filename fix.

**The point is not the 119.**  It is that a machine now costs a SEARCH, not a
session: `tools/counters/emit_lapcert.py --list FILE --emit` derives, validates
and compiles a board unattended.  Waves 8-12 spent five hand-written emitters
on ~500 boards.

## 2. The build

Full design in `docs/LAPDECIDER.md`.  In one paragraph: a symbolic tape side is
`pre ++ rep u (a*j+b) ++ post ++ X` with `X` an OPAQUE TAIL (the counter bits
above the carry) universally quantified, so one chain covers every `p` in a
branch at once.  A step language of framed windows, open-edge windows, the two
`WTape` cycles, block-boundary rotations and a block-offset fold is run by
`srun`; `srun_sound` turns a successful symbolic run into a concrete `csteps`
for every `j` and every tail; `lap_of_run`/`vis_of_run` feed `glue_neverqh`.

`LAPC_1RB1LA_1LC1RD_1LB1RA_0LA0RB.v` is the architecture proof — the same
machine as `ILS4_…`, whose hand board spent 9 window lemmas, 9 transported
phases and 2 assembled laps.  **24 of 25** sampled hand-emitted `ILS4_*` boards
re-derive automatically.

## 3. The build trap is closed

`tools/closeout/gen_stages.py` now computes the transitive in-tree dependency
closure of every board the stages `Require` and adds whatever is missing to
`_CoqProject` (`theories/Census/` excluded — its `.vo` are committed).
Verified by deleting a board AND its transitive dep `MonoCounter.v` and
watching both come back; and in production this wave, where it added all 114
new board files with no `No rule to make target`.

## 4. Three things this wave got wrong

1. **"A walled window is forced forward, so only the MAXIMAL cut matters."**
   False, and it cost the first search implementation: the last window of a lap
   must often stop SHORT so that a rotation can land the configuration on the
   anchor's syntactic form.  Making the window search target-aware turned 0
   chains into all of them.
2. **"Rotations can reach any equivalent representation."**  False in
   principle.  Rotations move a block BOUNDARY; they cannot change the count's
   constant offset `b`.  An overflow anchor is naturally REACHED as
   `uD ++ rep uD j ++ …` but STATED by `cview` as `rep uD (S j) ++ …`, and
   only the new `SFold` step reconciles them.
3. **"143 machines with no visit witness are rejects."**  False — John:
   *"qh is fine, we just need to know it qh before 32M."*  They are
   quasi-halters and a certified quiet bound boards them just as well.  See §6.

## 5. Where the residue actually stands

Of the 1,385 (measured over the whole list, not a sample):

| bucket | count | status |
|---|---:|---|
| boarded this wave | 119 | done |
| **no interior chain** | ~504 | anchor found, chain search failed — the biggest bucket, unanalysed |
| **no overflow chain** | ~371 | interior derives, overflow does not |
| **quasi-halting** (no visit witness) | ~143 | §6 — a real class with a real route |
| **no anchor** | ~149 | no `Ip/Jp/Kp/Dp/Mp` family at all |

The middle two buckets are where the next boards are.  **Do not template them
blind** — wave-12 §8: trace two or three members before templating, never one.

Note `Kp`/`Dp`/`Mp` are wired but produced almost nothing (`Dp` 6, `Kp` 1, `Mp`
0) — the encoding table is not the binding constraint; the chain search is.

## 6. The next build, precisely

The ~143 quasi-halting counters derive a LAP but have a state that genuinely
goes quiet.  Splitting them:

* **47** have `StA` targeted by NO transition, so its only visit is at
  configuration index 0 and `LapGlueQH.glue_qh` gives `QHBound 1` outright.
  Wired into the emitter; blocked in practice on a second quiet state (`StB`
  fires once at index 1 by the same argument) and on `mirrorize` not knowing
  the QH closing shape.  Both are small.
* **96** have `StA` targeted but fired only during the bootstrap.  The bound is
  `t0+1` where `t0` is the boot length, and it needs exactly ONE new fact:
  *the lap visits only states in `S`*.

That fact is computable from the chain — collect the states of every window
sub-step and every cycle unit run — but it needs a new soundness theorem,
because `wsteps_frame`, `cycL` and `cycR` currently state only their
ENDPOINTS.  The work is a "states visited" variant of each: roughly

    wsteps_states : wsteps bl br tm n c = Some c' ->
      (forall k c2, k <= n -> wsteps bl br tm k c = Some c2 -> In (fst c2) S) ->
      forall L R, ... every intermediate cstep state is in S

plus the same for the two cycles by the same induction they already use.  With
it, `QuietAfter tm q t0` follows for every `q` outside `S`, and `qhbound_mono`
lifts the bound to the census tier's 2000 — far inside the champion's 32.8M.

**This is the highest-value next item**: it converts a measured 143-machine
bucket, and it is one theorem, not one per machine.

## 7. Deferred, unchanged from wave-12

* Census fold-in (route B) — batch once on stable hardware; it is the only
  step that lowers `D_census`.
* The champion `1RB1LD_1RC1RB_1LC1LA_0RC0RD` (`exists B, QHBound B` + a 32.8M
  prefix) and the carry-shifted one-off `0RB1LC_1LC0LC_0RD1LA_1RD1RB`.
* The full `make closeout` COMPILE (`Closeout.vo`) needs the ~719-file board
  `.vo` closure, the documented ~85-minute one-time cost in a fresh container.
  `inventory.py` + `gen_stages.py` + `audit.py` all ran clean this wave and the
  numbers above come from them.

## 8. Do-not-retry, added this wave

* **Maximal-only window cuts in the chain search** (§4.1) — finds nothing.
* **Reaching an anchor's syntactic form by rotations alone** (§4.2) —
  impossible in principle, not a tuning problem.
* **mxdys' implementation** — John reports it is not available.  Stop asking;
  reconstruct from measurements (`WAVE9_FINDINGS.md` §7 is now closed out).
* **Widening the ENCODING table to buy boards** — `Kp`/`Dp`/`Mp` added this
  wave for 7 boards total.  The chain search, not the alphabet, is binding.

## 9. Five tape readings, four structural classes — and one hard architectural limit

_Added at the end of wave-13.  John read five machines out of the "no interior
chain" bucket; every reading converted into a measurement.  Two are mechanical
fixes to the emitter, two are outside the current model.  Hand-inspection is
now 20-for-20 across waves 8-13._

### 9a. `j = 0` vs `j >= 1` — mechanical, ~31% of the bucket

`0RB---_1LC1RB_0RB1LD_1LA0LC` — *"msb on the right and a 1 to the right of each
bit"*, i.e. `Mp`.  The reading CONFIRMED the emitter's anchor and frame
(snapshots decode as `Mp p ++ [S1]`), which localised the bug precisely: at
`j = 0` the repeated block vanishes, so the cell to the head's left is
ambiguous (block's first cell vs `post`'s first cell) and the search stalls
with no legal move at step 0.

Splitting the interior branch derives both cases immediately:

    j = S j'   [SWin 2; SCycL 2 0; SWin 2; SCycR 2; SWin 2]   4j'+6
    j = 0      [SWin 2]                                        2

Measured over 100 of the 517: **31 unlock**.  No new soundness surface — the
glue gains a `destruct j`.

### 9b. Period-`m` traversal (the double-pass carry) — mechanical, ~7% more

`0RB0LA_0LC1RD_0RD1LC_1LA1RB` — *"when doing the carry it alternates B then D;
the first time it hits with B it just goes back without flipping, then D
actually flips it."*  A two-pass carry makes the traversal period 2 in the
CELLS, so the cycle unit is two cells wide while the block unit is one, and
nothing matches.

Fix: re-index `j = m*i + r` and use `u^m` as the block unit,

    rep u (m*i + r) = rep (u^m) i ++ rep u r

which the EXISTING checker expresses (it is just a different starting
`sside`).  At `m = 2` both parity classes derive, and the two-pass structure
is visible in the chain — two `SCycL`/`SCycR` sweeps:

    j = 2i    [SWin 2; SCycL 2 0; SWin 2; SCycR 2; SWin 4;
               SCycL 2 0; SWin 2; SCycR 2; SWin 2]   8i+12
    j = 2i+1  [SWin 2; SCycL 2 0; SWin 4; SCycR 2; SWin 2]   4i+8

Measured: **4 more of 60**.  Smaller than the single example suggested.

### 9c. QUADRATIC laps — OUTSIDE the model, and the important one

`0RB0LA_1LA0LC_0RD1LC_1RB1RD`, `0RB0LA_1LA1LC_0RD0LC_1RD1RB`,
`0RB0LA_1LA0RC_0LD1RC_1RB1LD`, `0RB0LA_1LA1RC_0LD0RC_1LD1RB` — *"doing a carry
bit actually does many back and forths to get the bit set, so 1110 takes 3 back
and forths to get 0001."*  A space-time diagram shows the widening zigzag: one
round trip per carry bit.

All four have the SAME interior lap cost, measured on the raw simulator:

| `j` | 0 | 1 | 2 | 3 | 4 | 5 | 6 |
|---|---|---|---|---|---|---|---|
| steps | 2 | 6 | 12 | 20 | 30 | 42 | 56 |

Second differences constant 2, so **`lap(j) = (j+1)(j+2)`**.

**This is a hard architectural limit, not a search weakness.**  `sside` carries
its count as `a*j+b` and `srun` returns step counts as `ca*j+cb`; both are
AFFINE in `j` by construction, so a quadratic lap is not expressible and no
amount of chain search or step-language widening reaches it.  Closing this
needs one of:

* a quadratic count in the model (`sside` gains a `j^2` coefficient, and
  `cycL`/`cycR` gain a variant whose repetition count varies per iteration); or
* a NESTED chain — an inner cycle repeated `j` times whose own length grows
  with the iteration index.  This is the "three-level recursion" that
  `WAVE12_FINDINGS.md` §4.1 correctly rejected for the WALL family; it is real
  here, and the two claims do not conflict.

The wave-12 do-not-retry entry *"assuming affine-vs-exponential overflow is
uniform within a shape"* now has a sibling: **do not assume the INTERIOR lap
is affine either.**  `tools/counters/lapshape.py` segments laps by phase but
never measured cost-vs-`j`; it should.

### 9d. GRAY-CODE counters — a sixth word family, not a sixth digit alphabet

`0RB0LA_0RC1RC_1LD0LD_1LA1RB` — *"some bits seem inverted, or maybe it counts
up and down before doing a carry."*  Decoded: the tape word is `g(n)`, the
reflected-binary (Gray) code.

| word | binary | `gray^-1` |
|---|---:|---:|
| `11` | 3 | 2 |
| `011` | 6 | 4 |
| `101` | 5 | 6 |
| `0011` | 12 | 8 |
| `1111` | 15 | 10 |

`gray^-1` runs 2, 4, 6, 8, … — exactly consecutive.  `0RB0LA_1LA1RC_0RD1RD_1LB0LB`
(*"counts up, then down, then bumps the msb: 8->15->9, then 16->31->17, then
32"*) is the same thing with a paired step: `gray^-1` = 4,5, 8,9, 12,13, 16,17…

This is NOT a new digit alphabet.  `Ip/Jp/Kp/Dp/Mp` all encode the BINARY
expansion; a Gray word is a different function of `n` and needs its own
`GpCounter.v`.

**But it reuses `cview` verbatim, and it is AFFINE** — corrected after John's
follow-up reading (*"when it carries the msb it keeps the top 2 bits set: 12 ->
15 -> 9, then 24 -> 31 -> 17, then 48 -> 63 -> 33"*), which is exactly
`g(2^k) = 2^k + 2^(k-1)`, i.e. `g(8)=12`, `g(16)=24`, `g(32)=48`.

Writing `Gp p` for the Gray word LSB-first and `j` for `cview`'s carry index
(the trailing-ones count of `p`), VERIFIED for every `p` in 2..39:

    j >= 1:  Gp p        = rep [S0] (j-1) ++ [S1] ++ [x]  ++ T
             Gp (succ p) = rep [S0] (j-1) ++ [S1] ++ [~x] ++ T
    j  = 0:  the two words differ in cell 0 only

One repeated block, one flipped cell, same carry index — so the LAP IS AFFINE
and the existing `sside`/`srun` model expresses it unchanged.  What is needed
is only:

  1. `theories/Counters/GpCounter.v`: `Gp` plus those two lemmas, proved the
     same way as `cview_some_I`/`cview_none_I` (induction on `p`);
  2. one `ENCDATA` row, with the interior branch split on the extra bit `x`
     (two sub-cases) exactly as 9a splits on `j = 0`.

So Gray is a NEAR-TERM build, not new theory.  It also means the residue's
"weird" counters are two quite different things: Gray (affine, in-model) and
the round-trip family of 9c (quadratic, out-of-model).  Do not conflate them —
both were sitting in the same "no interior chain" bucket.

A constant-difference detector found **4 of 35** resistant machines as Gray,
and it MISSES the paired-step ones (`0RB0LA_1LA1RC_0RD1RD_1LB0LB` decodes as
Gray but was scored "neither"), so 4 is a floor, not an estimate.  Before
building `GpCounter.v`, re-run the detector allowing a PERIODIC difference
pattern rather than a constant one.

### 9e. Ranked consequence

1. Wire 9a + 9b into the emitter (mechanical, no new Coq, ~35% of the 517).
2. Build `GpCounter.v` + the Gray `ENCDATA` row (9d).  The decomposition is
   verified and affine; this is an implementation pass, not a design pass.
   Re-run the Gray detector with PERIODIC differences first to size the class —
   the constant-difference version scores paired-step Gray machines as
   "neither" and so under-counts.
3. Decide 9c: quadratic counts vs nested chains.  This is the first thing in
   five waves that the EXISTING theory genuinely cannot express, so it deserves
   a design pass rather than an implementation pass.

## 10. The overflow wall, and the alternating-frame hypothesis

### 10a. The overflow is now the binding constraint — measured

Wiring the `j = 0` split (§9a) moved **138** of the 517 "no interior chain"
machines past the interior and **0** all the way to a board: every one then
fails on the OVERFLOW chain.  Peeling the overflow block (`rep uS (S j) =
uS ++ rep uS j`, unconditional when `obS >= 1`) unlocked **0** of the 385 that
already had an interior.

| bucket | count |
|---|---:|
| interior derives, overflow fails | 385 |
| interior derives after the §9a split, overflow fails | 138 |
| **fail ONLY on the overflow** | **~523** |

So ~523 machines — essentially the whole remaining counter residue — are one
chain away from a board, and that chain is always the msb carry.  Any further
tape-reading should be spent there, not on interior laps.

### 10b. The hypothesis: the FRAME ALTERNATES with msb parity

John, reading `0RB---_0RC0LD_1LD1RC_0LA1LB`: *"a counter with 1's to the LEFT
of the bits when the msb is even and 1's to the RIGHT of the bits when the msb
is odd — when msb is 8 (2^3) it has a 1 to the right, when msb is 16 it has a 1
to the left."*

Marker-before vs marker-after is exactly the `Ip`/`Mp` one-cell frame shift
that `WAVE12_FINDINGS.md` §7 identified.  If the frame alternates with the
parity of the msb exponent, then it flips **precisely at the overflow**, since
the overflow is the increment `2^k - 1 -> 2^k` that grows the msb.

That would explain the §10a wall exactly and completely:

* the INTERIOR lap keeps the bit length fixed, so both sides of the lap are in
  the same frame — which is why every interior chain derives;
* the OVERFLOW lap crosses `2^k - 1 -> 2^k`, so its SOURCE and TARGET are in
  DIFFERENT frames — and `emit_lapcert` builds `B0` and `B1` from the same
  `ENCDATA` row, so such a lap is not merely hard to find, it is
  **unrepresentable**.

It also explains wave-12 §7's observation from the other side: an `Ip`
recognizer "half-fires" on these because half the anchors really are in the
`Ip` frame.

**Status: John's reading, not yet independently verified.**  A crude
frame classifier over that machine's snapshots was inconclusive (its
state-C words are all-ones prefixes, which satisfy both patterns trivially),
and the state-A snapshots this session caught were all of ONE bit-length
parity — consistent with the hypothesis but not a test of it.  **Verify before
building**: decode the anchor words at CONSECUTIVE bit lengths and check the
frame flips.  Wave-12 §4 is the standing warning about concluding structure
from a partial search.

### 10c. What it would take

Small, and inside the existing checker:

1. `emit_lapcert` learns an overflow branch whose SOURCE and TARGET come from
   different `ENCDATA` rows (`enc_src` / `enc_dst`).  `B0` from `enc_src`'s
   `cview_none_*`, `B1` from `enc_dst`'s — both lemmas already exist.
2. The anchor family becomes frame-alternating: `Cc p = (q, (W p ++ tail, S0,
   far))` with `W p` selected by the parity of `bitlen p`.  This is the only
   new Coq, and it is one fixpoint plus the fact that `bitlen` is constant
   across an interior lap and increments at an overflow.

No new soundness surface in `LapDecider.v`: `srun_sound` never sees the
encoding, only the symbolic sides.

If the hypothesis holds, this is the single highest-value build left — it is
addressed at ~523 machines, more than four times the 119 boarded this wave.
