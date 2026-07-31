# The three-state core rows (`1RB---_...`), and how to finish them

_Written 2026-07-31; §3's `StA` entry rewritten the same day when that row
boarded.  The 24 core rows whose `StA` has an undefined `S1` transition:
after step 1 they are THREE-state machines started on a tape carrying a
single `1`.  This is the map of that population — what they actually are,
what boarded, and what each survivor still needs.  Companion reading:
`COUNTER_CLOSEOUT.md` (the counter route in general), `WAVE34_REACHSTI.md`
(the previous session on these rows)._

## 0. The one fact that reorganises the population

**Thirteen of the 24 are boarded** (twelve on 2026-07-31 morning, then the
`StA` row; §3).

**The 24 rows are 9 sub-machines.**  `StA` fires once, at index 0, and 23 of
the 24 rows are the target of no transition, so everything after step 1 is
the `{StB, StC, StD}` sub-machine running on a tape with one `1` on it.  Up
to relabelling those three states, the 24 rows collapse to **nine** distinct
sub-machines (plus one row that does target `StA`):

| sub-machine (canonical) | rows | boarded | closer |
|---|---|---|---|
| `0LB1RC_0RD0RC_1LB1LD` | 3 | **3** | `Counters/Ter3Wall.v` |
| `0LC1RD_0LB1RD_1LB0RD` | 3 | **3** | `Counters/KpWallAlt.v` |
| `0LC1RB_0LB1RD_1LC0RD` | 3 | **3** | `Counters/KpWallScan.v` |
| `0LC1RD_1LB1RD_1LC0RD` | 1 | **1** | `Checkers/LapDecider.v` (nested) |
| `0LB1RC_1LB0RD_1LC0RC` | 2 | **2** | `Counters/Ter3WallB.v` |
| `0LB1RC_1LD0RC_1LB1RC` | 3 | 0 | — |
| `0LC1RD_1LB1RC_1LB0RD` | 3 | 0 | — |
| `0LC1RD_1LB1RD_1LB0RD` | 3 | 0 | — |
| `0LB1RC_1LB0RD_1LC0RD` | 2 | 0 | — |
| (targets `StA`) | 1 | **1** | `Machines/Counters/NLAP_1RB____1RC1LB_0LB1RD_0RA0RC.v` |

Two rows sharing a sub-machine differ **only in their bootstrap**: the entry
from `StA` lands in a different one of the three states, so the trajectory to
the first anchor differs while the lap does not.  That is why every closer
here is ROLE-PARAMETERISED (`qW`/`qC`/`qD` as `St` arguments) and why one
closer + one boot probe boards a whole row-group at once.  `tools/counters`
sibling scans looked for relabellings among *boarded* machines; the useful
question on this population is the relabelling classes of the population
itself.

## 1. What they are

All 24 are **wall counters growing rightward**: cell 0 holds a permanent `S1`
(the wall), the counter's digits live at cells 1, 2, … with the LOW digit
next to the wall, and the head bounces between the wall and the carry
frontier.  The head never visits a negative cell on any of the 24.

The natural anchor is therefore

```coq
Cc p = (q, ([], S1, <counter word>))
```

— the head sitting **ON** the wall cell, nothing to its left.  That anchor's
head symbol is `S1`, and until this session every anchor search in the tree
(`emit_interleave.derive_tail_best` and `_far`, and so
`emit_lapcert.anchors`) hard-coded `h == 0`.  One literal, and it hid the
whole population.  `emit_lapcert.py` now carries the head symbol as `HD`,
searched `S0`-first so no previously boarded row can change route, and
`anchors` proposes every family with a long consecutive-value run rather than
the single best-scoring one.  Regression: a 10-row sample of already-boarded
`LAPC`/`LAPQ`/`NLAP`/`PEEL` rows still derives 10/10, every one of them by
the same encoding and step law as before and none of them by the new `S1`
route.

## 2. The boarded five families

All five are `iqh` — `NonHalt /\ QHBound 2000 /\ QuasiHaltsSt` — **not**
`NeverQuasiHaltsSt`: `StA` fires once and never again, so these machines
genuinely quasihalt, with score 1.  `LapGlueQuiet.glue_qh_quiet` is the
closer in every case (`qa = StA`, `s0 = 0`), and its `AvoidRun` premise is
free from `ReachStI.inv_csteps_all` because the three roles are a total,
closed state set that excludes `StA`.

### `Ter3Wall.v` / `Ter3WallB.v` — base three (3 + 2 rows)

`tools/closeout/residue_map.tsv` calls these "EXP3": read at base 2 their lap
grows like `3^j`.  They are not base 2.  After the wall the tape is 2-cell
digits over `{00, 01, 11}` and the lap is `4j + 4` in the carry length —
`tools/counters/radix_infer.py` measured that over 10^4 consecutive anchor
snapshots a session ago; what was missing was the Coq side.

* `Counters/TernCounter.v` — base-3 numerals `tern`, the carry view `tview`
  (the run of low 2s), the word `Tw` over three digit words and a
  terminator, and TWO increments, because both occur in these rows:
  `tsucc` (no terminator: overflow writes a fresh digit 1) and `tsuccT` (a
  terminator sits past the top digit and the overflow carry clears it too,
  so the fresh digit is a 0).  `TerStep` packages what a lap consumes: one
  trichotomy in single cells, proved for both increments.
* `Counters/LapGlueIx.v` — `LapGlueQuiet` over an ARBITRARY index.  Neither
  it nor `LapGlue` uses arithmetic; `Pos.le` only carries the `p0 <= p`
  guard.  A base-3 counter has no `positive` to index by.

`Ter3WallB.v` is the same radix over a DIFFERENT alphabet — digits
`{00, 10, 11}`, and the increment writes its fresh `1` in the digit's first
cell (`00 -> 10`) where `Ter3Wall`'s writes it in the second (`00 -> 01`).
There the parity IS the branch: the outward clear alternates one cell at a
time and what stops it is the first clear cell, so a digit-0 stop leaves an
even run and a digit-1 stop an odd one.  Base 3's two interior branches are
therefore not two lap lemmas but the two parities of one, both `2k + 2` in
the run length.

### `KpWallAlt.v` / `KpWallScan.v` — the alternating return (3 + 3 rows)

`KpWallQH.v` (wave 34) closed the shape whose carry RIPPLE alternates between
two states.  These two are its siblings:

* **`KpWallAlt`**: the ripple is one state and the RETURN alternates.  The
  two return states agree at the wall, so the parity is invisible: the return
  lemma carries "the state is still one of the two" instead of naming it.
  Lap `2j + 6`, both branches exact.
* **`KpWallScan`**: the return alternates AND its two members DISAGREE at the
  wall — `qQ` bounces into the ripple, `qP` bounces into itself.  Lap
  `2j + 2` for even `j`, `2j + 4` for odd (`residue_map`'s "PARITY-AFFINE").
  The parity still never reaches the anchor: a `qP` bounce runs one cell out
  onto the counter's low cell, which an increment with `j >= 1` has just
  cleared, so `qP` turns straight back and hands to `qQ` at the same anchor.

**Why `Checkers/LapDecider.v` cannot take any of these six.**  Its `SCycL` /
`SCycR` steps require the unit run to return to the state it started in.  An
alternating sweep does so only every second cell, so no chain over a
`rep u (a*j+b)` block can express it.  A fixed 2-cell unit would cover only
even runs, and `j` is universally quantified.  This is a real expressiveness
gap, not a search gap — the alternative would be a state-SET in `sconf`,
which changes `srun_sound` and every step's soundness lemma.

## 3. The survivors, and what each needs

Measured with `tools/counters/radix_infer.py`, `nestscan.py`,
`radix_clock.py`, `fib_anchor.py` and by hand-reading traces.

> **Read this section to the end before acting on it.**  It is written in
> discovery order and the first half is superseded by the second: every
> "measured absent" below is a base-2 search, and the eleven rows it is about
> do not count in base 2.  The answer is at **"The anchor was never the
> problem.  Here it is."**

**The flat wall reading is measured absent — but read the caveat.**  A search
over the TRUE wall anchor (head at cell 0) for all four surviving
sub-machines, across anchor state, anchor head symbol, radix 2–4, digit width
1–3, terminator length 0–2 and 0–2 padding blanks past the top digit, finds
**no consecutive-value decode** on any of them.  The same search finds base 3
immediately on the two `Ter3Wall*` groups.

The caveat the `StA` row taught (§3 last entry) is NOT the one first written
here.  It is not that the anchor space is too narrow — it is that every scan
in the tree scores a family by its longest run of CONSECUTIVE VALUES, which a
NESTED counter supplies only inside one epoch.  Three searches have now come
back negative on these four sub-machines, and they are independent:

* the flat wall reading, above (head at cell 0, all the parameters listed);
* `tools/counters/carry_anchor.py`, the carry-straddling shape, with
  run-units `1`, `11`, `01`, `10`, `111` and eight digit-pairs — it finds the
  `StA` row instantly and none of these;
* `tools/counters/nestscan.py`, which drops the consecutive-value score
  entirely and asks only whether ADJACENT anchor words are related by an
  `Alph` increment.  On the `StA` row it reports `run = 255`.  On **all
  eleven** surviving rows the best stretch is 1 or 2 pairs at every anchor,
  and the anchor word grows at nearly every anchor instead of staying fixed
  inside an epoch.

So these eleven are not the `StA` row's shape wearing a different hat.  And
the reason all three searches miss is now measured, and it is not the anchor:

### **The eleven are not base 2.  They are FIBONACCI counters.**

`tools/counters/radix_clock.py` (new) reads a counter's radix with no anchor,
no word family and no alphabet: count, for each tape cell, how many writes
actually CHANGED it.  A cell of digit weight `r^k` toggles `~V / r^k` times,
so the ratio between the toggle counts of cells one digit apart IS the radix.
On **all eleven** rows:

```
ratio = 1.6180 = phi,  spread 0.00 across every digit,
raw counts 94432, 58362, 36070, 22291, 13776, 8514, 5262, 3252
             — and F(n) = F(n-1) + F(n-2) holds on them exactly.
```

Calibration, against rows whose radix is already a theorem in this tree:

| row | measured | proved by |
|---|---|---|
| `1RB---_0LC1RD_0LB1RD_1LB0RD` | base 2, spread 0.00 | `Counters/KpWallAlt.v` |
| `1RB---_1RC1LB_0LB1RD_0RA0RC` | base 2 (stride 2) | `NLAP_1RB____1RC1LB_…` |
| `1RB---_0LB1RC_0RD0RC_1LB1LD` | base 3, spread 0.00 | `Counters/Ter3Wall.v` |

Independent cross-check on the tape width: at `t = 2·10^5` these rows have a
23-cell tape and `~4.7·10^4` low-digit toggles; `phi^23 ≈ 6.4·10^4` is the
right order, `2^23 ≈ 8.4·10^6` is wrong by two.

That is the whole explanation of §3's negative searches.  **Every alphabet in
`theories/Counters` is base 2** (plus `Ter3Wall`'s base 3), and every anchor
scan decodes words in one of them, so a Fibonacci counter's words cannot
decode to consecutive values at ANY anchor — which is exactly the "sparse
self-similar set" `1 | 3 | 6,7 | 12,13,15 | …` recorded below.  It is
wave-35's base-3 lesson a second time, one notch further out: *part of the
residue is not base 2, and this part is not even an integer base.*

### The anchor was never the problem.  Here it is.

Acting on that reading, `tools/counters/fib_anchor.py` (new) runs the ordinary
anchor scan — same anchor space, same consecutive-value score — with the
weight ladder `1, 1, 2, 3, 5, 8, …` in place of `1, 2, 4, 8, 16`.  **All
eleven rows decode to `0, 1, 2, 3, 4, …` at an ordinary flat anchor**, ten
under `F(1,1)` and one (`1RB---_1LC1RB_0LB1RD_1LC0RD`) under `F(1,2)`, each
scoring the full 4,000-word cap.  Two of them checked exhaustively:

| row | anchor | transitions | consecutive-value failures |
|---|---|---|---|
| `1RB---_0LB1RC_1LB0RD_1LC0RD` | `StB`, head `S1`, word right, left empty | 57,300 | **0** |
| `1RB---_0LC1RD_1LB1RC_1LB0RD` | `StB`, head `S0`, word right, 1 cell left | 21,890 | **0** |

The per-row anchor and ladder for all eleven are recorded in
`tools/counters/FIB_ELEVEN.txt`, so the next session does not have to re-run
the scan.

And the words are the ones this file already recorded — `(empty), 1, 11, 011,
111, 0011, 1011, 1111, 00011, …` — the very sequence called "plain `Kp` words
visited at a sparse self-similar set".  Weighed `1,1,2,3,5,8,…` they are

```
0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, …
```

with nothing skipped.  **The sparse set was a base-2 misreading and nothing
else.**  The anchor sees every increment, it always did, and four waves of
"WHERE is the anchor" were asking the wrong question.

Control, so the score is not an artefact of offering more ladders: plain
base 2 is one of the ladders `fib_anchor.py` tries, and the one row in this
population that genuinely IS base 2 — `1RB---_1RC1LB_0LB1RD_0RA0RC`, boarded
above — scores **4 of 4000** here against the eleven's **4000 of 4000**.

### What these eleven now need

Not an anchor search, and not `nestcert`'s inner head symbol.  A **Fibonacci
numeral module** — the analogue of `Counters/TernCounter.v` one notch out:

* `Fib v` over `positive` (or `nat`) with the encodings measured above.  Note
  the two rows sampled use DIFFERENT digit words (`1, 11, 011, 111, 0011, …`
  versus `1, 11, 101, 111, 1101, 1011, 1111, …`), so this is an alphabet
  family like `Alph_*`, not a single fixpoint.
* the increment, which is NOT a fixed-radix roll-over: `MonoCounter.cview`
  splits `p` at its run of trailing ones over base 2 and does not apply.  The
  carry here folds `F(k) + F(k+1) -> F(k+2)`, so the view has to name the
  Fibonacci-carry position instead.
* then the ordinary route: `LapDecider` chains at the anchor above, and
  `LapGlueIx`-style glue (a Fibonacci counter has no `positive` to index by,
  exactly as base 3 did not).

**And the lap law is already measured, and it is AFFINE.**  Let `r` be the
index of the highest digit the increment rewrites.  On both rows sampled the
step gap is **single-valued in every observed class** and affine in `r`:

| row | law | classes | laps |
|---|---|---|---|
| `1RB---_0LB1RC_1LB0RD_1LC0RD` | `2r` (one branch) | 22 | 38,201 |
| `1RB---_0LC1RD_1LB1RC_1LB0RD` | `2r + 4` odd `r`, `2r + 8` even `r` | 19 | 21,890 |

No class carries two different gaps.  Nothing super-affine, and at most a
parity split — the same two-branch shape `Ter3WallB` already handles.  So once
the numerals exist these are ORDINARY `LapDecider` chains, not nested ones:
the same shape as every `Kp` board in `theories/Machines/Counters`, in a
different base.  (The "lap is super-affine `6, 16, 36, 82, 196`" reading
recorded below was measuring the base-2 misreading, where consecutive wall
visits span a whole sub-epoch.)

### `0LB1RC_1LB0RD_1LC0RD` (2 rows), `0LB1RC_1LD0RC_1LB1RC` (3 rows)

`residue_map` reads both as `Dp` (each bit in two identical copies) and calls
them "HIGHER".  That label is a PARTIAL fit: sampling
`1RB---_0LB1RC_1LB0RD_1LC0RD` at the wall gives the words

```
(empty), 1, 11, 011, 111, 0011, 1011, 1111, 00011, 10011, 11011, 01111, …
```

which are plain `Kp` words — a binary counter, low bit at the wall, top bit
as terminator — and only the subsequence that happens to pair up as
`00`/`11` looks like `Dp`.  [2026-07-31: those words ARE the tape, but
reading them as base-2 `Kp` is the misreading — `radix_clock.py` says the
radix is `phi`, so what looks like a binary counter skipping values is a
Fibonacci counter read in the wrong base.]  What is wrong is
that **the wall is not where every increment shows**: those words decode to

```
1 | 3 | 6,7 | 12,13,15 | 24,25,27,30,31 | 48,49,51,54,55,60, …
```

— a sparse self-similar set, each block twice the previous.  Consecutive wall
visits are therefore separated by a whole sub-epoch, which is why the lap
measured at that anchor is super-affine: `6, 16, 36, 82, 196` steps at carry
lengths `0..4`.  The open question is not "is it a counter" but WHERE the
anchor makes every increment visible.  A lap that
grows like that is a NESTED counter — the outer increment runs an inner one —
which is what `Counters/NestedLap*.v` and `nestcert.py` exist for.  The
nested route in `emit_lapcert.py` is currently `S0`-anchor-only (it is
refused outright when `HD = 1`, see the guard): `nestcert` states its INNER
anchor with a literal `S0` head of its own, and that head is genuinely
independent of the outer one.  Threading a second head symbol through
`nestcert` is one sized piece.

[2026-07-31, after the `StA` row boarded.]  **Do not start there.**  That row
needed no second head symbol (its anchor head is `S0`), `nestscan.py` is
negative on all five of these, and `radix_clock.py` says why: they count in
`phi`, not in 2 (§3 preamble).  The head symbol is a real hole in `nestcert`,
but no emitter in the tree can express a Fibonacci digit at any head symbol,
so widening the anchor search cannot help until the numerals exist.  The
`Kp`-shaped words below are a base-2 misreading of Zeckendorf digits, which is
also why their "values" come out as a sparse self-similar set.

### `0LC1RD_1LB1RC_1LB0RD` (3 rows), `0LC1RD_1LB1RD_1LB0RD` (3 rows)

`residue_map` reads both as `Ip`, "HIGHER".  Same diagnosis as above: no
affine lap at any anchor the scan finds, so nested rather than flat.  Note
`1RB---_1LC1RD_0LB1RD_1LB0RD` — the one row that DID board by certificate —
is the nested route (`NLAP_`) at an `S0` anchor, so the machinery is not far
away.

### `1RB---_1RC1LB_0LB1RD_0RA0RC` — the one row that targets `StA` — **BOARDED**

`Machines/Counters/NLAP_1RB____1RC1LB_0LB1RD_0RA0RC.v`, `NeverQuasiHaltsSt`
via `LapGlue.glue_neverqh`.  It is the one row of the 24 that does **not**
quasihalt, so `glue_neverqh` rather than `LapGlueQuiet.glue_qh_quiet`.

Its `0RB` shadow `0RB0RD_1RC---_1RD1LC_0LC1RA` boards with it, in
`Machines/Counters/RRNQ_0RB0RD_1RC____1RD1LC_0LC1RA.v` — and it has to,
because a shadow is only a shadow of a row that is still DEFERRED: boarding
the core row moves the shadow out of `shadow_rows.tsv` and into
`core_rows.txt` rather than settling it.  The transport is
`Census/Reroot.neverqh_reroot` across the blank prefix of length 1, plus
`TM_swap StB StC` and `TM_swap StC StD`, which move no start state.

**It is a plain binary counter** (John's reading, 2026-07-31): MSB to the
LEFT, one marker `1` to the left of every bit, ordinary carry.  Digit words
`A = 01`, `B = 11`, terminator `C = 1` — a new alphabet,
`Counters/Alph_01_11_1.v`.

**The anchor is FLAT, and the row is NESTED.**  `carry_anchor.py` found this
row at a carry-straddling anchor (127 consecutive values at state `StB`, head
`S0`, run-unit `11`, digits `10`/`11`), and the first reading of that was
"the checker can express it, what is missing is a straddling template".  That
was the wrong conclusion, and the straddling template was never needed.
Restrict that same family to its `j = 0` members — the anchors whose carry
run is EMPTY — and the head sits at the right end of the written region with
the whole word to its left:

```coq
Cin v = (StB, (S1 :: Rw v, S0, [S0]))
```

which is an ordinary flat anchor, and consecutive `j = 0` anchors are
consecutive values of `v`.  The lap is `4j + 8` and closes EXACTLY (the one
trailing `S0` in the anchor is what buys the exactness).

What actually hid the row was neither the head symbol nor the straddle: it
was that **the counter is FIXED-WIDTH inside an epoch**.  `Cin v` is visited
only for `v` in `[2^(2i), 2^(2i+1) - 1]`; when `v` fills to all ones the
machine re-spreads the solid run of ones into marker/bit pairs and the word
JUMPS to `2^(2i+2)`.  That widening is the only path on which `StD`'s `0RA`
fires — measured configuration indices

```
19, 66, 257, 1024, 4095, 16382, 65533, 262140, 1048571, …
```

(to `t = 2·10^6`), once per epoch.  So the value sequence is
`4,5,6,7 | 16,…,31 | 64,…,127 | …`, and **every anchor search in the tree
scores a family by its longest run of CONSECUTIVE VALUES** — which for a
nested counter is bounded by one epoch, drowning in noise at any tractable
step budget.  `residue_map.tsv` read the row as "no-anchor / no overflow
phase at K=6" for four waves on exactly that account.

**The general gap, corrected.**  It is the SCORE, not the anchor space.
`tools/counters/nestscan.py` (new) scores a candidate family by the local
`Alph` increment structure of ADJACENT anchor words —

```
w = pre ++ B^j ++ A ++ tail      w' = pre ++ A^j ++ B ++ tail
```

— voting `(A, B, |pre|)` out of the pairs themselves, with no notion of "the
value".  It reports this row's family at `run = 255` with the word length
breaking `6 → 10 → 14 → 18 → 22` at pair 5, 21, 85, 341, i.e. the epoch
structure read straight off.  Two details matter in that fit and both cost a
family if dropped: the `pre` (the stop digit's own marker sits in front of
the run) and a separate `j = 0` arm (there `B` does not occur in `w` at all
and has to be read from `w'`).

**The proof shape** is `Counters/NestedLap.v`'s, with the epoch as the outer
level:

| piece | what | cost |
|---|---|---|
| outer anchor | `Cc p := Cin (pow2 (2 * Pos.to_nat p))` | — |
| boot | one interior lap | `8` |
| inner | `Cin v0 -> Cin (fill v0)`, `inner_to_fill` | induction, existential |
| exit | the widening, `Cin (fill (pow2 (2j))) -> Cc (p+1)` | `8j + 11` |

Both laps are `LapDecider` certificates (`el`/`er` and the chains are in the
file).  `StA`'s visit witness is a prefix of the EXIT chain, which is the
only place it fires.  Differentially validated before the file was written:
3,988 interior laps exact (`v = 2..3999`), 11 exit laps lift-exact, and the
rails walked forward through six epochs of the real trajectory.

## 4. Reproducing the measurements

```sh
python3 tools/counters/radix_infer.py <rowfile>     # radix, digits, lap law
python3 tools/counters/carry_anchor.py <rowfile>    # anchors that straddle the head
python3 tools/counters/nestscan.py    <rowfile>     # anchors of a NESTED counter
python3 tools/counters/radix_clock.py <rowfile>     # radix, from the toggle spectrum
python3 tools/counters/fib_anchor.py  <rowfile>     # anchors under FIBONACCI weights
python3 tools/counters/emit_lapcert.py --list <rowfile> [--emit]
```

Two of these are new and they are the ones to reach for when a row is called
"no-anchor":

* `radix_clock.py` FIRST, always.  It needs no anchor at all, so it still
  answers on a row every other tool has given up on, and it answers the
  question that decides which machinery can possibly apply.  Had it existed,
  `Ter3Wall`'s base 3 and these eleven rows' `phi` would both have been known
  four waves earlier.
* then, on what it says: `fib_anchor.py` if the radix is `phi` (the ordinary
  anchor scan with a Fibonacci weight ladder), or `nestscan.py` if the radix
  is an integer but no scan finds a family — that is the only anchor scan here
  that does not require a long run of consecutive values, so it is the only
  one that can see a counter whose width is fixed inside an epoch.

The pattern across both of this session's findings: **the anchor space was
never the problem, the DECODING was.**  Twice in one session a row called
"no-anchor" turned out to be sitting at an ordinary flat anchor that every
scan already visits, missed once because the score demanded consecutive values
from a nested counter and once because the weights were `1,2,4,8` on a machine
counting in Fibonacci.

The emitters are UNTRUSTED, as everything under `tools/` is: a wrong role,
digit triple, boot index or chain fails to typecheck rather than mis-proving,
and the Coq kernel re-runs every checker on every board.
