# The REACHST tier: liveness on the machine, not on an abstraction

_Written 2026-07-30 after Nick Drozd pointed at 23 residue rows and said they
were easy.  They were, and this file records why — the reason generalises well
past those 23.  Extended the same day, after a second list of 31, by two more
flavours (§8); §0 is the state after both waves and §§1–7 are the first wave,
kept as written._

## 0. TL;DR

* **127 rows boarded** over two waves, kernel-checked,
  `functional_extensionality_dep` only.  Core undecided **143 → 68**,
  0RB shadows **74 → 22**, settled **4,939 → 5,066 of 5,156
  (95.8% → 98.3%)**.
* The mechanism is one idea.  For a counter, the **state-avoiding SUB-MACHINE
  can be far simpler than the machine**, and liveness only needs that
  sub-machine to terminate — not an exact lap.
* Across the whole open core the sparse state's avoid sub-machine takes only
  **FOUR** shapes up to state relabelling and mirroring.  Wave 1 proved two of
  them (§2, plain binary counters running DOWN, 78 rows); wave 2 proved the
  other two (§8, counters in a PAIR encoding, 49 rows).
* The tier is EXHAUSTED on the open list at both waves' end, by the same probe
  each time: 0 of the remaining 68 rows match a flavour.
* `docs/WHY_NO_HAMMER.md` is not refuted; it is **sharpened**.  Its measurement
  ("the q-avoiding subgraph of a finite abstraction is cyclic at every
  precision") is exactly right, and it says the abstraction has to go.  It does
  not say liveness is hard.

## 1. What the residue's liveness obligation actually is

`NeverQuasiHaltsSt tm` is `forall q, Visited q -> forall N, exists n >= N,
VisitsAt tm q n`.  Non-halting is easy on this residue; the wall is liveness.

Every engine in this tree discharges liveness the same way
(`Closure.rank_ok` / `lex_ok`, and `nghist_prove.cert_for_state` above them):
take the **q-avoiding subgraph** of a finite covering abstraction and show it
has no infinite path.  `WHY_NO_HAMMER.md` measured that to death: the closure
always closes, and the q-avoiding subgraph is always cyclic, at every `(k, n)`
on the grid, because a finite window admits the abstract path *"stay in the low
bits forever"* and a counter's carry is an unbounded wait.

`ReachSt` keeps the argument and drops the abstraction:

```coq
Definition ReachSt (tm : TM) (q : St) : Prop :=
  forall cc : cconf, exists k c', stepn tm k (lift cc) = Some c' /\ fst c' = q.
```

"From **every** configuration, `tm` reaches `q`" — i.e. the q-avoiding
sub-machine terminates, on the real tape, with no window and no merging, so the
spurious path has nowhere to live.  With all transitions defined it implies the
liveness obligation outright (`reach_st_recurs`).

## 2. Why that is CHEAPER than modelling the machine, not dearer

The 23 rows Drozd named all begin `1RB0LD`, and in 20 of them state `C` is the
sparse one: it fires ~16–530 times in 200k steps while `A`, `B`, `D` fire
~50,000 times each.  So `C` is the whole liveness question.

Now delete `C`.  What is left of the machine is

| flavour | the `StC`-avoiding sub-machine | rows |
|---|---|---|
| **B** | `A0->1RB  A1->0LD  B1->1RA  D0->0RB  D1->1LD` | 12 |
| **A** | `A0->1RB  A1->0LD  B1->1RA  D0->0RA  D1->1LD` | 8 |

**Two sub-machines for twenty rows.**  The C-transitions differ across the 20
and none of them matters: the instant `B0` fires we are in `C` and done.  The
full machines are nested counters — wave-33's item (1), the largest open thing
in the residue.  The sub-machines are plain binary counters running **down**,
and termination needs only a decreasing measure.

The measure (`theories/Checkers/ReachSt.v`):

```
mu (l, h, r) = 2 ^ |l| * (h + 2 * val r)
```

the tape read from the head RIGHTWARD as a binary number, weighted by ABSOLUTE
position (`2 ^ |l|` is the head cell's weight, `l` the left half-tape).  Every
branch drops it by an exact power of two:

| branch | drop |
|---|---|
| `A` on a blank, right neighbour 1 (walk 2 right) | `2 ^ (|l| + 1)` |
| flavour B, left run of `j+1` ones | `2 ^ (|l2| + 2)` |
| flavour A, left run of `j+1` ones | `2 ^ (|l2| + 1)` |
| flavour A, empty left run | `2 ^ (|l2| + 1)` |

and the remaining branches reach `StC` outright in 1–3 steps.  Induction on
`mu`.  That is the entire mathematical content of 20 boards.

**The one real side condition.**  The left half-tape is carried in the
decomposed form `rep S1 k ++ S0 :: l2` — a run of ones, then a blank, then
anything.  It is not cosmetic.  It says the list REPRESENTATION reaches past the
leftmost 1, so the leftward `D`-sweep stops inside it and no blank cell is
materialised.  Materialising one shifts the frame and DOUBLES `mu`, and the
measure stops decreasing — this cost two hours before it was diagnosed.  It is
free to impose, because trailing blanks are invisible to `lift` (`lift_pad`), so
any configuration pads into the form, and every branch preserves it.

## 3. Splicing it into the existing engine

`ReachSt` covers ONE state.  The other three still come from `NGramHist`, and
they come cheaply — measured over all 22 open rows at `k=2, n=2`:

**17 of 22 discharge `A`, `B`, `D` and fail on exactly the sparse state.**
The other 5 need one rung more (`k=3, n=2`); all of them discharge there.

So the boards are `NGramHist` for three states and a theorem for the fourth:

* `theories/Checkers/ClosureExt.v` — `closure_check_neverqh_lex_ext`, the
  engine's check with the gate for a designated `qext` lifted, and
  `closure_check_neverqh_lex_ext_sound`, which takes `qext`'s liveness as a
  PREMISE.  `Closure.v` is inside the census closure and is untouched; this is
  its top theorem re-proved with one extra case split.
* `theories/Checkers/NGramHistExt.v` — the same for
  `ngramhist_check_neverqh_lex_sound`.
* `tools/nghist/reachst_prove.py` — UNTRUSTED emitter: checks the machine is one
  of the two flavours, runs the closure, synthesises certificates for the other
  three states, emits the board.

Nothing is weakened.  The skipped state's obligation is not dropped, it is
MOVED, and the caller has to prove it.

## 4. The 78, the two widenings, and the 2 that are not here

The four ReachSt roles are SECTION VARIABLES (`qA qB qC qD : St`), not
`StA..StD`, and `Mirror.mirror_visits` is an iff.  So a machine boards if ITS
sub-machine, or its MIRROR's, is one of the two flavours under ANY state
relabelling — and the residue is full of both.  Boarding Drozd's rows first,
then re-running the tier over the whole open core and iterating to a fixed point
(each round of boards promotes 0RB shadows into the core, and those had never
been swept), gives **78 boards from the same two lemmas**:

| flavour | route | roles `qA qB qC qD` | `k,n` | rows |
|---|---|---|---|---|
| ma | direct | A B C D | 2,2 | 6 |
| ma | direct | A B C D | 3,2 | 2 |
| ma | direct | B C D A | 2,2 | 6 |
| ma | direct | B C D A | 3,2 | 2 |
| ma | direct | C A B D | 2,2 | 3 |
| ma | direct | C A B D | 3,2 | 1 |
| ma | mirror | B C A D | 2,2 | 5 |
| ma | mirror | B C A D | 3,2 | 1 |
| ma | mirror | C A B D | 2,2 | 2 |
| mb | direct | A B C D | 2,2 | 10 |
| mb | direct | A B C D | 3,2 | 2 |
| mb | direct | B C A D | 2,2 | 1 |
| mb | direct | C A B D | 2,2 | 1 |
| mb | direct | C A B D | 3,2 | 1 |
| mb | direct | C B A D | 2,2 | 3 |
| mb | direct | D B C A | 2,2 | 12 |
| mb | direct | D B C A | 3,2 | 1 |
| mb | direct | D C A B | 2,2 | 3 |
| mb | mirror | B C A D | 2,2 | 4 |
| mb | mirror | B C A D | 3,2 | 1 |
| mb | mirror | C A B D | 2,2 | 8 |
| mb | mirror | D A B C | 2,2 | 3 |

All at `t=200 fuel=40000`; the per-row detail is in the emitted headers under
`theories/Machines/ReachSt/`.  **Eight distinct role assignments** appear and
only 20 of the 78 use the identity; 24 go through the mirror.  So the two
generalisations together are worth **nearly three times** the original catch,
and neither needed a line of new mathematics — the relabelling because the
ReachSt roles are section variables, the mirror because `Mirror.mirror_visits`
is already an iff.

The 23rd row Drozd listed, `1RB0LD_1LC1RA_1LA1RC_0RB1LD`, was **already
boarded** (`theories/Machines/Counters/REG_...`, wave-32's two-form route).  It
is flavour `mb`, so `ReachSt` covers it too — a free control, and a useful one:
the two routes agree.

**Still open: `1RB0LD_1LC1LB_1LD1RC_0RC1LA` and `1RB0LD_1LC1RB_1LD1RC_0RC1LA`.**
Their sparse state is `B`, not `C`, and they share a THIRD avoid sub-machine:

```
A0 -> HALT(B)   A1 -> 0LD   C0 -> 1LD   C1 -> 1RC   D0 -> 0RC   D1 -> 1LA
```

It is measured terminating (§5) but it is not a down-counter: `A`/`D` alternate
leftward turning `1^k` into `1010...` while the rightward `C` sweep appends one
1, so the block GROWS and `mu` does not work.  It wants its own measure.  Two
rows, one lemma — the cheapest thing left in this direction.

## 5. What was measured, and the controls

Probes are committed under `tools/` and the measurements are at this commit.

* **Sparse-state identification** — state usage over 200k steps, all 23 rows.
  `C` (resp. `B` for the two `0RC1LA` rows) fires 16–530 times where the others
  fire ~50,000.
* **Avoid-sub-machine termination, EXHAUSTIVE** — every tape of width ≤ 10 with
  blanks outside, every head position, every start state, for all 23 × 4
  avoid-machines (**62 distinct tables**).  **52 of 62 terminate.**  All 10 that
  do not are spin-outs on an all-blank tape (`C0->0RC` / `C0->1LC` walking
  forever over blanks), i.e. genuine infinite runs from configurations that are
  not the point here — the SPARSE state's own avoid-machine terminates for
  **all 23 rows**.  Probe: `tools/reachst/avoid_probe.py --tables`, output
  recorded in `tools/reachst/RESULTS.txt`.
* **Control** — the same measure `mu` on the boarded row
  `1RB0LD_1LC1RA_1LA1RC_0RB1LD` reproduces the flavour-B law, and its two
  routes (two-form certificate, ReachSt) agree.
* **Per-state NGramHist**, `k=2 n=2 t=200 fuel=40000`, all 22 rows: exactly the
  sparse state fails on 17; 5 rows need `k=3`.  This is the same closure the
  wave-12 hammer ran; the difference is only that it is now asked for three
  states instead of four.

## 6. Where this goes next

The tier is not about `1RB0LD`.  The generalisable claim is:

> **liveness of a residue machine's sparse state is a termination question
> about a SMALLER machine, and the smaller machine is often several rungs
> below the original on the counter ladder.**

Three concrete follow-ups, in order of cheapness (1 and 2 are DONE — see §8
for what they actually paid, which in both cases was far more than the
estimate here):

1. **The third flavour** (§4) — two rows, one measure.
2. **MIRRORING — the half of the widening that is still on the table.**
   State relabelling is now done (§4, +22 rows).  Mirroring is not: measured
   over the open core AFTER this wave, **22 of the remaining 119 rows match a
   flavour under mirroring** (and 0 without it — the forward catch is
   exhausted).  They are untouched because `NGramHistExt` wants the liveness premise for the
   ORIGINAL machine and `Mirror.v` transports `NeverQuasiHaltsSt`, not a single
   state's `VisitsAt`.  One transport lemma — "`q` recurs in `mirror_tm tm`
   implies `q` recurs in `tm`" — unlocks all 21.  This is the cheapest large
   thing left in this direction and it is bigger than what is here.
3. **A verified uniform-termination decider.**  The bounded symbolic search
   (branch on each freshly-read cell) is NOT enough on its own — a leftward
   sweep over an unbounded run has no uniform step bound: **0 of 62** tables are
   bounded at depth 40 (`avoid_probe.py --bounded`).  With sweep ACCELERATION (`q1 -> 1Lq` etc. as one macro
   step) most of the 60 become bounded, and that is a real decider rather than
   one lemma per flavour.

## 7. Do not retry

* **Reading `WHY_NO_HAMMER.md` as "liveness is hard here".**  It measured that
  liveness is hard *for a finite abstraction*.  Twenty rows say otherwise once
  the abstraction is removed for one state.
* **A uniform STEP BOUND for an avoid sub-machine.**  Measured: symbolic search
  branching on every unknown cell is unbounded at depth 40 on 62 of 62 tables,
  because a sweep over an unknown run is unbounded.  Accelerate the sweeps or
  do not bother.
* **`mu` without the `rep S1 k ++ S0 :: l2` invariant.**  The frame shift
  doubles it (§2).
* **Sizing a flavour from the rows that suggested it.**  §6 called the third
  flavour "two rows, one measure".  It was 34 rows, and its sibling another 15
  (§8).  Group the whole open core's avoid tables BEFORE costing a lemma —
  `tools/reachst/cluster.py` is three lines of work and it is the difference
  between a two-row lemma and a fifty-row one.

## 8. Wave 2: the PAIR counters, and the other two flavours

_2026-07-30, after Drozd named a second list — 31 rows this time.  Twenty of
the 31 were already settled before they were named: **17 by wave 1's
fixed-point sweep**, which had caught them as relabellings and mirrors of its
two flavours, 2 by wave 32's two-form route, and one is the QUASIHALTER
`1RB1RD_1RC0LD_1LB0RA_1LC0LC`.  Of the 11 that were left, 4 board here and 7
do not (§8e)._

### 8a. Grouping first

The 11 open rows of Drozd's 31 were clustered by the CANONICAL FORM of their
sparse state's avoid table, modulo state relabelling and mirroring
(`tools/reachst/cluster.py`).  Three of them share ONE table — and it is
exactly the third flavour §4 flagged, the one the two `0RC1LA` rows wanted.
Swept over the whole open core the same table appears in **25 of 97 rows**,
not the two §4 estimated from the rows that had suggested it.  That is the
lesson of this wave and it is now a do-not-retry entry in §7.

### 8b. Flavour C — the block GROWS, and the counter INCREMENTS

    qA 0 -> ..qC   qA 1 -> 0L qD          (the eraser; its blank is the gate)
    qB 0 -> 1L qD  qB 1 -> 1R qB          (the rightward sweep)
    qD 0 -> 0R qB  qD 1 -> 1L qA          (the writer)

`mu` is useless here, exactly as §4 said: the `qA`/`qD` alternation walks left
turning `1^k` into `1010…` while the `qB` sweep appends a 1, so the block grows
and the tape-as-a-binary-number goes UP.  What is running is a counter in a
different alphabet.  Read the tape rightward from the head TWO CELLS AT A TIME,

    X = (1,1)    Y = (0,1)    Z = (1,0)    O = (0,0)

and one round — restart to restart — is exactly

    X^j (0,b) R   |-->   X Y^(j-1) (1,b) R

a little-endian increment on the leading `{X,Y}` block, with `Z` the
terminator that stops the machine.  So the measure is

    mu2 w = sum_{i <= q} [w(2i) = 0] * 2^i,     q = min { i | w(2i+1) = 0 }

which drops by **exactly 2** every round (`mc_drop`), and `mu2 = 0` is exactly
the halting case — the leading 1-run has odd length, `qA` meets the barrier
blank and steps to `qC`.  Induction on `mu2`, nothing else.

### 8c. Flavour D — the same five arrows, and it DECREMENTS

    qA 0 -> ..qC   qA 1 -> 1L qD          (the writer; its blank is the gate)
    qB 0 -> 1L qA  qB 1 -> 1R qB
    qD 0 -> 0R qB  qD 1 -> 0L qA          (the eraser; its blank turns)

C and D are the same shape with the two BLANK branches swapped between the
writer and the eraser.  That one swap turns the increment into borrow
propagation:

    X^j Z R   |-->   Z^j X R

so reading `Z` as the bit 1 over the leading `{X,Z}` block,

    nu2 w = sum_{i < p} [w(2i+1) = 0] * 2^i,    p = min { i | w(2i) = 0 }

drops by **exactly 1** per round (`md_drop`), and `nu2 = 0` — the block is all
`X` — is the halting case.  D needs no refill dance at the turn: the eraser's
blank branch lands on the next restart directly.

Both are in `theories/Checkers/ReachSt.v`, sections `MC` and `MD`.  Unlike
`MA`/`MB` a round CONSUMES a blank from the right list, so the decomposed form
has to be restored every round; that is why both state reaching `qC` on the
LIFTED configuration, where `lift_pad_r` makes the restore free.

### 8d. What it paid, and the seven that are left

| | rows | core | shadows | settled |
|---|---|---|---|---|
| after wave 1 | — | 97 | 42 | 5,017 (97.3%) |
| + flavour C | 34 | 77 | 28 | 5,051 (98.0%) |
| + flavour D | 15 | 68 | 22 | 5,066 (98.3%) |

Both were swept to a fixed point (each round of boards promotes 0RB shadows
into the core, and those had never been swept): C caught 20 then 14, D caught
9 then 6.  The tier is exhausted again — 0 of the remaining 68 match any of
the four flavours.

Of Drozd's 31, **24 are settled**: the 20 that already were (see the note
under §8), plus 3 by flavour C and 1 by flavour D.

### 8e. The seven that are left, and why the tier cannot reach them

A board needs TWO independent things for the SAME state `q`: the `q`-avoiding
sub-machine must terminate (so `ReachSt tm q` is provable at all), and
`NGramHist` must discharge the other three with `q` lifted out.  Wave 1 and
wave 2 both chose `q` by sparseness and never had to ask whether that was the
right choice.  `tools/reachst/bothhalves.py` asks it per state — `T` = the
avoid machine terminates exhaustively at width <= 10, `N` = the closure
discharges the other three at `k=2` or `k=3`, `n=2`:

    1RB1LC_0LC0RB_0RD1LA_0LA1RD   A:T-  B:fN  C:T-  D:T-
    1RB1LC_0LC0RB_1LA1LD_1RC0LD   A:T-  B:T-  C:T-  D:fN
    1RB1LD_1RC0RC_1LA0LA_0RA0LD   A:T-  B:f-  C:f-  D:fN
    1RB1RC_1LA0LB_1LD0RD_1LB0RC   A:T-  B:T-  C:f-  D:f-
    1RB1RC_1LA1LD_0RB0RC_1LB0LB   A:T-  B:T-  C:fN  D:T-
    1RB1RC_1LA1RA_0RC1LD_1LB0LD   A:f-  B:f-  C:T-  D:f-
    1RB1RD_1LC1RA_0RB0LC_1LA0RD   A:T-  B:T-  C:T-  D:fN

**Not one cell reads `TN`, and the near-misses are all the same near-miss.**
On five of the seven exactly ONE state carries the `N`, and it is exactly the
state whose avoid machine fails: the two halves exist, on disjoint states.
There is no choice for the emitter to get right here — a board must lift the
`N` state, and that state has no `ReachSt` theorem to lift it with.  On the
other two the closure discharges no state at all, so the tier has nothing to
lift.

So the seven are blocked by two different things, and only one of them is
about `ReachSt`:

* **The avoid machine of the only liftable state does not terminate** (the
  five rows with an `fN` cell).  Every
  counterexample `avoid_probe.py --tables` reports is a spin-out on an
  ALL-BLANK tape — a configuration the machine never reaches.  `ReachSt`
  quantifies over EVERY configuration, so the predicate as it stands is
  strictly stronger than liveness needs and these rows fall outside it.  The
  fix is a `ReachSt` relativised to an invariant the real orbit satisfies.
  That is the first thing in this direction that is not just another measure,
  and it is what the tier should do next: it is worth at least these rows and
  the same spin-outs were 10 of the 62 tables measured in wave 1 (§5).
* **The closure discharges nothing** (`1RB1RC_1LA0LB_1LD0RD_1LB0RC` and
  `1RB1RC_1LA1RA_0RC1LD_1LB0LD`).  Nothing to lift, so a
  better `ReachSt` would not help either; these want more precision on the
  `NGramHist` side, or a different engine entirely.  `docs/RESIDUE_MAP.md`
  files them as `EXP3`/`AFFINE` interior laps with no interior chain.
