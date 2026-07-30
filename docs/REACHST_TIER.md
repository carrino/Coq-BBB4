# The REACHST tier: liveness on the machine, not on an abstraction

_Written 2026-07-30 after Nick Drozd pointed at 23 residue rows and said they
were easy.  They were, and this file records why — the reason generalises well
past those 23._

## 0. TL;DR

* **42 rows boarded**, kernel-checked, `functional_extensionality_dep` only.
  Core undecided **143 → 119**, 0RB shadows **74 → 56**, settled
  **4,939 → 4,981 of 5,156 (96.6%)**.
* 20 of the 42 are Drozd's; the other 22 are the same two sub-machines under a
  different STATE RELABELLING, found by re-running the tier over the whole open
  core and then iterating as boarding promoted shadows into it.
* The mechanism is one new idea and three new files.  For a counter, the
  **state-avoiding SUB-MACHINE can be far simpler than the machine**, and
  liveness only needs that sub-machine to terminate — not an exact lap.
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

## 4. The 42, the widening, and the 2 that are not here

The four ReachSt roles are SECTION VARIABLES (`qA qB qC qD : St`), not
`StA..StD`.  The sub-machine is what the theorem is about, so any relabelling
of it is the same theorem — and the residue is full of relabellings.  Boarding
all of Drozd's rows first, then re-running the tier over the whole open core and
iterating (each round of boards promotes 0RB shadows into the core, and those
had never been swept), gives **42 boards from the same two lemmas**:

| flavour | roles `qA qB qC qD` | `k,n` | rows |
|---|---|---|---|
| mb | A B C D | 2,2 / 3,2 | 10 / 2 |
| mb | D B C A | 2,2 / 3,2 | 4 / 1 |
| mb | C A B D | 2,2 / 3,2 | 1 / 1 |
| mb | B C A D · C B A D · D C A B | 2,2 | 1 · 1 · 1 |
| ma | A B C D | 2,2 / 3,2 | 6 / 2 |
| ma | B C D A | 2,2 / 3,2 | 6 / 2 |
| ma | C A B D | 2,2 / 3,2 | 3 / 1 |

All at `t=200 fuel=40000`; the per-row table is the emitted headers under
`theories/Machines/ReachSt/`.  **Six distinct role assignments** appear, and
only 20 of the 42 use the identity — so the relabelling generalisation is worth
more than the original catch.

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

Two concrete follow-ups, in order of cheapness:

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
