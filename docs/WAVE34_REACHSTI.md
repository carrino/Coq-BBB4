# Wave 34 — `ReachStI`, and Drozd's 26 measured end to end

Nick Drozd posted 26 machines as "easy".  All 26 are in
`tools/closeout/core_rows.txt` (the 65 open core rows).  This wave builds the
tier `docs/REACHST_TIER.md` §8e names as the next move — **`ReachSt`
relativised to an invariant** — measures exactly what it buys on those 26,
and reports, honestly, that **it boards none of them** and why.

Everything below that is a measurement was produced by a tool committed in
this wave; everything that is a proof is kernel-checked with the usual
footprint (`functional_extensionality_dep` only).

## 1. What the 26 are

**All 26 are binary counters.**  Tape width against step count
(`tools/reachsti/`, and the raw widths at `t = 1e4 / 1e5 / 1e6 / 1e7`) grows
by 3–4 cells per decade on every row — the log-time signature.  None is a
cycler (no configuration repeats in 4·10^5 steps) and none halts.
`tools/counter_encodings.tsv` already classifies 17 of them `KCOPY1`; the
plain-counter emitter `tools/counters/emit_kp.py` derives **0 of 17**, all
failing at "laps not affine on both branches" — the wave-9 finding that the
overflow lap grows like `2^j`.

**They split two ways, and the split matters.**

| | rows | target theorem |
|---|---|---|
| `1RB---` | 14 | `iqh = NonHalt /\ QHBound 2000 /\ QuasiHaltsSt` |
| total | 12 | `NeverQuasiHaltsSt` |

On every one of the 14, the undefined cell is `A1` and **no transition
targets `StA`** (checked, not assumed).  So `StA` fires exactly once, at
configuration index 0, and those machines genuinely **quasihalt with score
1**: `NeverQuasiHaltsSt` is *false* for them.  The whole `ReachSt` tier is
therefore inapplicable on its face — and indeed `tools/reachst/bothhalves.py`
skips them with "(undefined transition — boards via its completions)", so
they had never been measured at all.  Their real obligation is the liveness
of `StB`, `StC`, `StD` plus `NonHalt`.

## 2. The tier: `theories/Checkers/ReachStI.v`

`ReachSt tm q` asks the `q`-avoiding sub-machine to terminate from **every**
configuration.  §8e measured how that over-shoots: every counterexample
`avoid_probe.py --tables` reports is a spin-out on an all-blank tape.  Re-run
on these 26 it is the same story — **every** counterexample across the 97
distinct avoid tables is `(w,bits,pos) = (0,0,-1)` or `(1,1,-1)`, i.e. the
head just off the edge of an (almost) blank tape.

`ReachStI` relativises the predicate to

    I cc  :=  the STATE of cc lies in `allowed`

where `allowed` is the largest state set that is **total** and **closed**
under the table (`inv_ok`).  That one change fixes both defects at once:

* on a `1RB---` row it drops `StA`, and with it the undefined transition —
  without which `ReachSt tm StB` is not merely unprovable but **false**, since
  `(StA, ([], S1, []))` halts on the spot;
* the blank spin-outs go with it, because they are reached only through the
  dropped states.

Termination is a **computable certificate**, not a hand-written per-flavour
lemma.  The measure is

    mu (q,(l,h,r)) = B * ones l + C * ones r + rk (q, chd l, h, chd r)

and `drop_ok` checks a strict drop on every goal-avoiding step.  `mu` is a
`nat`, so the drop bounds the run outright.  The check is exact because
`CTape.ctape_move` moves exactly one cell across the head:

    DR  (l,h,r) -> (w::l, chd r, ctl r)     ones l += w    ones r -= chd r
    DL  (l,h,r) -> (ctl l, chd l, w::r)     ones r += w    ones l -= chd l

Every quantity the drop compares is known except the cell freshly exposed
behind the one being crossed; `drop_ok` quantifies over both its values, so
nothing is assumed away.  `reach_sti_recurs` returns **`NonHalt` together
with** the goal state's liveness — the `1RB---` rows need the `NonHalt`, and
`ReachSt`'s `Total` premise cannot give it to them.

The constants come from a Bellman-Ford over the difference constraints
(`tools/reachsti/cert_search.py`).  Nothing there is trusted: a wrong
constant makes `drop_ok` evaluate to `false`.
`theories/Tests/ReachStI_Examples.v` proves the positive direction on
`1RB---_0LB1RC_0RD0RC_1LB1LD` and pins eight corruptions that must fail —
including `allowed` swallowing `StA` (the unsoundness the totality check
exists to stop) and the two goal states that row is genuinely missing.

## 3. What it buys

* **26 of 26** rows have at least one state whose avoid sub-machine
  terminates from every configuration (exhaustive, every tape of width ≤ 8,
  every head position, every start state).
* **25 of 26** get a certificate from the measure the Coq checker implements
  (one cell of context each side).  The 26th,
  `1RB1LA_0LA0RC_0LD0RB_1LD1RC`, needs two cells — the search finds it at
  `K = 2`, and extending `drop_ok` to depth 2 is mechanical but not done.
* On the 14 `1RB---` rows this is the first liveness *or* non-halting fact
  the development has ever had.

## 4. Why it still boards nothing — the actual blocker

A board needs **every** visited state at once: `NeverQuasiHaltsSt` quantifies
over all of them, and so does the `QHBound` half of `iqh`.  `ReachStI`
supplies one or two; the rest must come from the `NGramHist` closure.

`tools/reachsti/sweep.py` runs both engines per row per state.  Measured on
all 14 `1RB---` rows and 3 of the 12 total rows (the closure blows past a
2-minute budget on the others; the sweep reproduces them given longer):

    1RB---_0LB1RC_0RD0RC_1LB1LD  allowed=BCD   reachsti=B   closure=B    missing CD
    1RB---_0LC1RB_0LB1RD_1LC0RD  allowed=BCD   reachsti=BC  closure=BC   missing D
    1RB---_0RC0RB_1LD1LC_0LD1RB  allowed=BCD   reachsti=D   closure=D    missing BC
    1RB---_1LC0RB_0LD1RB_0LC1RB  allowed=BCD   reachsti=CD  closure=CD   missing B
    1RB---_1LC0RD_0LC1RB_1LB0RB  allowed=BCD   reachsti=C   closure=C    missing BD
    1RB1LA_1LC0RD_0RA0LC_0LA1RD  allowed=ABCD  reachsti=A   closure=AD   missing C
    1RB1LC_0LA0RB_0RD1LA_0LC1RD  allowed=ABCD  reachsti=C   closure=ACD  missing B
    1RB1LD_1RC0RC_1LA0LA_0RA0LD  allowed=ABCD  reachsti=A   closure=ABC  missing D

Two things stand out, and they are different on the two halves of the split.

**On all 14 `1RB---` rows the closure certifies exactly the states `ReachStI`
certifies — not one more.**  The two engines fail on the same states, for the
same reason, so there is no complementarity to exploit there at all.

**On the total rows there IS complementarity** (`closure=ACD` against
`reachsti=C`), and it is not enough: every row measured is short by at least
one state.  `bothhalves.py` says the same thing from the other side — 0 of
the 26 have a state reading `TN`.

**So no row is boardable, and 9 of the 17 measured are short by exactly one
state.**  That one state is always the **wall** state.  On
`1RB---_0LB1RC_0RD0RC_1LB1LD` the counter is `1 [bits] 1` with a fixed `1` at
cell 0; `StC` is live iff `StB`'s leftward sweep always terminates at that
wall, and neither a state-set invariant nor a finite window can see it.  It is
`docs/WHY_NO_HAMMER.md`'s unbounded carry wait, one layer in.

Chaining barely helps.  A cheap extension — "from every allowed configuration
**in state q1**, reach q2", strictly weaker than `ReachStI`, giving liveness
implications — was searched over all row × (q1,q2) pairs.  On
`1RB---_0LB1RC_0RD0RC_1LB1LD` it proves `C ⟹ D` and `D ⟹ B`, exactly the two
easy edges, and fails on `B ⟹ C`, the wall edge.  It adds one state on one
row (`1RB1LA_1LC0RD_0RA0LC_0LA1RD`, `A` then `B`) and nothing anywhere else,
and it closes no row.  It is therefore **not** implemented in Coq: it would
add machinery and board nothing.

## 4b. The counter reading — and why the classifier was pointing the wrong way

The liveness engines were the wrong tool, and the reason is worth writing
down, because it is a *classification* bug rather than a proof gap.

`tools/kcopy_classify.py` labels 17 of the 26 `KCOPY1` ("one bit per cell"),
and `emit_kp.py` derives **0 of 17**, every one at "laps not affine on both
branches".  But `kcopy_classify.py`'s entire vocabulary — `KCOPY<k>`,
`SEP<k>` — is *one BIT per k cells*, and `alphabet_infer.py`'s shape is a
positive-recursion (`E (xO q) = A ++ E q`, `E (xI q) = B ++ E q`).  **Both can
only ever return a base-2 counter, and so can every alphabet in
`theories/Counters`: Ip, Jp, Kp, Dp, Bp, Mp.**

Some of these rows are not base 2.  Reading the tape of
`1RB---_0LB1RC_0RD0RC_1LB1LD` at its anchor (state `StB`, empty left list —
the wall):

    01 | 11 | 00 01 | 01 01 | 11 01 | 00 11 | 01 11 | 11 11 | 00 00 01
     1 |  2 |   0,1 |   1,1 |   2,1 |   0,2 |   1,2 |   2,2 |    0,0,1
     1    2      3       4       5       6       7       8         9
gap: 4    4      8       4       4       8       4       4        12

It is a **base-3 counter, one digit per two cells**, digits
`{00, 01, 11} = {0, 1, 2}`, whose anchor snapshots decode to
1, 2, 3, … consecutively over 10^4 visits, with the lap **affine in the carry
length**: `4 + 4j`.  `emit_kp.py` was fitting the wrong radix.

`tools/counters/radix_infer.py` (new) does the search without assuming base 2.
Over the 26 (`tools/counters/RADIX_DROZD26.txt`): **17 decode to consecutive
integers** at some anchor, four of them at radix 3 with 2-cell digits, and
**5 are affine in the carry length on the branches observed** — all five
`1RB---` rows:

    1RB---_0LB1RC_0RD0RC_1LB1LD   radix 3, digits 00/01/11, lap 4 + 4j
    1RB---_0LB1RC_1LB0RD_1LB0RC   radix 2, one cell,         lap 2 + 2j
    1RB---_0RC0RB_1LD1LC_0LD1RB   radix 3, digits 00/01/11, lap 4 + 4j
    1RB---_1LC0RD_0LC1RB_1LC0RB   radix 2, one cell,         lap 2 + 2j
    1RB---_1LC0RD_0LC1RD_1LC0RB   radix 2, one cell,         lap 2 + 2j

(Affine over the carry lengths that *occurred*, interior and overflow lumped:
a routing hint, not the emitter's differential validation.)

**This is the route that should have been taken, and it does not need
`ReachStI` at all.**  A lap gives the liveness of *every* state at once, plus
`NonHalt` — which is exactly where the closure route died.  The closer
already exists and is already aimed at this case:
`LapGlueQuiet.glue_qh_quiet` returns `NonHalt /\ QHBound (S s0) /\
QuasiHaltsSt` from a bootstrap, laps avoiding the quiet state, and a visit
witness per other state.  For a `1RB---` row that is `qa = StA`, `s0 = 0`,
`t0 = 1`, and `StA`-freedom of every lap is immediate because nothing targets
`StA`.  `theories/Machines/Counters/BNC_1RB____1LC0RB_1LD1RB_1LC1RB.v` is a
`1RB---` row already boarded exactly this way (via `BounceGlue.bounce_qh`).

So for the three radix-2 affine rows the Coq encoding already exists
(`KpCounter.Kp`) and the closer already exists.  The missing piece is an
**emitter pairing the `Kp` encoding with the QUASIHALTING closer**:
`emit_kp.py` emits never-QH boards, and `emit_qh.py` — which does emit the
`iqh` triple — is hard-wired to the `Jp` encoding.  Crossing those two is the
shortest path to boarding rows from this list.  The two radix-3 rows need one
more thing: a ternary digit alphabet, which no `theories/Counters` encoding
currently provides.

## 5. The other next step, with the measurement that sizes it

For the missing states the run that must be excluded is often a pure
**runner**, which is what `Closure.runner_ok` + `Records.run_right_exhausts`
are for: a run that always moves the same way drains that side's window, so
"fuel ≥ 1 on the movement side, forever" is impossible.

Measured over all 54 missing states: **13 have an avoid sub-machine whose
every transition moves the same direction.**  On
`1RB---_1LC0RB_0LD1RB_0LC1RB` — where `ReachStI` already supplies `StC` and
`StD`, so `StB` is the *only* thing between the row and an `iqh` board — the
`StB`-avoiding sub-machine is `C0 -> 0LD`, `D0 -> 0LC`, everything else
reaching `StB`: a pure left runner.

So the concrete next piece is the **fuel-tracking abstraction
(`Checkers/FuelWide.v`, which already instantiates `node_moves_right` /
`node_rfuel_ge1`) wired into the one-state-lifted path** (`ClosureExt`), so a
board can combine: `ReachStI` for the states with a measure, the runner rule
for the pure-runner states, and the closure for the rest.  That combination
does not exist today — `ClosureExt` forks the plain lex engine, and the fuel
engine has no `ext` variant.

What that will *not* fix is the other 41 missing states, whose avoid
sub-machines change direction.  Those still want the wall itself.

## 6. Reproducing

    python3 tools/reachsti/cert_search.py 1RB---_0LB1RC_0RD0RC_1LB1LD
    python3 tools/reachsti/emit.py       1RB---_0LB1RC_0RD0RC_1LB1LD
    python3 tools/reachsti/sweep.py      tools/reachsti/drozd26.txt
    make -f Makefile.coq theories/Tests/ReachStI_Examples.vo

`tools/closeout/core_rows.txt` is **unchanged**: no row moved, and the
closeout audit still partitions.
