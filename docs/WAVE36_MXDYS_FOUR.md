# Wave 36 — mxdys's four "easy" rows, read end to end

mxdys handed over four rows as easy:

    1RB1LC_0LC0RB_1LA1RD_0LA0RD      (M1)
    1RB1LC_1LB1RA_0LC0LD_0RA0RD      (M2)
    1RB1LC_1LC1RA_0LC0LD_0RA0RD      (M3)
    1RB1LD_1LC1RA_0RB0LC_0RA0LD      (M4)

All four are in `tools/closeout/core_rows.txt`.  **None is boarded by this
wave.**  What this wave produced is the mathematics: complete, validated
macro-rule systems for M1 and M4, a proof of the one liveness obligation
that had no route before, the exact counter reading for M2/M3, and — the
result most worth carrying — a **permanent negative** that rules the whole
`ReachSt` tier out of M1 and M4 forever, so no future session spends a day
re-measuring it.

Everything below that is a measurement was produced by a tool in
`tools/mxdys4/`.  Nothing here is a Coq proof yet.

## 1. The target is `NeverQuasiHaltsSt` on all four

`tools/mxdys4/gaps.py` over 20M steps: every one of the four states is
visited on all four rows, and every one keeps recurring.  So the target
theorem is `NeverQuasiHaltsSt` — not `iqh` — and all four states carry a
liveness obligation.

## 2. The half-tape invariant, and why it is the whole game

Each of M1 and M4 keeps **one half-tape a bare unary run** for its entire
orbit (`tools/mxdys4/macro1.py`, `macro4.py`; 0 violations in 400k steps):

| row | invariant |
|---|---|
| M1 | `L [q s] 1^R` — everything right of the head is `1^R` then blank |
| M4 | `1^p [q s] R` — everything left of the head is `1^p` then blank |

That collapses the configuration to `(L, s, R)` resp. `(p, s, R)` and makes
the dynamics a **word-rewriting system with finitely many rules**.

### 2a. M1's macro system — four rules, exhaustive

Write the frame as cells `0..w-1`, head at `p`, `R = w-1-p` (so
`W[p+1..w-1]` are all `1` by the invariant):

| # | guard | action | steps |
|---|---|---|---|
| 1 | `W[p]=0`, `R>=2` | `W[p]:=1`; `W[p+1..w-2]:=0`; `p:=w-2` | `R+3` |
| 2 | `W[p]=0`, `R<=1` | `W[p]:=1` | `4` |
| 4 | `W[p]=1`, `W[p-1]=0` | `W[p-1]:=1`; `p:=p-2` | `2` |
| 5 | `W[p]=1`, `W[p-1]=1` | `W[p..w-1]:=0`; `p:=w-1` | `R+4` |

with rule 4 at `p<=1` widening the frame instead (`W = 0 1^(w+1)`, `p:=0`,
the epoch reset).  Equivalently, on the raw tape:

    (1)  L [A0] 1^R      ->  L 1 0^(R-2) [A0] 1        R >= 2
    (2)  L [A0] 1^R      ->  L [A1] 1^R                R <= 1
    (4)  L x 0 [A1] 1^R  ->  L [A x] 1^(R+2)
    (5)  L 1 [A1] 1^R    ->  L 1 0^R [A0]

**Validated 400/400 macro steps against the raw simulator** (≈30k raw
steps), no exceptions.  Every rule starts and ends in `StA`, so the system
is closed.

### 2b. M4's macro system — three rules

Config `1^p [A s] R`:

    (1)  1^p [A0] 1 R  ->  1^(p+2) [A R_0] R_1..          2      steps
    (2)  1^p [A0] 0 R  ->  1 [A0] 0^(p-1) 1 R             p+7    steps
    (3)  1^p [A1] R    ->  [A0] 0^(p-1) 1 R               p+2    steps

**Validated 4000/4000 macro steps.**  M4 is the same shape as M1 with the
two half-tapes exchanged — it is *not* `mirror_tm` of M1 under any state
bijection (checked), but the reading transports.

## 3. THE NEGATIVE: the `ReachSt` tier is permanently out of reach on M1 and M4

`ReachStI`'s measure is `mu = B*ones l + C*ones r + rk(node)` and a strict
drop per goal-avoiding step, so **it can only ever certify a goal that the
machine reaches within `O(tape width)` steps**.  `tools/mxdys4/gaps.py`
measures the worst gap between consecutive visits of each state against the
tape width at that moment (3M steps):

| row | A | B | C | D | width |
|---|---|---|---|---|---|
| M1 | 33 | 64 | 34 | **262170** | 32 |
| M2 | 26 | 32 | 30 | 30 | 27 |
| M3 | 26 | 32 | 28 | 28 | 27 |
| M4 | 35 | 33 | 63 | **196633** | 31 |

`StD` on M1 and M4 recurs on a `Theta(2^width)` schedule.  **No measure
linear in the half-tape `S1` counts — nor in any locally-checkable linear
functional of the tape, extents included — can bound a run that long.**
This is not a search failure and no widening of the certificate class fixes
it; it is a statement about the growth rate.  `ReachSt`, `ReachStI`, the
`NGramHist` closure and everything else in `docs/REACHST_TIER.md` are
therefore closed on `StD` for these two rows, and the sweeps that report
"missing D" are reporting a wall, not a gap.

The same table read the other way is the positive half: **on M2 and M3
every state recurs on an `O(width)` schedule**, so the tier is *not*
excluded there — see section 5.

## 4. THE POSITIVE: `StD` on M1 is live, and here is the proof

`StD` fires exactly at macro rule 5 (and at rule 2 with `R=0`, which only
follows a rule 5).  So the whole obligation is: **rule 5 fires infinitely
often.**  It does, and the argument is short.

Let `N(W) = sum_i W[i] * 2^(w-1-i)` — the frame read as a binary number
with cell 0 the *most* significant.  Then:

* **rules 1, 2 and 4 strictly increase `N(W)`.**  Rule 2 and rule 4 set a
  `0` cell to `1`.  Rule 1 sets `W[p]` (weight `2^(w-1-p)`) and clears
  `W[p+1..w-2]`, which by the invariant were all `1` and sum to
  `2^(w-1-p) - 2`; net `+2`.
* **only rule 5 ever clears a cell**, so once `W[0] = 1` it stays `1`.
* **the frame widens only at `p <= 1`**: at `p=1` it needs `W[0]=0`, at
  `p=0` it needs `p` even.
* **rules 1 and 2 send `p` to `w-2`, rule 4 preserves `p`'s parity, and
  only rule 5 sends `p` to `w-1`.**  Frame widths are odd throughout
  (`3, 5, 7, ...`; the `+1` widening needs `W[0]=0`, which cannot recur),
  so `w-2` is odd and `w-1` is even.

Now suppose rule 5 fires finitely often, and look after the last one.

* If the frame never widens again, `N(W)` strictly increases forever inside
  `[0, 2^w)` — contradiction.
* If it widens, the new frame is `W = 0 1^(w'-1)` at `p=0` with `w'` odd.
  The first move is rule 1 (`R = w'-1 >= 2`), which sets `W[0]:=1` and
  `p := w'-2`, an **odd** position.  From there rules 1, 2 and 4 keep `p`
  odd, so `p=0` is never reached and the `p=0` widening is unavailable;
  and the `p=1` widening needs `W[0]=0`, which is now impossible.  So the
  frame never widens again — back to the previous case, contradiction.

Hence rule 5 fires infinitely often and `StD` is live.  ∎

The parity is the load-bearing part: **after the first rule 1 of an epoch
the head is locked to odd positions, and the only exit from the odd class
is rule 5 itself.**  M4's `StD` yields to the same argument transported
through §2b.

With this, M1 and M4 need `StA`, `StB`, `StC` as well — and those are
already available off the shelf: `tools/reachsti/cert_search.py` returns
`ReachStI` certificates for M1's A `(B=0,C=1)`, B `(B=4,C=1)` and C
`(B=0,C=1)`, and `tools/reachsti/sweep.py`'s closure engine covers A, B, C
on M4.  So **each of M1 and M4 is one formalised argument away from a
board**, and that argument is section 4.

## 5. M2 and M3: the counter is clean, the blocker is the abstraction

M2's anchor family is exact and consecutive.  At every configuration in
`StA` whose left half-tape is blank, the tape reads

    Cf(n) = (StA, ([], S0, R(n)))

where `R(n)` spells `n` in base 2, **LSB first, two cells per digit**,
`0 -> 00`, `1 -> 01`, top digit always `01` — and the anchors occur with
`n = 0, 1, 2, 3, ...` consecutively, no gaps.  The lap from `n` to `n+1` is

    6 + 7*(3^c - 1)/2 + c        c = number of trailing 1-digits of n

(checked `c = 0..4`), so the carry is `Theta(3^c)` — the `EXP3` label in
`tools/closeout/residue_map.tsv` is measuring this correctly.  M3 is the
same family (the rows differ only in `B0`, `1LB` vs `1LC`).

Because the state gaps are `O(width)` (§3), a `ReachStI`-style board is
*possible in principle* for all four states.  It does not work today, and
the reason is exact:

* `cert_search.py` covers only `StC`.
* `tools/mxdys4/certE.py` (extent measure `Be*ext l + Ce*ext r`, which is
  the right shape — the sweeps are bounded by the distance to the outermost
  `1`, not by the count) and `certM.py` / `certM3.py` (k-cell window plus
  capped extents `min(ext, 2)` and `min(ext, 3)`) all still fail on A, B, D.
* The blocking cycle is always the **same spurious node**:
  `C |0[0]0  ext l = 0` — state `C` reading `0` with the left half-tape
  entirely blank, whose `C0 -> 0LC` self-loop sweeps left forever.  It is
  *not* in the real orbit (M2's `C` always reads `1` when it reaches the
  blank region, and turns into `D`), but every local abstraction tried here
  generates it, because "the leftmost `1` sits exactly at the head" is not
  a bounded-window fact.

So the sized next piece for M2/M3 is an invariant that can say *"the left
half-tape is non-blank"* and keep saying it — i.e. a genuine regular
half-tape invariant (a suffix-closed DFA condition, which `ctape_move`
supports: `DR` takes a tail, `DL` prepends one known cell), not a wider
window and not a deeper extent cap.  Both of those were measured here and
both fail.

## 6. What is left

| row | StA | StB | StC | StD | remaining |
|---|---|---|---|---|---|
| M1 | ReachStI | ReachStI | ReachStI | §4 | formalise §4 + §2a |
| M4 | closure | closure | closure | §4 transported | formalise, + §2b |
| M2 | — | — | ReachStI | — | §5's regular invariant |
| M3 | — | — | ReachStI | — | §5's regular invariant |

The M1/M4 job is the smaller one and it is fully specified: the four macro
rules of §2a as `csteps` lemmas over `rep S1 R` (the scan lemmas in
`Counters/WTape.v` already cover the `B`/`D` runs), then §4's induction on
`2^w - N(W)`, then `StD`'s liveness composed with the three existing
`ReachStI` certificates under a `destruct q`.

## 7. Tools

`tools/mxdys4/` (UNTRUSTED, like everything under `tools/`):

* `sim.py` — raw simulator.
* `macro1.py` — M1's macro rules + the differential validation, and a
  labelled macro trace.
* `macro4.py` — M4's macro rules + validation.
* `extract.py` — automatic macro-rule extraction: run from a symbolic
  config to the next `StA` configuration and print the transformation.
  This is how §2b was derived; point it at any row with a unary half-tape.
* `gaps.py` — §3's table: worst visit gap per state against tape width.
* `certE.py`, `certM.py`, `certM3.py` — the extent / windowed-extent
  measure searches, with the closure computed from the real orbit.  They
  return the blocking negative cycle when they fail, which is what located
  §5's spurious node.
* `rows.txt` — the four rows.
