# Wave 36 — mxdys's four "easy" rows, read end to end

mxdys handed over four rows as easy:

    1RB1LC_0LC0RB_1LA1RD_0LA0RD      (M1)
    1RB1LC_1LB1RA_0LC0LD_0RA0RD      (M2)
    1RB1LC_1LC1RA_0LC0LD_0RA0RD      (M3)
    1RB1LD_1LC1RA_0RB0LC_0RA0LD      (M4)

**M1 and M4 are now BOARDED** (`theories/Machines/Mxdys4/NGX_*.v`, wave 37;
see section 8).  M2 and M3 are not.

What wave 36 produced is the mathematics: complete, validated macro-rule
systems for M1 and M4, a proof of the one liveness obligation that had no
route before, the exact counter reading for M2/M3, and — the result most
worth carrying — a **permanent negative** that rules the whole `ReachSt`
tier out of M1 and M4 forever, so no future session spends a day
re-measuring it.  Wave 37 transcribed sections 2a/2b/4 into Coq and closed
M1 and M4 with them.

Everything below that is a measurement was produced by a tool in
`tools/mxdys4/`; sections 2a, 2b, 4 and 4a are now also Coq, section 8
says where.

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

### 3a. The same test over the WHOLE core list, and it splits 13/2

`gaps.py` is not specific to these four; it is a cheap a-priori triage for
the tier on any row.  Run over the 15 core rows open when this wave ran (3M
steps each), worst gap of any state against the final tape width.  (#118 has
since boarded the six `1RB---` rows and #120 the `1RB1RC_1LA0LB_..` row,
leaving **eight** — and **four of those eight are this wave's four**, so the
table below is the whole remaining problem plus the seven that went out by
another route.)

    1RB---_0LC1RD_1LB1RC_1LB0RD    width 28    worst C   30    ratio 1.07
    1RB---_0LC1RD_1LB1RD_1LB0RD    width 28    worst C   31    ratio 1.11
    1RB---_1LC0RB_0LD1RB_1LC1RB    width 28    worst D   31    ratio 1.11
    1RB---_1LC0RB_0LD1RB_1LC1RD    width 28    worst D   30    ratio 1.07
    1RB---_1LC1RB_0LB1RD_1LC0RD    width 28    worst B   30    ratio 1.07
    1RB---_1LC1RD_0LB1RD_1LC0RD    width 28    worst B   31    ratio 1.11
    1RB0RB_0LC1RD_1LC1LA_0LA1RB    width 28    worst D   31    ratio 1.11
    1RB0RB_1LC0RC_1RA0LD_0LB0LC    width 2255  worst D 5985    ratio 2.65
    1RB0RD_1LB1LC_1RC0RA_0LB1RD    width 39    worst A   39    ratio 1.00
    1RB1LC_0LC0RB_1LA1RD_0LA0RD    width 32    worst D 262170  ratio 8192.81   DEAD
    1RB1LC_1LB1RA_0LC0LD_0RA0RD    width 27    worst B   32    ratio 1.19
    1RB1LC_1LC1RA_0LC0LD_0RA0RD    width 27    worst B   32    ratio 1.19
    1RB1LD_1LC1RA_0RB0LC_0RA0LD    width 31    worst D 196633  ratio 6343.00   DEAD
    1RB1RC_1LA0LB_1LD0RD_1LB0RC    width 26    worst C   48    ratio 1.85
    1RB1RC_1LA1RA_0RC1LD_1LB0LD    width 53    worst C   55    ratio 1.04

**Thirteen of the fifteen sit between 1.00 and 2.65** — a linear measure is
not ruled out on any of them, on any state, and `1RB0RB_1LC0RC_..`'s 2255-cell
tape at ratio 2.65 says the test is not just seeing small tapes.  **Two are
four orders of magnitude out.**  There is no middle: the core list is either
comfortably inside the tier's reach or hopelessly outside it, and this one
command says which.  For the thirteen, `docs/REACHST_TIER.md`'s route is
still open and every "missing q" the sweeps report is a search gap worth
attacking; for the two, it is a wall and the counter must be read instead.

## 4. THE POSITIVE: `StD` on M1 is live

> **NOW KERNEL-CHECKED** (wave 37).  This section was written as a
> pen-and-paper argument on the macro system of §2a; it has since been
> transcribed into
> `theories/Machines/Mxdys4/NGX_1RB1LC_0LC0RB_1LA1RD_0LA0RD.v`, where the
> four rules are `csteps` lemmas and the argument below is `hitD_IO` /
> `hitD_IE` / `g_step`.  Section 8 records the two places the transcription
> needed more than the prose says.

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

### 4a. The measure, in the form Coq wants (this is the form Coq got)

`N(W)` needs the frame; the equivalent quantity written straight on the
`cconf` `(StA, (l, s, rep S1 R))` does not.  With `vall l` the left
half-tape read as a binary number, **nearest cell the least significant**
(`vall [] = 0`, `vall (b :: t) = sval b + 2 * vall t`),

    mu (l, s, R)  =  2^R * (2 * vall l + sval s + 1)          [ = N(W) + 1 ]

and the per-rule deltas are exact, with no frame in sight:

| rule | delta |
|---|---|
| 1 | `+2` |
| 2 | `+2^R` |
| 4 | `+2^(R+1)` |
| 5 | `-(2^(R+1) - 1)` |

The bound is `mu <= 2^w` for `w = length l + 1 + R`, and **`w` is preserved
by all four rules** (rule 1: `length l' = length l + R - 1`, `R' = 1`;
rule 4: `-2` and `+2`; rule 5: `+R+1` and `R' = 0`).  So the induction is
on `2^w - mu`, with `w` carried as proof-level data alongside the
`cconf` and `length l = w - 1 - R` as part of the invariant.

Head position `p = length l`, so "p odd" is "`length l` odd" and the
frame's cell 0 is `last l`.  All of §4 in those terms: rules 1, 2 and 4
preserve `length l` odd and `last l = S1`, no widening is enabled
(`length l = 1` with `last l = S1` means `l = [S1]`, which is rule 5's
guard), and `2^w - mu` strictly decreases.

Both lemmas — the four deltas and the parity lock — were checked over 4000
macro steps with zero exceptions (`tools/mxdys4/cmacro1.py` carries the
rules in exactly these `cconf` coordinates and runs the check; it also
re-validates every rule against the raw simulator).  They are now the Coq
lemmas `mu_r1` / `mu_r2` / `mu_r4` and `hitD_IO`.

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

| row | StA | StB | StC | StD | status |
|---|---|---|---|---|---|
| M1 | closure k=3 n=2 | closure | closure | §4, in Coq | **BOARDED** |
| M4 | closure k=3 n=2 | closure | closure | §4 transported, in Coq | **BOARDED** |
| M2 | — | — | ReachStI | — | §5's regular invariant |
| M3 | — | — | ReachStI | — | §5's regular invariant |

The M1/M4 job was the smaller one and it went exactly as specified: the
macro rules of §2a/§2b as `csteps` lemmas over `rep [S1] R` (the `cycR` /
`cycL` scan lemmas in `Counters/WTape.v` cover the `B`/`D` and `C`/`D`
runs), then §4's induction, then `StD`'s liveness supplied as the premise
of `NGramHistExt.ngramhist_check_neverqh_lex_ext_sound`.  The `ReachStI`
certificates of §4's last paragraph were not needed: at `k=3, n=2` the
`NGramHist` closure covers `StA`, `StB` and `StC` on both rows on its own.

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

## 8. Wave 37: M1 and M4 boarded, and what the transcription actually cost

`theories/Machines/Mxdys4/NGX_1RB1LC_0LC0RB_1LA1RD_0LA0RD.v` and
`NGX_1RB1LD_1LC1RA_0RB0LC_0RA0LD.v`: ~510 and ~533 lines of hand proof plus
the emitted certificate data, four seconds each to compile,
`functional_extensionality_dep` only.  Shared kit:
`theories/Counters/BinVal.v` (the half-tape as a binary number, the parity
predicates, the `last` algebra).  The closure half is emitted by
`tools/mxdys4/emit_ngx.py`, which rewrites everything after a MARK line and
leaves the hand proof above it alone.

- **`k=2, n=2` DOES NOT CLOSE either row; `k=3, n=2` does.**  At `k=2` the
  closure misses `StB` on M1 and `StC` on M4 (`no liveness cert for state
  ...`), and `n=3` does not close at all.  `tools/mxdys4/pin_kn.py` sweeps
  the grid; 134 and 131 contexts at the rung that works.  §4's plan to take
  `StA`/`StB`/`StC` off `ReachStI` was therefore unnecessary.

- **THE SHAPE MUST CARRY AN EXPLICIT BLANK AND THEN A GENERIC TAIL.**  The
  configuration is `(StA, (l, s, rep [S1] R ++ S0 :: Z))`, not
  `(StA, (l, s, rep [S1] R))` and not `... ++ Z`.  Both halves matter and
  for opposite reasons: rules 1 and 5 both walk ONE cell past the unary run
  and must find a blank there, so the `S0 ::` has to be in the statement;
  and rule 1 consumes that blank and writes a fresh one, so without a
  generic `Z` underneath it the output of one rule does not syntactically
  match the input of the next and the whole chain has to be re-aligned by
  hand at every join.  With both, `Z` is untouched by all four rules and
  every rule lemma composes by `csteps_chain` with no rewriting at all.
  M4 is the same one cell to the LEFT: `rep [S1] p ++ S0 :: Y`.

- **§4's "suppose rule 5 fires finitely often" does not transcribe.  What
  does is a predicate closed under ONE macro rule.**  The proof-by-
  contradiction shape needs a global "after the last rule 5", which is not
  a statement about a configuration.  The Coq form is two obligations over
  a disjunction `G`:

      hitD_G : G  ->  StD is visited within finitely many steps
      g_step : G  ->  one macro rule lands in G again, in >= 1 steps

  and then `forall N, exists m >= N` by induction on `N`.  §4's parity
  invariant is only ONE disjunct of `G`.  Rule 5 LEAVES it (it sets
  `R := 0`, and `R` is odd in the invariant), so `G` also carries the
  even-parity companion and the blank-tape states `l = []` / `r = []` the
  frame widens through.  Four disjuncts on M4, three on M1.

- **The two phases need DIFFERENT measures, and that is the real content.**
  The odd phase descends on `2^w - mu`, §4a's measure, and it is the phase
  where the exponential lives.  The even phase does not: it descends on
  `length l` (M1) resp. `length r` (M4), because rule 4 / rule 1 shortens
  the counter side by two cells per firing and every other exit leaves the
  phase in one step.  Trying to run the even phase on `mu` fails — that is
  exactly where widening lives, and widening raises `2^w - mu`.

- **The parity lock is what forbids widening, and it is worth stating as
  `last l = S1` AND a parity, never one without the other.**  `last l = S1`
  alone fails: `l = [S0; S1]` steps to `l = []`.  Parity alone fails: the
  widening guard is a length, not a parity.  Together, `length l = 1` forces
  `l = [S1]`, which is rule 5's guard and not rule 4's, and the frame cannot
  widen.  Same statement on M4 with `r` for `l`.

- **`apply H in Hyp` where `H : A <-> B` picks a direction by LUCK.**  With
  `H : forall n, OddN (S (S n)) <-> OddN n` and `Hyp : OddN (S (S k))`,
  BOTH sides unify (the second with `n := S (S k)`) and Coq took the wrong
  one, silently turning the hypothesis into `OddN (S (S (S (S k))))`.  The
  failure surfaces four tactics later as an unprovable `lia`.  `BinVal.v`
  therefore states the two implications separately (`oddN_SS_inv`,
  `oddN_SS_intro`) and never the `iff`.

- **M4 has a genuine 2-cycle in its macro system and it is harmless.**
  Rule 3' (`p = 0`, head reads `S1`) returns the identical configuration in
  two steps.  It is not in the real orbit, but it does not have to be
  excluded: it visits `StD` on its first step, so it satisfies the
  obligation on the nose and only needs to be closed under `G`.  M1 has the
  analogous rule-5-at-`R=0` cycle, and there the parity invariant excludes
  it instead — either treatment works, and picking the cheap one per row
  saved a case split each time.

- **The rules were re-derived in `cconf` coordinates before any Coq.**
  `tools/mxdys4/cmacro1.py` and `cmacro4.py` carry §2a/§2b as functions of
  `(l, s, R)` resp. `(p, s, r)` — the exact triples the Coq lemmas are
  stated over, including `chd`/`ctl` at the list ends — and differentially
  validate them against the raw simulator (300/300 macro steps each) plus
  the four `mu` deltas and the parity lock (4000 macro steps).  The frame
  form of §2a hides two things the `cconf` form must say: which rules read
  past the run, and what happens at `l = []` versus `l = [S0]`.

- **A D-free run from an ARBITRARY shaped configuration does not
  terminate**, so the invariant is not decoration.  From `(l, s, R) =
  ([], S0, 1)` on M1 and `(p, s, r) = (1, S0, [])` on M4 the macro system
  widens forever without ever visiting `StD` (measured to 200k macro
  steps).  Both are parity-broken; neither is reachable.

- **Both rows carry exactly one `0RB` shadow** (`0RB0LA_1LC1RD_0RD0LC_1RB1LA`
  and `0RB0LA_1RC1LA_1LD1RB_0RC0LD`), harvested by `make closeout` in the
  same regen.
