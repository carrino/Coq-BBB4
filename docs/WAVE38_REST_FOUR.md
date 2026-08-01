# Wave 38 — the last four core rows, measured end to end

After wave 37 (mxdys's M1/M4) and the parallel base-2 pair board, the core
undecided list is exactly four rows:

    1RB0RB_1LC0RC_1RA0LD_0LB0LC      (row 1)
    1RB0RB_0LC1RD_1LC1LA_0LA1RB      (row 2, "the phi row")
    1RB0RD_1LB1LC_1RC0RA_0LB1RD      (row 3, Drozd's sixth)
    1RB1RC_1LA1RA_0RC1LD_1LB0LD      (row 4, KCOPY3)

This wave produced one piece of Coq that was missing outright, a
**permanent negative** on row 1 that closes off the route the row was
queued for, a **decisive reconciliation** of the two documents that
disagreed about row 2, and complete or near-complete macro systems for the
two rows that turn out to be word-rewriting systems.  No row boarded.

## 1. The lever test, run on all four (and it splits them 2–2)

Wave 36's reusable lever: a row whose orbit keeps ONE half-tape a bare
unary run is a finite word-rewriting system, and `extract.py` reads the
rules off.  `tools/mxdys4/cconf_rules.py SPEC --scan N` is this wave's
mechanised version of the test — it walks the real orbit, reads each `StA`
configuration off in the `cconf` triple `(l, s, R)`, and counts how often
the right half fails to be `1^R` then blanks.

| row | impure right halves / 60,000 StA configs | max \|l\| | max R | verdict |
|---|---|---|---|---|
| row 1 | 59,984 | 565 | 3 | lever does NOT apply |
| row 2 | **0** | 21 | 21 | **LEVER APPLIES** |
| row 3 | **0** | 31 | 29 | **LEVER APPLIES** |
| row 4 | 29,993 | 42 | 3 | lever does NOT apply |
| M1 (control, boarded wave 37) | 0 | 24 | 24 | applies, as known |

Rows 2 and 3 were re-checked at 2,000,000 raw steps with 0 violations.

The test was also run in a strictly weaker form on rows 1 and 4 — a
half-tape of the shape `(bounded inner junk) w^p (bounded outer junk)` for
every block `w` of length ≤ 4 and junk ≤ 8 on each end, and gated on each
state separately rather than at every step, so that a row whose invariant
only holds at macro boundaries would still be caught.  **Rows 1 and 4
survive none of it.**  Row 1's `LADDER_NOFAM.md` reading `phi·(101)^p·0011111`
is a WHOLE-TAPE shape with the head inside it, not a half-tape invariant,
which is why the block search finds nothing.

The two rows that fail the lever are exactly the two with `max R = 3` — the
unary run never grows, because the counter lives on the other side and is
not unary.

## 2. Row 1 — the combinator now exists, and the route it was queued for
   does not

### 2a. `theories/Checkers/LiveAll.v`

`ReachStI.reach_sti_recurs` certifies `StA`, `StB` and `StC` on this row
(`tools/reachsti/cert_search.py`: `B=3,C=0`, `B=1,C=0`, `B=0,C=0`), each as

    forall N, exists m, N <= m /\ VisitsAt tm q m

and `NeverQuasiHaltsSt` is exactly that quantified over `q`.  The closer
that turns four such facts into the theorem did not exist anywhere in
`theories/` — every previous board reached `NeverQuasiHaltsSt` through a
checker that produces it whole, which a row with no `NGramHist` coverage
cannot use.  `neverqh_of_live4` is five lines (`intros q _ N; destruct q`)
and discards the `Visited` hypothesis, so it is strictly stronger than
`NeverQuasiHaltsSt` needs.  `nonhalt_of_live` gets `NonHalt` from any ONE
live state without going through `Visited` at all.

### 2b. `StD` is PERMANENTLY outside the `ReachStI` tier

`cert_search.py` was pushed from its default `B,C <= 4` to `B,C <= 60`:
still `NONE`.  That is not a budget result.  For each fixed `(B,C)`
Bellman–Ford is complete — it returns the pointwise-least `rk` or proves
infeasibility — so the search is exhaustive per constant, and infeasibility
for all `(B,C) >= 0` follows from a single structural witness:

    (StA, chd l=1, head=1, chd r=0)
      --A1 = 0RB-->  (StB, 0, 0, 0)
      --B0 = 1LC-->  (StC, 0, 0, 1)
      --C0 = 1RA-->  (StA, 1, 1, 0)

a 3-step cycle in the `StD`-avoiding graph on which `ones l` increases by 1
and `ones r` is unchanged.  `drop_ok`'s measure is
`mu = B*ones l + C*ones r + rk(q, chd l, h, chd r)` and must strictly drop
on every `StD`-avoiding step; around this cycle `rk` returns to its start
while `B*ones l` grows, so `mu` cannot drop for any `B, C >= 0`.  None of
`StA`, `StB`, `StC` is `StD` and none of the three transitions targets
`StD`, so the cycle is genuinely `StD`-avoiding.  Verified against the
table by hand.

### 2c. The three states are banked, in the kernel

`theories/Machines/Rest4/R3_1RB0RB_1LC0RC_1RA0LD_0LB0LC.v` — the `StA`,
`StB` and `StC` certificates, emitted by `tools/reachsti/emit.py` and
re-checked by `vm_compute` inside each proof, restated as
`LiveSt tm q` (the shape `neverqh_of_live4` consumes) and with `NonHalt`
derived from one of them through `nonhalt_of_live`.

It is deliberately **three lemmas and no theorem**: the row is still
unproven and the closeout inventory correctly leaves it that way, because
the file contains no `NeverQuasiHaltsSt`.  If `StD` ever falls to another
engine, `neverqh_of_live4` closes the row in one line from these three plus
that one.  The file also serves as the worked example of `LiveAll.v` in
use.

**So row 1 has three of four states and cannot get the fourth this way.**
With the lever also excluded (section 1), row 1 needs a different engine.
Its gap ratio of 2.66 remains correct and remains inside the tier; the
ratio says the tier is *not excluded by recurrence speed*, and this section
says it is excluded by measure shape.  Those are different obstructions and
the gap ratio was never evidence against this one.

### 2d. But the row is QUADRATIC, and that is the lead

`LADDER_NOFAM.md`'s unary-stripe reading (lines 90, 148, 169) is right, and
measuring it gives the growth law nobody had written down.  The right end
of the tape is a fixed suffix `…11011011011011011010011111` for the whole
run, and the stripe count `p = #011` grows while the left region fills with
`1`s and drains (`ones` swings between 294 and 1,744 at consecutive
samples).  The first step at which `p` reaches a given value:

| p | first t | t / p² |
|---|---|---|
| 20 | 178,000 | 445.0 |
| 44 | 848,000 | 438.0 |
| 68 | 2,014,000 | 435.6 |
| 92 | 3,678,000 | 434.6 |
| 116 | 5,840,000 | 434.0 |

**`t ≈ 434 p²`, converging cleanly, with the tape width linear in `p`.**

So row 1 is a **quadratic** unary counter — the only polynomial row of the
four.  Rows 2 and 3 are Fibonacci counters with exponential laps; row 1 is
not in that family at all, which is exactly why the word-rewriting lever
does not read it and why `max R = 3`.  Its laps are `O(p) = O(width)` and
there are `p` of them, which is where the 2.66 gap ratio comes from.

The obvious inference from that shape — "so point `RepWL` at it" — **was
checked and is wrong.**  Row 1 is already a survivor of BOTH committed
RepWL sweeps (`tools/repwl2_survivors.txt` line 2753,
`tools/repwl_residue_survivors.txt` line 3102), which ran the rung ladder
out to `(L,T) = (6,4)`.  Block length 6 covers the period-3 `011` stripe
comfortably, so this is not a rung-size gap and widening the ladder is the
same trap as widening `maxBC` was in §2b.

So row 1 has no open route among the existing engines: `ReachStI`
permanently dead for `StD`, the lever inapplicable, the `NGramHist` closure
covering nothing, and `RepWL` swept.  What the quadratic law changes is the
TARGET rather than the tool — the row wants a quadratic-counter argument,
which is a different animal from rows 2 and 3's Fibonacci counters and
closer to the shapes already in `theories/Counters/` (`LinCarry`,
`Sep2Counter`).  Nobody has read this row against those, and that is the
one honest next experiment; it is not a search, it is a hand reading.

## 3. Row 2 — the phi reading is CONFIRMED, exactly, and the docs are
   reconciled

`docs/RESIDUE_MAP.md` calls this row the cheapest lead and reads it as
`phi` at spread 0.00; `docs/LADDER_PLAN.md` §4s says flatly "no family at
any anchor, file it with the no-anchor bucket".  Measured on the current
tree, **RESIDUE_MAP is right and LADDER_PLAN §4s is a statement about the
EMITTER, not about the machine** — exactly as RESIDUE_MAP predicted.

The measurement is not a ratio fit.  Running the validated macro system
(section 3a) and recording the first macro step at which the counter
reaches `n` digits:

| n | first macro step | Fibonacci |
|---|---|---|
| 19 | 17,709 | F(22) − 2 |
| 20 | 28,656 | F(23) − 1 |
| 21 | 46,366 | F(24) − 2 |
| 22 | 75,024 | F(25) − 1 |
| … | … | … |
| 28 | 1,346,268 | F(31) − 1 |
| 29 | 2,178,307 | F(32) − 2 |

**Exactly Fibonacci**, alternating offset −2 / −1, out to F(32); the ratio
converges to 1.61803.  This is a phi row.

The tape is correspondingly tiny: **28 cells wide after 3,000,000 raw
steps**, growing like `log_phi t`.  That is what makes the gap ratio 1.11
and it is why every "missing q" here was always a search gap.

### 3a. The macro system — six rules, exhaustive, differentially validated

`tools/mxdys4/cmacro2.py`, in the `cconf` coordinates a Coq proof is
written in, over `(StA, (l, s, rep [S1] R ++ S0 :: Z))` — explicit blank
AND generic tail, for the two reasons §8 gives:

| # | guard | action | steps |
|---|---|---|---|
| 1 | `s=S0, R=0` | `(ctl l, chd l, 1)` | 3 |
| 2 | `s=S1, R=0, l = 0^j 1 l1` | `(ctl l1, chd l1, j+2)` | j+4 |
| 3 | `s=S0, R=2k+1` | `(1^(2k+1) ++ l, S1, 0)` | 2k+3 |
| 4 | `s=S0, R=2k+2` | `(1^(2k+1) ++ l, S1, 1)` | 2k+5 |
| 5 | `s=S1, R=2k+1` | `(1^(2k) ++ S0::l, S1, 0)` | 2k+3 |
| 6 | `s=S1, R=2k+2` | `(1^(2k) ++ S0::l, S1, 1)` | 2k+5 |

4,000 macro steps differentially validated against the raw simulator, 0
mismatches, 0 impure right halves.  Every rule fires (1:1, 2:1527, 3:8,
4:7, 5:1520, 6:937).

Rules 3/4 and 5/6 push the SAME word onto `l` and differ only in the
leftover `R'` and the step count — the parity structure §8 says to expect.
`Z` is untouched by all six.

### 3b. Liveness reduces to ONE obligation, and it is the invariant

Measured state coverage per rule firing, and the resulting recurrence gaps:

    rule 1 -> A B C      rule 3 -> A B D      rule 5 -> A B D
    rule 2 -> A B C      rule 4 -> A B C D    rule 6 -> A B C D

    max gap between macro steps visiting D: 2
    max gap between macro steps visiting C: 2

`StA` is the macro boundary itself and `StB` is visited by every rule, so
both are free.  `StC` and `StD` each follow structurally within 2 macro
steps, with no invariant needed:

* `R >= 1` fires 3/4/5/6, all of which visit `D`; `R = 0` fires 1 or 2,
  which set `R' >= 1`, so `D` follows next step.
* `R = 0` fires 1 or 2, which visit `C`; `R` even fires 4 or 6, which visit
  `C`; `R` odd sets `R' = 0`, so `C` follows next step.

**So all four liveness obligations hold as soon as the macro system never
gets stuck**, and the whole remaining cost of this row is that one fact.

Rule 2 is PARTIAL: it needs a `S1` in `l`.  On an all-blank left half-tape
the machine sweeps left forever in `StC` and never returns to `StA` — and
that is a genuine quasihalt (only `StC` recurs), so it must be excluded,
not waved past.  This is the same shape as M1/M4's "a D-free run from an
arbitrary shaped configuration does not terminate".

### 3c. What blocks it, stated precisely

`In S1 l` is **not** closed under the rules, and neither is the obvious
repair.  Two facts, both measured:

* `R = 0 -> s = S1` **is** closed under all six rules (rules 3/5 are the
  only producers of `R' = 0` and both set `s' = S1`; rules 1/2 set
  `R' >= 1`).  It also kills rule 1 after the transient — rule 1 fires
  exactly once, at macro step 0, in 300,000 macro steps.
* The dangerous transitions are rules 5 and 6 at `k = 0`, which push only
  `[S0]` onto `l` and so cannot replenish it.  Chasing closure through them
  regresses: `(·,S1,0)` needs `(·,S1,1)` safe, which needs `(·,S1,2)` safe,
  which lands back on rule 2's output `(ctl l1, chd l1, 2)`.

Measured over 200,000 macro steps, at every rule-2 configuration the cell
after the first `S1` is ALSO `S1` (`l = 0^j 1 1 …`), and `l` is 1-free only
in configurations with `s = S0` and `R >= 3` (21 of 300,000).

### 3d. The composite step, which is where the next session should start

Rules 3–6 always leave `R' <= 1`, and `R' = 1` is immediately consumed by
rule 5 at `k = 0`.  So `R` is only ever large transiently, and composing
rule 2 with the rule that consumes its output gives a SINGLE self-map `T`
on the left word alone, taken at `(s = S1, R = 0)`.  Writing words
nearest-cell-first and implicitly `0^∞`-terminated, `w = 0^j 1 a l2`:

| case | `T(w)` |
|---|---|
| `a=S0`, `j` odd | `1^(j+2) l2` |
| `a=S0`, `j` even | `0 1^(j+1) l2` |
| `a=S1`, `j` odd | `1^(j+1) 0 l2` |
| `a=S1`, `j` even | `0 1^j 0 l2` |

**`T` is LENGTH-PRESERVING** — all four cases give `|T(w)| = |w|` — so the
whole row is a shift register on `0^∞`-terminated words, and the growth
seen in `|l|` is only trailing blanks being consumed and released.  This is
a much smaller object than the six-rule system and is the right thing to
state the invariant over.

Two facts about `T` that bound the problem:

* `ones(T(w)) >= ones(w)` in every case EXCEPT `j = 0, a = S1` — i.e. `w`
  beginning `11` — where it drops by exactly 2.  So the counter can only
  drain through a leading `11`.
* The stuck set is `{0^∞}`, and its preimage chain is
  `… -> 0^2 1 1 0^∞ -> 0 1 1 0^∞ -> 1 1 0^∞ -> 0^∞`.  But `0^i 1 1 0^∞`
  for `i >= 2` ALSO has the preimage `1 1 0^(i-2) 1 1 0^∞`, which has four
  ones and is not itself of the doomed shape — **so the doomed set is not
  closed downward and "avoid words with two ones" is not the invariant.**
  This is the trap to know about before starting.

Measured: 400,000 `T` steps from the real orbit's first `(S1, 0)` word
never stick, `ones` ranges over 1…27, and no doomed word occurs.

**There is no linear potential.**  Fitting `nu(w) = Σ_{w[i]=1} c_i` with
`nu(T(w)) = nu(w) + 1` over 200 orbit words leaves 185 inconsistent
equations, so the value function is not a weighted digit sum and the parity
of `j` genuinely enters.  That is why this is a carry analysis and not an
odometer argument.  `LadderFam`'s `Fib`, `FibL` and `fam_lo` are the right
vocabulary and already exist; the missing piece is the characterisation of
`T`'s reachable set.  Budget it as a wave, not a tidy-up.

**This is the cheapest row left and the one to start the next session on.**
Everything except the invariant is done and validated.

## 4. Row 3 — Drozd's sixth also passes the lever, and most of it is read

The lever applies (section 1), which the Drozd lap fit did not predict.  In
`cconf` coordinates the clean rules are:

| # | guard | action | steps |
|---|---|---|---|
| 1 | `s=S0, R>=1` | `(S0::l, S1, R-1)` | 3 |
| 2 | `s=S0, R=0, l = S1::l1` | `(S0::l1, S1, 1)` | 4 |
| 3 | `s=S0, R=0, l = S0::l1` | `(S0::S1::l1, S1, 0)` | 5 |
| 4 | `s=S1, R=1` | `(S0::S1::l, S0, 0)` | 6 |
| 5 | `s=S1, R>=2` | `(S0 :: 1^(R-2) ++ S0::l, S1, 0)` | R+4 |

Rule 5 was checked uniform for `R = 2 … 14`; `R = 1` is the one exception
(it lands in `s' = S0`) and is rule 4.

**The sixth rule, `s=S1, R=0`, is the leftward sweep and is NOT yet in
closed form.**  It depends on the leading two cells of `l` and, deeper, on
the run structure — it is this row's carry.  Measured values are in the
grid (`tools/mxdys4/cconf_rules.py SPEC`); e.g. `S1::S1::l2 -> (S0::l2,
S1, 1)` in 5 and `S1::S0::l2 -> (S0::S1::l2, S1, 0)` in 6, but the `S0::S1`
cases open a deeper sweep.

This is consistent with, and sharper than, the lap fit recorded in
`NEXT_SESSION.md`: a doubling composed with a sweep affine in `i` is
exactly what rule 5's `R+4` plus the sweep produces.  It remains a hand
board, and the macro-system route now looks cheaper than the reset-family
route it was budgeted as.

## 5. Row 4 — nothing was lifted, as expected

`KCOPY3`, right wall, `+9` cells per `8x` steps
(`docs/RESIDUE_708_DIAGNOSIS.md`).  The lever does not apply (section 1;
`max R = 3`, the counter is on the other side and is not unary).
`cert_search.py` at `B,C <= 25` gives `StC` only (`B=1,C=4`) and `NONE` for
`StA`, `StB`, `StD`.  The `NGramHist` closure discharges only `StC`.  It is
the hardest of the four and nothing here changes that.

## 6. What was measured dead, so nobody re-runs it

* **`cert_search.py` on row 1 `StD` at any `(B,C)`** — section 2b, with the
  structural witness.  Same for rows 2/3/4 at `B,C <= 25`: row 2 `StC`
  only, row 3 nothing at all, row 4 `StC` only.
* **`pin_kn.py` on rows 2 AND 3**, all eight `(k,n)` rungs × all four
  `qext` (64 runs).  Row 2 reports `no liveness cert for state A`
  everywhere; row 3 reports `closure did not close` at five rungs and `no
  liveness cert for state A` at the other three.  The `NGramHist` closure
  route that boarded M1/M4 does not open on either row — on row 2 the
  closure covers `StC` and nothing else, on row 3 nothing at all — so
  neither has anything to lift and `k`/`n` is not the knob.  Both must go
  out through their macro systems.
* **The block-run half-tape search on rows 1 and 4** — every block of
  length ≤ 4, junk ≤ 8 at both ends, gated per state.  Nothing survives.
