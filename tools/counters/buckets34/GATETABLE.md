# Gate table over the 1 open core row

`tailcert.py --list tools/closeout/core_rows.txt --out scan.json` (scan labels,
no --emit), split by `buckets.py`, filtered to live membership after each wave.
An exact partition of `core_rows.txt`.  Regenerate rather than trust: both
commands are untrusted Python and need no Coq.

| n | furthest gate |
|--:|---|
| 1 | `no_inner_interior_chain` |

**Six of the seven gates are EMPTY** — `register_step_does_not_close` and
`no_boot_chain` first, then `no_interior_j0_chain_at_octave_parity_0`
(wave 37), `no_inner_family_at_pow2_j` (#126), and
`no_interior_jS_j_chain_at_octave_parity_0` and
`no_gap_free_two_form_family` (wave 39).

**ONE ROW, and not one of the seven gates was ever answered.**  Every bucket
on this page emptied by someone re-reading a machine instead.  What follows is
kept as the record of how a gate label fails, not as a difficulty map.

## What is actually left

`no_inner_interior_chain` is 1 row: `1RB0RD_1LB1LC_1RC0RA_0LB1RD`, the last
undecided (4,2) core machine.  Its `residue_map.tsv` entry is a pair of
dashes — the emitter found no anchor, so it recorded no shape.  What is
actually known about it lives in `docs/WAVE38_REST_FOUR.md` §4: the lever
test APPLIES (0 impure over 2,000,000 steps), five of its six macro rules are
read in closed form, and the sixth — the `s=S1, R=0` leftward-sweep carry —
is the whole remaining problem.  Its fitted laps are `2^(2i+3) - 1` and
`48*4^i - 6i - 15`: a doubling composed with a sweep affine in `i`.

The last two rows to leave this page both left through entries 8 and 9 below.
`no_interior_jS_j_chain_at_octave_parity_0`'s final row was the φ row this
file spent four waves calling anchorless.

## What this table has been wrong about, nine times

A gate name says what stopped the emitter, never what stops a proof.  This
file has asserted nine verdicts that later measurement overturned.  The shape
of the mistake is the same every time and is worth more than any label in it:

1. **"The four QUADRATIC rows are not coming back without a new arm shape."**
   The arm measurement was right and was made three times — 4p on the arm,
   `docs/QUAD_TERMINAL_MEASUREMENT.md` independently, §4t a third time.  **All
   four boarded anyway, none with a new arm shape**: #115 took three as
   `Counters/LinC_*`, #116 the last as `Counters/BinCarry_*`.  The verdict
   bounded the LADDER and never the machines.  **Never read "closed as a ladder
   row" as "closed."**

2. **"The fibonacci rows have no anchor."**  Four waves searched for one.
   `radix_clock.py` reads `ratio = 1.6180` at spread 0.00 and the toggle counts
   satisfy `F(n) = F(n−1) + F(n−2)` exactly.  The anchor was always fine; the
   RADIX was wrong.

3. **"The six are Zeckendorf, weights 1,2,3,5,8."**  4s inferred that from a
   fit that had DROPPED A COLUMN — the counter's lowest digit is a constant 1,
   so `fit_weights` has a zero coefficient in a column that never varies and
   abandons the fit.  `1,2,3,5,8,13` is `1,1,2,3,5,8` with the bottom rung
   missing: the numeration the kernel already had.  Building `(Fib, 2)` would
   have produced a `fam_lim`, a weight ladder and a round trip that all exist.

4. **"Whether the new code reaches the remaining rows is unmeasured — that is
   an emitter run."**  It was measured, twice (§4s, §4v), and neither answer
   was "it reaches them" nor "the emitter refuses".

5. **"THREE are the BASE-3 block."**  Only one of the three was.
   `1RB1RC_1LA0LB_1LD0RD_1LB0RC` was probed and is base 3; the other two were
   called base 3 because they read `EXP3` and sit one transition from each
   other.  #120 swept both over every blank-side anchor, every 0/1/2-cell
   prefix and every 2-cell radix: **base 2, with a `3^c` lap.**  `EXP3` names
   the LAP, not the radix — `docs/CORE_3STATE.md` §2 says so in words, and
   `residue_map.tsv`'s own `Alph_11_00_1` names two digit words, so the label
   never claimed what this file read into it.

6. **"No closer in the tree glues a non-affine lap."**  Written on this page
   about the two `1RB1LC` siblings the moment #120 measured their laps as
   `3.5*3^c + c + 2.5` and `3*3^c + 2c + 1`.  The measurement was right and
   the conclusion did not follow.  #123 boarded both — with their two shadows,
   both `NeverQuasiHaltsSt` — off the **plain** `LapGlue.glue_neverqh`, at
   `Cf p = (StD, ([], S0, Wp p))` with `MonoCounter.Wp` verbatim and no
   offset.  **No closer needed to glue the lap, because `LapGlue`'s lap
   obligation is an existential over step counts**: the whole gap between the
   two laps rides inside that existential and is never written down.  The
   mathematics that WAS open was the cascade (`Bin3Lap.Hloop`), which is not
   what the lap shape pointed at.  `docs/RESIDUE_MAP.md` states the
   existential caveat two sections above where it made this claim.

7. **"`no_inner_family_at_pow2_j` is a nested-cascade row."**  Never stated
   here in those words, but it is what the label plus the TSV's `EXP2`
   interior said, and #126 measured **both fields wrong in the hard
   direction**.  The lap is AFFINE in the carry length (`6j+6` / `6j+4` /
   `6(S j)+2`, zero mismatches over 250,012 laps) because the counter's LSB
   sits against the wall, so an increment is local; `EXP2` was the growth of
   the RUN against the tape width, not the shape of a lap.  And the
   `Alph_000_111_111` field does not decode the row at all — `Ap` mismatches
   at 250,013 of 250,013 anchor visits, because the real numeral packs its
   top TWO digits into four cells instead of six.  The row went out by the
   ordinary `LapDecider` route with a new numeral (`Counters/Kc3Num.v`).
   `tools/counters/kc3lap.py`'s lap-per-`cview`-class table is the
   one-command test that separates "the emitter cannot find a family" from
   "the row is not that shape".

8. **"`1RB0RB_0LC1RD_1LC1LA_0LA1RB` finds no family at any anchor; it once
   counted with the fibonacci rows, it was never one of them."**  This file
   said that for four waves.  It was one of them.  Wave 39 settled it not with
   a ratio fit but with an exact identity: the first macro step at which the
   counter reaches `n` digits is `17,709 = F(22)-2`, `28,656 = F(23)-1`, ...,
   `2,178,307 = F(32)-2` — Fibonacci with an alternating `-2`/`-1` offset, out
   to `F(32)`.  Its tape is 28 cells wide after 3,000,000 steps, growing like
   `log_phi t`.  **"No family at any anchor" was true of the EMITTER and was
   written down as a verdict about the machine** — the same sentence, in the
   same file, that entries 1-7 are about.  It boarded in wave 39 with its
   shadow.

9. **"A FLAT toggle spectrum means the row is not a counter."**  Not from this
   file — from the session prompt written for wave 39, and it is the cleanest
   instance of the pattern on the page because the MEASUREMENT was right and
   only the inference was wrong.  `radix_clock.py` reads
   `1RB0RB_1LC0RC_1RA0LD_0LB0LC` at ratio `1.0013`, spread `0.00`, counts
   `[3069, 3068, 3064, 3062, ...]` — every cell alike, stable from 400k to 4M
   steps.  The prompt concluded "no radix, no digit, therefore no anchor to
   find; this is a SWEEPER, take it to `WTape.cycR`/`cycL`/`cycLW`, do not run
   counter probes at it."

   It is a **quadratic UNARY counter**.  A unary counter has no positional
   weighting, so a flat spectrum is exactly what it looks like — "flat" means
   "no radix", and "no radix" means "unary", not "not a counter".  The right
   end of the tape is a fixed suffix `...11011011011011011010011111`, the
   stripe count `p = #011` grows, and `t ~ 434 p^2` (`p=20` at 178,000, `p=116`
   at 5,840,000).  It wanted a quadratic-counter reading — `LinCarry`,
   `Sep2Counter` — and the bouncer machinery the prompt pointed at was the
   wrong shelf.  Wave 39 boarded it by hand off its lap system.

   Corollary worth keeping: `radix_clock.py`'s FLAT verdict is a positive
   reading, not a negative one.  It says "unary", and the tree has counters
   for that.

**The rows behind 1–4 all boarded.**  #118 took the six at `(FibL, 1)` — a
fourth CODE, not a second numeration: `fibdec`/`fibokb` pick the greedy
representative and these six stood on the LAZY one, so `LadderFam` gained
`FibL` with the decoder `fiblaz` (`fibdec`'s two-state automaton with the
transitions swapped), plus `fam_lo`, because what a weighted numeration really
costs the interface is a FLOOR — width `k` spells exactly
`[fibw k .. fibsum k]`.  **Behind 5 and 6, all three rows boarded too** — the
one that WAS base 3 in #120 (`Counters/Ter3WallD.v` + `LapGlueNeverIx.v`), the
two that were not in #123 (`Counters/Bin3Lap.v`), behind 7 the last `pow2 j`
row in #126 (`Counters/Kc3Num.v`), and behind 8 and 9 both wave-39 rows.  **So
every row this table has ever pronounced on is now decided, and it was wrong
about the route in all nine cases.**  One row is left and this file has never
said anything about it.

## `no_gap_free_two_form_family`: 10 -> 1, and the gate was never answered

Nine rows left this bucket in four waves and not one needed the gate answered:

* **4s took three.**  The champion `1RB1LD_1RC1RB_1LC1LA_0RC0RD` had a board
  that compiled since wave 33 and was held out by an arithmetic comparison in
  `inventory.py`.  The two gray rows closed once the searcher preferred, among
  readings tied on chain length, one whose digit words do not all end in a
  blank — a `cconf` carries no trailing blanks, so the other reading's boot
  check could never pass.
* **#114 took four** — the remaining `0RB` rows, all four bouncer counters.
* **#115 took one** (a doubling nested bouncer).
* **#116 took one** (a two-block bouncer, hand-boarded off
  `WTape.cycR`/`cycL`/`cycLW`) and its shadow.

## Wave 37: a bucket emptied where the gate was RIGHT, and permanently

Every other entry on this page is a gate that turned out not to bound the
machine.  Wave 37 is the other case, and it is worth more than any of them.

`no_interior_j0_chain_at_octave_parity_0` went 1 -> 0 and
`no_inner_interior_chain` 2 -> 1, on `1RB1LD_1LC1RA_0RB0LC_0RA0LD` and
`1RB1LC_0LC0RB_1LA1RD_0LA0RD`.  Both labels were correct.  Both were also
confirmed by a second, independent instrument: `tools/mxdys4/gaps.py` measured
`StD` on these two rows recurring on a `Theta(2^width)` schedule — gap ratios
8,192 and 6,343 against a linear measure — which is not a search failure and
no widening of the certificate class can fix (`WAVE36_MXDYS_FOUR.md` §3).
They were the only two rows on the core list outside the REACHST tier's reach,
and they still are.

**They boarded anyway, by changing what the object is.**  Read one half-tape
as a unary run and each row becomes a finite word-rewriting system — four
macro rules for one, three for the other — at which point `NGramHist` at
`k=3, n=2` closes three states and a hand measure on the macro rules closes
`StD`.  `theories/Machines/Mxdys4/NGX_*.v`.

So the lesson this page keeps teaching has a second half.  A gate label being
WRONG is the common case and the rest of this file documents it.  A gate label
being RIGHT — even corroborated by an orthogonal measurement, even provably
permanent — still says nothing about the machine, because the next wave can
re-read the machine as a different object and the label was only ever about
the old one.

## A shape worth remembering

Wave 4o briefly put two rows in `core_rows.txt` that were in none of these
lists — the 0RB shadows its four boards promoted.  A promoted shadow needs the
re-root transport, not a family, so it will never have a useful gate label.
Since #105 that case is handled without anyone noticing: `make closeout` runs
`gen_shadow.py --harvest`, which boards a freed shadow in the same regen as its
partner.  It first fired in anger in wave 4u, and every quadratic row's shadow
came that way.
