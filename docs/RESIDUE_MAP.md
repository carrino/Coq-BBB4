# The residue, characterised — the completed record

_How the last stretch of the (4,2) space was worked down to zero.  While
the closeout was live this page was the project's frontier: a map of the
machines no engine here had settled yet, published as a target list
rather than as an apology.  The list reached zero on 2026-08-01 —
Drozd's sixth, `1RB0RD_1LB1LC_1RC0RA_0LB1RD`, was the last row;
`audit.py` reports 5,156 of the frozen 5,156 settled — the `skipped`
disjunct is discharged (`not_skipped_nil`, `Closeout/BBB4_Value.v`), and
the value theorem `BBB4_value : BBB4_statement` (the claim of
`theories/BBB4_Spec.v`) is kernel-checked; see `docs/CLAIMS.md`.  The
page is kept as the per-row record of how each family fell, and for the
"what this map was wrong about" sections, which are the part worth
reading._

_Companion data: `tools/closeout/residue_map.tsv`, one row per machine —
an untrusted analysis snapshot, regenerated with the commands at the
bottom.  While the list was live, the authority for membership and count
was `tools/closeout/frozen_unproven.txt`, which the closeout split into
`core_rows.txt` (the distinct problems) and `shadow_rows.tsv` (their 0RB
re-root shadows, falling automatically with their core rows,
Closeout/ShadowKit.v).  Both lists ended empty.  With tower #20 boarded
on 2026-07-28 the (4,2) HOLDOUT list closed too, so nothing is
outstanding on either front.  (The wave-23 residue track boarded
the whole 15-machine "no visit witness (`StA`)" bucket: quasihalters whose
quiet state is a transition target, closed by the state-AVOIDANCE route --
the kernel recomputes from the SAME lap chains that no window step is ever
in `StA` (`Checkers/LapAvoid.v`), and `Counters/LapGlueQuiet.v` turns that
plus a checked bootstrap window into the R_QH triple with the exact
last-visit bound.  Wave-22 before it boarded 110: the 8-machine "no shift
chain" bucket by chaining the sync-bouncer construction through THREE and
FOUR counts per overflow (`nestcert.MAXCOUNTS`), and 102 of the "no inner
family at pow2 j" bucket by the OFFSET-family route -- an inner count
starting at `2^(j+1)+2` rather than a power of two, the whole overflow
branch reindexed at `j = S j'`, the `j = 0` case one concrete run, plus for
the Mp-outer cluster a SPLIT inner lap (`i = 0` window + peeled `i - 1`
chains) and a shift-by-one landing/refill bridge through `WTape.rep_rot`
(`nestcert.derive_offset`).)_

## What this list was

These were the (4,2) Turing machines in the frozen deferred set that no
engine in this repository had settled yet.  Every other row was
discharged by a kernel-checked board theorem, which is what
`Closeout.closeout_partial` says:

```
forall tm, Deferred D_census tm -> boarded tm \/ Deferred D_remaining tm
```

with `D_remaining` this table — which ended EMPTY, making the second
disjunct uninhabited.

**They were not counterexamples.**  Nothing here was known to quasihalt
late, or to behave badly.  They were *undecided by us*: no certificate
had been found yet.  A machine left this list the moment any proof
settled it — and every one of them eventually did.

**They were not thought to be hard.**  mxdys' assessment of this
population was that it is easy and not worth the attention — which was a
good reason to publish the list, and which turned out to be right: the
whole population fell, along the routes the map below records.

## How to read the map

`residue_map.tsv` has five columns:

| column | meaning |
|---|---|
| `machine` | the TM, in bbchallenge standard format |
| `interior` | measured cost of the INTERIOR lap vs the carry index `j` |
| `overflow` | measured cost of the OVERFLOW lap vs `j` |
| `alphabet` | the counter digit alphabet its tape decodes under, if any |
| `blocker` | the first thing that stopped our emitter |

`interior`/`overflow` come from `tools/counters/ovfshape.py`, which measures
the lap cost at consecutive `j` and classifies by finite differences:
`AFFINE` (in model), `PARITY-AFFINE` (in model after a re-index), `QUAD`,
`EXP2`/`EXP3`/`EXP4` (`c*b^j`), `HIGHER`.

**Everything in these two columns is UNTRUSTED measurement, not a claim.**
`tools/` carries no proof weight anywhere in this project; the shape column
is a map drawn from simulation to help someone choose a target.  While the
list was live, the only kernel-checked fact about these rows was that they
were *absent* from the boarded set; every one of them is now in it.

## The families

Counts below are over the core rows as they stood when each family was
written up — all are now zero (the shape measurements come from the last
full `ovfshape.py` sweep, filtered to the then-live list).  **The
`blocker` column in the TSV predates wave-30.**  The FINAL gate
partition — a fresh `tailcert` scan, one committed row list per gate,
regenerable via `tailcert --out` + `buckets.py` — is
`tools/counters/buckets34/*.txt` with `GATETABLE.md` beside it (the
lists partition `core_rows.txt` exactly):

| n | furthest gate at the end |
|--:|---|
| 0 | *(every gate is empty)* |

**ALL SEVEN gates are EMPTY, and not one of them was ever answered.**
`no inner family at pow2 j` went in #126, `no interior j = 0 chain` in
wave 37, and `no interior j = S j'`, `no gap-free two-form family` and
`no inner interior chain` in wave 39.
`register step does not close` lost its last
row, `1RB1LA_0LA1RC_0RD0RB_1RA---`, in wave 4u along with its shadow — and
that verdict had been stale rather than negative: the row closes today at the
defaults in 60 s, and the sweep that said otherwise differed in its arm set,
not in its mathematics (`docs/LADDER_PLAN.md` §4u).  `no boot chain` lost
`1RB0RD_1LC1RA_0RB0LC_1LD0LA` in #115, which widens into its own padding.

(The two re-root rows wave 4o promoted out of the shadow table —
`0RB0LA_1LA1RC_0RD1RD_1LB0LB` and `0RB0LA_1RC1LA_1RD0RD_1LB0LB` — boarded
the same day and are gone from this list; they never needed a gate, only
the re-root transport.)

**The `no gap-free two-form family` bucket went 10 → 0 across five waves,
and not one of them needed the gate answered.**  Wave 4s took three: the
CHAMPION, which had a compiling board all along and was held out by an
arithmetic comparison in `inventory.py`, and the two gray rows
`1RB0RD_1LC0LB_1LD0LB_1RD0RA` and `1RB0RD_1LC0LC_1LD0LB_1RD0RA`, which closed
the moment the family searcher was made to prefer, among readings tied on
chain length, one whose digit words do not all end in a blank (a `cconf`
carries no trailing blanks, so the other reading's boot check could never
pass).  #114 took four more `0RB` rows, all bouncer counters; #115 took a
doubling nested bouncer; #116 took a two-block bouncer
(`1RB1LB_1LC0RD_0LB1LA_0LA1RA`, hand-boarded off `WTape.cycR`/`cycL`/`cycLW`)
and its shadow.  **Read a gate label as "where the emitter stopped", never as
"how hard the machine is"; that is now eight waves running**
(`docs/LADDER_PLAN.md` §4s).

| interior / overflow | n | what stops us (pre-wave-30 labels) |
|---|---:|---|
| — | 0 | *(the table is empty)* |

**What that table said, and why it never predicted anything.**  Its last
surviving entry was a pair of dashes — the emitter found no anchor on the
final row, so it recorded no shape at all, and the column that was supposed to
be a difficulty map said nothing whatever about the machine that took the
longest.  The
column has now been emptied three times from underneath by rows that went out
through routes it does not model — the `AFFINE`/`HIGHER` pair in wave 37
(re-read as word-rewriting systems), the `EXP3` pair in #123 (base-2 counters
whose whole geometric lap rides inside `LapGlue`'s existential step count),
and the last `AFFINE`/`EXP2` row in #126 — where **both** TSV fields turned
out to be misleading in the hard direction: the `EXP2` was the growth of the
RUN against the tape width and not the shape of a lap (the lap is affine), and
the `alphabet` field failed to decode the row at 250,013 of 250,013 anchor
visits.  **A non-affine shape measurement has never once predicted that a row
was hard, and this column has now also been caught naming an alphabet that
decodes nothing.**  Read the per-row notes below instead.

**The `QUAD` column is gone, and it is the caution worth keeping.**  It held
four rows whose arm really is quadratic — a second difference of exactly 2,
corroborated independently by `QUAD_TERMINAL_MEASUREMENT.md` and re-measured
a third time in §4t — and this file said they were "not coming back without a
new arm shape".  **All four boarded, none with a new arm shape**: #115 took
three as `Counters/LinC_*` and #116 took the last as
`Counters/BinCarry_*` off John's carry reading, with its two shadows.  A
shape measurement bounds the ladder, never the machine.

**The `HIGHER` bucket is CLOSED, and it took four re-readings to get there.**
It was never a verdict — it was a base-2 clock.  Those rows are the FIBONACCI
counters (`docs/CORE_3STATE.md` §3): `ovfshape.py` measured their lap against a
base-2 anchor, and their radix is **φ**.  The sequence is worth keeping because
every step of it was a measurement overturning a label:

1. **"no anchor"** — four waves searched for one.  `radix_clock.py` reads
   `ratio = 1.6180`, spread 0.00 across every digit, and the toggle counts
   satisfy `F(n) = F(n−1) + F(n−2)` exactly.  The anchor was always fine; the
   *radix* was wrong.
2. **"no interior chain"** — 4p measured the ladder ARM costs affine.  The
   blocker was the numeration, and 4r built it (`LadderFam`'s `Fib` code),
   boarding five rows.
3. **"Zeckendorf, weights 1,2,3,5,8"** — 4s inferred that from a fit that had
   dropped a column: the lowest digit is a constant 1, so `fit_weights` cannot
   pin it and abandons the fit.  `1,2,3,5,8,13` is `1,1,2,3,5,8` with the
   bottom rung missing — the numeration the kernel already had.
4. **"what blocks them is `Class`, not `Code`"** — 4v's reading, and the six
   boarded instead as a fourth CODE.  `fibw 0 = fibw 1 = 1`, so a value does
   not determine a string; `fibdec`/`fibokb` pick the greedy member and these
   six stood on the LAZY one.  #118 added `FibL` — the decoder `fiblaz` is
   `fibdec`'s two-state automaton with the transitions swapped — plus `fam_lo`
   (a weighted numeration costs the interface a FLOOR, since width `k` spells
   exactly `[fibw k .. fibsum k]`) and `fam_next` reading `lazfill` directly.
   All six `iqh`, `functional_extensionality_dep` only.

**One row carried the `HIGHER` label without being one of them**:
`1RB0RB_0LC1RD_1LC1LA_0LA1RB` found no family at any anchor, so it
belonged with `no anchor` (it boarded in wave 39, below).

So the count of rows whose cost the certificate language genuinely could
not write was **3** — the `EXP3` rows.  Not the φ rows (their arithmetic
is denotable and was denoted), and not the four `QUAD` rows, every one of
which boarded off the ladder entirely.

What was left wanted either a closer that never needs the cost
(`LapGlue`'s lap obligation is an EXISTENTIAL over step counts, which is
how the wave-19 fractals boarded with a `3^k` lap) or a route that never
models the lap at all, like ReachSt — and that is exactly how it went
out.

### What each blocker means

* **no anchor** / **no overflow phase** — the tape never decodes as a counter
  under any of the 21 alphabets in the zoo, so there was no anchor family to
  build a lap around.  These needed `tools/counters/alphabet_infer.py` to read
  a new `(A,B,C)` triple off the tape first; `gen_alphabet.py` then generated
  a PROVED Coq module for it (a wrong triple fails to compile).
* **no interior chain** — the ordinary lap is not expressible as one affine
  `srun`.  For `EXP3` that is a statement about the machine, not the search:
  the certificate language carries `a*j + b`.  **It was said of `QUAD` too,
  and all four `QUAD` rows have since boarded** — off the ladder entirely.
  **And for `HIGHER` it was never true**: those rows are the φ counters, the
  label came from measuring a Fibonacci lap on a base-2 clock, and 4v measured
  that the kernel denotes their arithmetic exactly — only their string FORM is
  out of reach (above; `docs/CORE_3STATE.md` §3, `docs/LADDER_PLAN.md` §4v).
* **no inner family at pow2 j** — the overflow runs a second counter, but its
  count does not start at `2^j`.  Measured in wave-15: ~21% of these run at a
  different octave or offset.
* **no boot / exit / second exit chain** — the nested overflow's pieces.
  Wave-22 boarded the 8 "no shift chain" machines (multi-count chaining) and
  measured the then-surviving "no second exit chain" machines (2 at the
  time) precisely: their exit's return sweep enters its rightward cycle
  mid-unit against a non-matching post, which no rotation lstep can align —
  the judgment was that they needed a new `SCycR`-with-entry-offset step in
  `LapDecider.v` (a checker extension with its own soundness proof), or
  hand-written boards; in the event both boarded.
* **no visit witness (`StA` is targeted)** — RETIRED (wave-23 boarded all
  15).  `docs/WAVE16_FINDINGS.md` §6b was the analysis: quasihalters whose
  quiet state is `StA` (last visit at step 4-11).  The closer is the
  state-AVOIDANCE route: `srun_avoid` re-runs the SAME chains checking no
  window step is in `StA` (`Checkers/LapAvoid.v`), and
  `LapGlueQuiet.glue_qh_quiet` closes the R_QH triple with the exact bound.

## The community cross-check — and how it played out

nickdrozd read the published version of this map and posted lists of
machines he was "pretty sure are all solvable"; John's live hand-reads and
the mxdys Inductive target list ran alongside.  Every one of those calls
paid out: nick's lists sized the `no interior chain` bucket and then
seeded every ReachSt wave (`docs/REACHST_TIER.md` — liveness of a
machine's sparse state as TERMINATION of the state-deleted sub-machine,
110+ boards across five flavours plus the parity-witness fix
`LapCertGluePar` and the invariant-relativised `ReachStI`); John's
one-line reads exposed the bit-polarity inversion that emptied the old
70-row interior gate (`WAVE30_FINDINGS.md` §6b); and the Inductive
prover's layer read cracked the CHAMPION — the machine blanks its whole
10,239-cell region and returns to a blank tape in `StC` at step
32,779,478, so its board is one ~17 s binary-fuel `vm_compute`
(`Machines/Counters/Champion_1RB1LD_1RC1RB_1LC1LA_0RC0RD.v`).  **That row
is now OFF this list** (2026-08-01, wave 4s).  It sat here for one reason
and the reason was never mathematics: `boarded` demanded `QHBound B_board`
with `B_board` = 66,349, the PREVIOUS champion's score
(`Closeout/CloseoutKit.v`), 32,779,478 ≰ 66,349, so `inventory.py` refused
the board by the same comparison and no number of closeout regens moved it.
The fix is the second of the two `CloseoutKit` changes this paragraph used
to name — **a third disjunct** for exact-score quasihalters above
`B_board`, carried through `covers_iqh_champ_at` and the swap/mirror
lemmas — and not raising `B_board`, so
`bbb4_decided_le_prev_champion_or_champion` still separates the champion
from the other 5,135 boarded rows instead of coarsening all of them.  Its
gate is the PROPOSITION `B <= B_champ` under `lia`, never a `<=?`:
evaluating a boolean against 32,779,478 would make the kernel build a
32.8M-constructor unary numeral.  At the time it bought the LOWER bound
— BBB(4) ≥ 32,779,478 — and nothing more; the 29 rows that then remained
were what stood between it and the value, and all 29 boarded:
`BBB4_value` is a theorem.  See `docs/CLAIMS.md`.

Measured dead along the way (all do-not-retry): the `cycR-gap` primitive,
the double peel, the SOLO-cascade route on the boot bucket, every FRAMING
of the nested-lap bucket, the flat `emit_lapcert` route, the ladder's
far-side template and its glue (§4k: measured before building it),
uniform step bounds for avoid sub-machines without sweep acceleration, a
flat arm stated with `stride = 0` (no chain at ANY depth, because `srot 0`
is the identity — it reads like "not affine" and is not), **every base-2
anchor search on the φ rows** (four waves' worth, and now explained), the
Zeckendorf weight hunt (840 exhaustive fits, zero at `1,1,2,3,5,8` — the
question was wrong, not the answer), and the ladder ARM_GRID on the four
`QUAD` rows (a second difference of exactly 2 on the arm itself, measured
three times — though all four rows boarded anyway, off the ladder).

## Where a newcomer should probably start

There is nothing left to start on.  What follows is the record of how the
5,156 went out, kept because the shape of the mistakes is the transferable
part: **on this list, a label that said a row was hard was wrong every single
time it was checked.**

**BOARDED, #123 — and this page had just called the shape unreachable.**
The two `1RB1LC` siblings (`1RB1LC_1LB1RA_0LC0LD_0RA0RD` and
`1RB1LC_1LC1RA_0LC0LD_0RA0RD`, one transition apart at `B0`) went out
together with their two shadows, both `NeverQuasiHaltsSt`, both
`functional_extensionality_dep` only.  `theories/Counters/Bin3Lap.v` plus
`Machines/Counters/B2L_*.v`.

**The claim this section made was: "a base-2 counter whose lap is
`α*3^c + βc + γ` — a shape no closer in the tree has: `LapGlue` glues AFFINE
laps."**  It was wrong twice over.  No new closer was needed at all: the
board uses the **plain** `LapGlue.glue_neverqh`, at the anchor
`Cf p = (StD, ([], S0, Wp p))` with `MonoCounter.Wp` verbatim, `Cf` fitting
with no offset because all four states occur in every lap.  And the reason
the lap shape never mattered is written on this very page, three sections
down: **`LapGlue`'s lap obligation is an existential over step counts, so a
cost never has to be written down.**  The gap between `3.5*3^c + c + 2.5`
and `3^(c+1) + 2c + 1` rides inside that existential and is never named in
the proof.  This document contained the refutation of its own claim and
still made it.

*(The mathematics that was actually open was the cascade — `Bin3Lap`'s
`Hloop`, that `LOOP (S k) = D1 ; field run ; MARK ; CASC` closes by one
induction on the turn count with the level climbing as the set cells run
out.  The one-transition difference between the rows is absorbed by `Hbc`:
`bc_selfB` for `1LB`, `bc_toC` for `1LC`.)*

**Measured, with a named blocker.**  _This table is now EMPTY: all three
rows boarded on 2026-08-01 and `tools/closeout/core_rows.txt` has no rows
left._

**BOARDED, wave 39 (2026-08-01)** — two of the three rows of this table,
plus the last shadow, in one session (`NEXT_SESSION.md` §2b7); the third
followed the same day (§2b8, below):

* `1RB0RB_0LC1RD_1LC1LA_0LA1RB` ⬩+1 (was `no interior j = S j'`, the twelfth
  φ row) — as `NeverQuasiHaltsSt` through its wave-38 macro system and the
  `ones l + sval s` parity invariant, `Machines/Rest4/R2_*.v`; exactly the
  transcription job `WAVE38_REST_FOUR.md` §3 said it had become.  Its 0RB
  shadow `0RB1LC_1LC0LC_0RD1LA_1RD1RB` harvested in the same regen
  (`Machines/Counters/SH_0RB1LC_1LC0LC_0RD1LA_1RD1RB.v`), so shadows are 0.
* `1RB0RB_1LC0RC_1RA0LD_0LB0LC` (was `no gap-free two-form family`, "the
  LEAST tractable of the four") — as `NeverQuasiHaltsSt` by a HAND lap
  system: nine boundary words cycling at the left-turnaround anchor, laps
  `96j + b_phi`, `StD` carried by the `cycL` zeroing sweep;
  `Machines/Rest4/R3_*.v`.  The wave-38 `ReachStI` negative on `StD` stands
  — the row went out AROUND the tier, not through it, one wave after §5's
  caution about exactly this pattern.

**BOARDED, wave 39** — `1RB0RD_1LB1LC_1RC0RA_0LB1RD` (Drozd's sixth; was
`no inner interior chain`, gap ratio 1.00), BY HAND, and the transferable
part is that **the label was about `digit_words` and not about the tape**.
The `no-anchor` column is a statement that the counter emitter found no
family; the row has an exact anchor cell for cell, with a literally empty
right list, and a DENSE one:

* the family the row is named after — the reset family
  `R k = (StC, ([], S0, rep [S1] k))` — is real (both closed forms exact on
  all 13 measured half-laps) and is the WRONG anchor, because both half-laps
  are exponential in `i`.  No affine lap-decider arm reaches it, so
  `emit_lapcert.py`'s refusal here was correct.
* `Counters/LapGlueNeverIx.glue_neverqh_ix` takes an arbitrary index type, so
  the anchor need not be that family.  `tools/counters/drz6land.py` prints
  max-gap per `(state, symbol)` in one command: `D0` recurs at most every
  **56** steps over 300,000 — polynomial (`2z+4`) where the other seven
  classes are exponential — with a literally empty right list at all 37,516
  visits.  Read in those coordinates the whole row is three single-cell rules
  (37,432 / 76 / 7 firings, zero mismatches over 37,515 transitions) and the
  descending cascade is three lines, because a decrement IS the interior
  rule.  The laps stay exponential (36, 198, 864, … steps); what changes is
  that they are an induction over three closed rules instead of new
  mathematics per gap.
* there is **no invariant on the left word anywhere in the board** — the
  macro rule genuinely can die (1,605 of 4,095 canonical words up to length 12
  do), and the survivors are an arithmetic set rather than a local language,
  so the board is built out of SHAPES that each carry their own `S1` instead.

Board: `theories/Machines/Counters/DRZ6_1RB0RD_1LB1LC_1RC0RA_0LB1RD.v`;
method in `docs/LADDER_PLAN.md` §4ab.  No `0RB` shadow.

**BOARDED, wave 38** — `1RB1RC_1LA1RA_0RC1LD_1LB0LD` (was
`no inner family at pow2 j`, gap ratio 1.04), through the ordinary
`LapDecider` certificate route after all.  **Both of its TSV fields were
misleading and both in the hard direction**, which is the transferable part:

* `EXP2` interior/`no inner family at pow2 j` reads as the nested cascade
  (`Bin3Lap.v`'s shape).  It is not — the lap is AFFINE in the carry length
  (`6j+6` / `6j+4` / `6(S j)+2`, zero mismatches over 250,012 laps), because
  the counter's LSB sits against the wall so an increment is local.  `EXP2`
  is the growth of the RUN against the tape width, not the shape of a lap.
* the `Alph_000_111_111` field does not decode the row at all: `Ap`
  mismatches at 250,013 of 250,013 anchor visits.  The real numeral packs
  its top TWO digits into four cells instead of six, and the packing is
  forced by the extent law rather than being a decoder artefact, so no
  re-anchoring reads it away.  New numeral: `theories/Counters/Kc3Num.v`.

The gate label was accurate about what the emitter could find and useless
about what the row is; `tools/counters/kc3lap.py`'s lap-per-`cview`-class
table is the one-command test that separates the two.  Board:
`theories/Machines/Counters/KC3_1RB1RC_1LA1RA_0RC1LD_1LB0LD.v`; method in
`docs/LADDER_PLAN.md` §4aa.  No `0RB` shadow.

**BOARDED, wave 37** — `1RB1LC_0LC0RB_1LA1RD_0LA0RD` (was
`no inner interior chain`, gap ratio 8,192.81) and
`1RB1LD_1LC1RA_0RB0LC_0RA0LD` (was `no interior j = 0`, gap ratio 6,343),
each with its `0RB` shadow.  Neither went out through the counter emitter,
and neither could: their gate labels and their gap ratios were both correct
and both permanent.  What boarded them is that the ROW is a finite
word-rewriting system once one half-tape is read as a unary run — the
`NGramHist` closure at `k=3, n=2` for three states, and a hand measure
argument on the macro rules for `StD`.  `theories/Machines/Mxdys4/NGX_*.v`;
method in `docs/WAVE36_MXDYS_FOUR.md` §§2a, 2b, 4, 8.

**A second, orthogonal reading, and it is the one that survived.**  Wave 36's
`tools/mxdys4/gaps.py` is a cheap a-priori triage for the REACHST tier: run
3M steps and compare each state's worst recurrence gap to the final tape
width.  Over the core list as it stood at eight rows **it split with no
middle** — six between 1.00 and 2.65, two four orders of magnitude out — and
the two walls are exactly the two rows wave 37 then boarded by hand.  So
**every row then left on this table was inside the tier's reach** (1.00, 1.11
and 2.65) and `docs/REACHST_TIER.md`'s route was excluded on none of them.
That is a different axis from the gate labels above, which are about the
*counter* emitter; of the two, this is the one that never turned out wrong.

**But "not excluded" is not "this is the route."**  Wave 38's row sat at ratio
1.04 and boarded OFF the tier anyway (#126).  The triage is a cheap way to
rule the tier OUT, and it has never been wrong doing that; it has never yet
been the thing that ruled a route IN.  Full table and method:
`docs/WAVE36_MXDYS_FOUR.md` §3a.

**The φ row was the cheapest lead on the list, and this table used to hide
it.**  `1RB0RB_0LC1RD_1LC1LA_0LA1RB` is filed above as "no family at any
anchor", which was true of the EMITTER and was never a verdict about the
machine.  `tools/counters/RADIX_CORE.txt` reads it as `phi` at spread 0.00,
with anchor values stepping by successive Fibonacci numbers — the same
family as the eleven three-state rows that boarded on 2026-08-01 off
`(Fib, 1)` and `(FibL, 1)` (`docs/CORE_3STATE.md` §3).  It was the twelfth
of twelve and the last one out (wave 39); the numeration was already built
— `LadderFam` has `Fib`, `FibL`, `fam_lo` and the round trips.

**SETTLED, wave 38: the φ reading is exactly right, and `LADDER_PLAN.md`
§4s's "no family at any anchor, file it with the no-anchor bucket" is a
statement about the emitter and not about the machine.**  The measurement
is not a ratio fit: running the row's validated macro system and recording
the first macro step at which the counter reaches `n` digits gives
17,709 = F(22)−2, 28,656 = F(23)−1, 46,366 = F(24)−2, … , 2,178,307 =
F(32)−2 — **exactly Fibonacci, alternating offset −2/−1, out to F(32)**.
The tape is 28 cells wide after 3,000,000 steps, growing like `log_φ t`,
which is where the 1.11 gap ratio comes from.

Wave 38 also found the route that does NOT need the anchor at all: this row
passes wave 36's lever (its orbit keeps the RIGHT half-tape a bare unary
run, 0 violations in 2,000,000 steps), so it is a finite word-rewriting
system — six rules, exhaustive, differentially validated in
`tools/mxdys4/cmacro2.py`.  Its four liveness obligations all reduce to the
SINGLE fact that the macro system never gets stuck, and **that fact was
proved**: the composite step preserves the parity of `ones l`, is undefined
only at `ones l = 0` (even), and the orbit starts odd -- so it is never
stuck.  The remaining cost was not a search for an anchor and not new
mathematics; it was the Coq transcription, which wave 39 supplied.
`docs/WAVE38_REST_FOUR.md` §3.

**The shadows never became a task, and that was the design working.**  The
shadow table is empty and the last entry, `0RB1LC_1LC0LC_0RD1LA_1RD1RB`, fell
with the φ row it rode on.  `Census/ShadowBoard.shadow_nqh` is the whole
argument in one lemma and `make closeout` runs `gen_shadow.py --harvest`, so
from wave 4u onward every freed shadow boarded in the same regen as its
partner — wave 37's two, #123's two, wave 39's one — without anyone touching
it.  The population that once stood at 96 rows closed without ever being
worked on directly.

**The stale-verdict query earned its keep once.**  "Which core rows carry a
`closed: true` certificate in a committed sweep and are still unproven?" is
how wave 4u's row was found — it had been carrying "families found, none
closed" and closed at the defaults in 60 s, the old sweep differing in its
*arm set* and not its mathematics.  A lesson for the next census: a
negative sweep verdict is only as fresh as the sweep's configuration.

## Reproducing the map

```bash
python3 tools/counters/ovfshape.py --list tools/closeout/frozen_unproven.txt --json ovf.json
python3 tools/counters/emit_lapcert.py --list tools/closeout/frozen_unproven.txt --json emit.json
```

Both are untrusted and neither needs Coq.  The first is ~20 min over the whole
list (shard it), the second similar.  `--emit` on the second writes and
`coqc`-checks a board for every machine it can derive, which is how this list
first shrank from 883 to 511 (and, wave by wave, to zero).
