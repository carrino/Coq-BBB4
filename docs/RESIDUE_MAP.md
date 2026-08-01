# The residue, characterised

_The frontier of this project, published as a target list rather than as an
apology.  Companion data: `tools/closeout/residue_map.tsv`, one row per
machine, regenerated with the commands at the bottom.  The TSV is an
ANALYSIS SNAPSHOT (a ~40 min sweep) and can lag a wave or two behind the
list itself; the authority for membership and count is
`tools/closeout/frozen_unproven.txt`, which every closeout regen rewrites.
The closeout further splits that list: `core_rows.txt` is the distinct
problems, `shadow_rows.tsv` their 0RB re-root shadows, which fall
automatically with their core rows (Closeout/ShadowKit.v)._

_**4 rows as of this commit — 3 distinct core machines + 1 0RB
re-root shadow.**  A shadow needs no new mathematics, but it does need its
own board: boarding a core machine moves its shadow into `core_rows.txt`
rather than settling it, so budget the pair (2026-08-01; worked example
`Machines/Counters/RRNQ_0RB0RD_1RC____1RD1LC_0LC1RA.v`).  The count moves every wave, so
treat the row files as the authority and this prose as a snapshot.  With
tower #20 boarded on 2026-07-28 the (4,2) HOLDOUT list is closed, so this
is the entire remaining problem.  (The wave-23 residue track boarded
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

## What this list is

These are the (4,2) Turing machines in the frozen deferred set that **no
engine in this repository settles**.  Every other row is discharged by a
kernel-checked board theorem, which is what `Closeout.closeout_partial`
says:

```
forall tm, Deferred D_census tm -> boarded tm \/ Deferred D_remaining tm
```

with `D_remaining` this table, and `vm_compute` on
`List.length remaining_rows` confirms its length inside the kernel.

**They are not counterexamples.**  Nothing here is known to quasihalt late,
or to behave badly.  They are *undecided by us*: no certificate has been
found yet.  A machine leaves this list the moment any proof settles it.

**They are not thought to be hard.**  mxdys' assessment of this population
was that it is easy and not worth the attention — which is a good reason to
publish the list.  If that is right, most of it should fall quickly to
someone who looks; if it is wrong, the map below says where the difficulty
actually is.  Either outcome is worth more than the list sitting in a build
directory.

## How to read the map

`residue_map.tsv` has five columns:

| column | meaning |
|---|---|
| `machine` | the TM, in bbchallenge standard format |
| `interior` | measured cost of the INTERIOR lap vs the carry index `j` |
| `overflow` | measured cost of the OVERFLOW lap vs `j` |
| `alphabet` | the counter digit alphabet its tape decodes under, if any |
| `blocker` | the first thing that stops our emitter |

`interior`/`overflow` come from `tools/counters/ovfshape.py`, which measures
the lap cost at consecutive `j` and classifies by finite differences:
`AFFINE` (in model), `PARITY-AFFINE` (in model after a re-index), `QUAD`,
`EXP2`/`EXP3`/`EXP4` (`c*b^j`), `HIGHER`.

**Everything in these two columns is UNTRUSTED measurement, not a claim.**
`tools/` carries no proof weight anywhere in this project; the shape column
is a map drawn from simulation to help someone choose a target.  The only
kernel-checked fact about these rows is that they are *absent* from the
boarded set.

## The families

Counts below are over the core rows as of this commit (the shape
measurements come from the last full `ovfshape.py` sweep, filtered to the
live list).  **The `blocker` column in the TSV predates wave-30.**  The
CURRENT gate partition — a fresh `tailcert` scan, one committed row list
per gate, REGENERABLE via `tailcert --out` + `buckets.py` — is
`tools/counters/buckets34/*.txt` with `GATETABLE.md` beside it (the
lists partition `core_rows.txt` exactly):

| n | furthest gate today |
|--:|---|
| 1 | no interior `j = S j'` chain |
| 1 | no inner interior chain |
| 1 | no gap-free two-form family |

**One row per gate, and four gates are now EMPTY.**  `no inner family at
pow2 j` joined them in #126 and `no interior j = 0 chain` in wave 37.
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

**The `no gap-free two-form family` bucket has gone 10 → 1 in four waves,
and not one of the nine needed the gate answered.**  Wave 4s took three: the
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
| `-`/`no-anchor` | 2 | 1 no anchor, 1 no overflow phase at K=6 |
| `HIGHER`/`HIGHER` | 1 | 1 no family at any anchor |

**What that table now says, and why you should stop reading it.**  At three
rows: two never decode as a counter under any alphabet and one is `HIGHER` on
both branches.  Every row that ever carried a *decodable* shape is gone.  The
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

**One row still carries the `HIGHER` label and is not one of them**:
`1RB0RB_0LC1RD_1LC1LA_0LA1RB` finds no family at any anchor, so it belongs
with `no anchor`.

So the count of rows whose cost the certificate language genuinely cannot
write is **3** — the `EXP3` rows.  Not the φ rows (their arithmetic is
denotable and now denoted), and not the four `QUAD` rows, every one of which
boarded off the ladder entirely.

What is left wants either a closer that never needs the cost (`LapGlue`'s lap
obligation is an EXISTENTIAL over step counts, which is how the wave-19
fractals boarded with a `3^k` lap) or a route that never models the lap at
all, like ReachSt.

### What each blocker means

* **no anchor** / **no overflow phase** — the tape never decodes as a counter
  under any of the 21 alphabets in the zoo, so there is no anchor family to
  build a lap around.  These need `tools/counters/alphabet_infer.py` to read a
  new `(A,B,C)` triple off the tape first; `gen_alphabet.py` then generates a
  PROVED Coq module for it (a wrong triple fails to compile).
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
  measured the then-surviving "no second exit chain" machines (2 remain)
  precisely: their
  exit's return sweep enters its rightward cycle mid-unit against a
  non-matching post, which no rotation lstep can align — they need a new
  `SCycR`-with-entry-offset step in `LapDecider.v` (a checker extension with
  its own soundness proof), or hand-written boards.
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
32.8M-constructor unary numeral.  It buys the LOWER bound — BBB(4) ≥
32,779,478 is a theorem here now — and nothing more; the 29 that remain
are what stands between this and the value.  See `docs/CLAIMS.md`
"What this is NOT".

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

At three rows the useful unit is the row, not the bucket.  All three, with
what is known about each:

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

**Measured, with a named blocker.**

| row | gate | note |
|---|---|---|
| `1RB0RB_0LC1RD_1LC1LA_0LA1RB` ⬩+1 | `no interior j = S j'` | wears a `HIGHER` label and the emitter finds **no family at any anchor** — `digit_words` names nothing.  But see below: it is the TWELFTH φ row, and the other eleven have all boarded. |
| `1RB0RD_1LB1LC_1RC0RA_0LB1RD` | `no inner interior chain` | gap ratio **1.00** — the tightest on the whole list |
| `1RB0RB_1LC0RC_1RA0LD_0LB0LC` | `no gap-free two-form family` | the last row of a bucket that went 10 → 1 without the gate ever being answered.  Gap ratio 2.65 on a 2,255-cell tape — the widest tape here, and still inside the tier |

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
**every row left on this table is inside the tier's reach** (1.00, 1.11 and
2.65) and `docs/REACHST_TIER.md`'s route is excluded on none of them.  That is
a different axis from the gate labels above, which are about the *counter*
emitter; of the two, this is the one that has not yet been wrong.

**But "not excluded" is not "this is the route."**  Wave 38's row sat at ratio
1.04 and boarded OFF the tier anyway (#126).  The triage is a cheap way to
rule the tier OUT, and it has never been wrong doing that; it has never yet
been the thing that ruled a route IN.  Full table and method:
`docs/WAVE36_MXDYS_FOUR.md` §3a.

**The φ row is the cheapest lead on the list, and this table used to hide
it.**  `1RB0RB_0LC1RD_1LC1LA_0LA1RB` is filed above as "no family at any
anchor", which is true of the EMITTER and is not a verdict about the machine.
`tools/counters/RADIX_CORE.txt` reads it as `phi` at spread 0.00, with anchor
values stepping by successive Fibonacci numbers — the same family as the
eleven three-state rows that boarded on 2026-08-01 off `(Fib, 1)` and
`(FibL, 1)` (`docs/CORE_3STATE.md` §3).  It is the twelfth of twelve and the
only one left.  **The numeration is already built** — `LadderFam` has `Fib`,
`FibL`, `fam_lo` and the round trips — so the entire remaining cost of this
row is LOCATING ITS ONCE-PER-INCREMENT ANCHOR, which `digit_words` never
enumerates because the row is read at a sparse one.  Every other row on this
page needs mathematics that does not exist yet; this one needs a search.

**The one shadow is not a task.**  `0RB1LC_1LC0LC_0RD1LA_1RD1RB` rides on the
φ row and no other core row carries one.  It needs no new mathematics and it
falls automatically: `Census/ShadowBoard.shadow_nqh` is the whole argument in
one lemma and `make closeout` runs `gen_shadow.py --harvest`.  Board the φ row
and the shadow comes with it — first demonstrated in wave 4u, and every shadow
since (wave 37's two, #123's two) came that way without anyone touching it.

**And re-run the stale-verdict query.**  Which core rows carry a `closed: true`
certificate in a committed sweep and are still unproven?  That is how wave 4u's
row was found — it had been carrying "families found, none closed" and closed
at the defaults in 60 s, the old sweep differing in its *arm set* and not its
mathematics.  Nobody has re-run it since the emitter changed.

## Reproducing the map

```bash
python3 tools/counters/ovfshape.py --list tools/closeout/frozen_unproven.txt --json ovf.json
python3 tools/counters/emit_lapcert.py --list tools/closeout/frozen_unproven.txt --json emit.json
```

Both are untrusted and neither needs Coq.  The first is ~20 min over the whole
list (shard it), the second similar.  `--emit` on the second writes and
`coqc`-checks a board for every machine it can derive, which is how this list
first shrank from 883 to 511 (and, wave by wave, to the current 4).
