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

_**13 rows as of this commit — 8 distinct core machines + 5 0RB
re-root shadows.**  A shadow needs no new mathematics, but it does need its
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

| n | furthest gate today | | n | furthest gate today |
|--:|---|---|--:|---|
| 3 | no interior `j = S j'` chain | | 1 | no interior `j = 0` chain |
| 2 | no inner interior chain | | 1 | no inner family at `pow2 j` |
| 1 | no gap-free two-form family | | | |

**Two gates are now EMPTY.**  `register step does not close` lost its last
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
| `-`/`no-anchor` | 2 | 2 no overflow phase at K=6 |
| `AFFINE`/`HIGHER` | 2 | 2 no inner interior chain |
| `EXP3`/`EXP3` | 2 | 2 base-2 counters with a `3^c` lap (wave 4y) |
| `HIGHER`/`HIGHER` | 1 | 1 no family at any anchor |
| `AFFINE`/`EXP2` | 1 | 1 no inner family |

**What that table now says:** three of the eight measure NON-AFFINE on both
branches (`EXP3` 2, `HIGHER` 1), two never decode as a counter under any
alphabet, and three are affine on at least one branch.  At eight rows the
shape column is worth less than the per-row notes below — read them
individually.  And `EXP3` is a lap shape, not a radix: wave 4y measured its
two remaining rows as **base 2** counters whose lap grows like `3^c`, where
the `Ter3Wall*` rows carrying the same label really are base 3.  When the
question is the radix, read the ALPHABET column.

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

At eight rows the useful unit is the row, not the bucket.  All eight, with
what is known about each:

**The two `1RB1LC` siblings — measured, and the measurement is the lead.**
They differ from each other in **exactly one transition** (`B0`: `1LB` vs
`1LC`), and #120's `tools/counters/ter3_scan.py` swept every blank-side
anchor, every 0/1/2-cell prefix and every 2-cell radix on both:

| row | shadow | anchor | reading | lap |
|---|---|---|---|---|
| `1RB1LC_1LB1RA_0LC0LD_0RA0RD` | ⬩+1 | `(StA, ([], S0, <digits>))` | base 2, `{00, 10}` | `3.5*3^c + c + 2.5` |
| `1RB1LC_1LC1RA_0LC0LD_0RA0RD` | ⬩+1 | `(StA, ([], S0, <digits>))` | base 2, `{00, 10}` | `3*3^c + 2c + 1` |

Both exact and consecutive from 0 with zero decode failures, each corroborated
at two further anchors (`C1`, `D0`).  **No base-3 reading exists at any anchor
or prefix on either** — this map used to call them base-3 by inference from
their `EXP3` label and their one-transition distance from
`1RB1RC_1LA0LB_1LD0RD_1LB0RC` (now boarded, wave 4y, and genuinely base 3).
The inference was wrong on both counts, and the shape table above says why:
`EXP3` names a LAP that grows like `3^j`, not a radix.

So what these two need is not `Ter3Wall*` but a base-2 counter whose lap is
`α*3^c + βc + γ` — a shape no closer in the tree has: `LapGlue` glues AFFINE
laps and `LadderCheck`'s families are all affine-lapped too.  Whether the
half-integer coefficient on the first row survives a change of anchor is
unmeasured and is the cheapest next question (it takes minutes and no Coq).

**Measured, with a named blocker.**

| row | gate | note |
|---|---|---|
| `1RB0RB_0LC1RD_1LC1LA_0LA1RB` ⬩+1 | `no interior j = S j'` | wears a `HIGHER` label and the emitter finds **no family at any anchor** — `digit_words` names nothing.  But see below: it is the TWELFTH φ row, and the other eleven have all boarded. |
| `1RB0RD_1LB1LC_1RC0RA_0LB1RD` | `no inner interior chain` | gap ratio **1.00** — the tightest on the whole list |
| `1RB1LC_0LC0RB_1LA1RD_0LA0RD` ⬩+1 | `no inner interior chain` | gap ratio **8,192.81** — REACHST is a wall here.  But wave 36 §4 has a pen-and-paper argument that `StD` is live on it, so the remaining work may be transcription |
| `1RB1LD_1LC1RA_0RB0LC_0RA0LD` ⬩+1 | `no interior j = 0` | gap ratio **6,343** — the other REACHST wall |
| `1RB0RB_1LC0RC_1RA0LD_0LB0LC` | `no gap-free two-form family` | the last row of a bucket that went 10 → 1 without the gate ever being answered.  Gap ratio 2.65 on a 2,255-cell tape — the widest tape here, and still inside the tier |
| `1RB1RC_1LA1RA_0RC1LD_1LB0LD` | `no inner family at pow2 j` | NOT a time-cap row: finishes in 723 s on `interior-not-covered` with 5 of 12 families tried.  Gap ratio 1.04 |

**A second, orthogonal reading of the same eight.**  Wave 36's
`tools/mxdys4/gaps.py` is a cheap a-priori triage for the REACHST tier: run
3M steps and compare each state's worst recurrence gap to the final tape
width.  Over the core list **it splits with no middle** — six of the eight
sit between 1.00 and 2.65, and two are four orders of magnitude out.  That is
a different axis from the gate labels above (which are about the *counter*
emitter), and on six rows it says `docs/REACHST_TIER.md`'s route is not
excluded and every "missing q" the sweeps report is a search gap worth
attacking.  On the two it is a wall, and the counter has to be read instead.
Full table and method: `docs/WAVE36_MXDYS_FOUR.md` §3a.

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

**The five shadows are not a task.**  They sit on five of the eight, they need
no new mathematics, and they fall automatically: `Census/ShadowBoard.shadow_nqh`
is the whole argument in one lemma and `make closeout` runs
`gen_shadow.py --harvest`.  Board a core row and its shadow comes with it —
first demonstrated in wave 4u, and every quadratic row's shadow came that way.

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
first shrank from 883 to 511 (and, wave by wave, to the current 13).
