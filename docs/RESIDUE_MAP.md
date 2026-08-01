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

_**14 rows as of this commit — 9 distinct core machines + 5 0RB
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
| 10 | no interior `j = S j'` chain | | 1 | no interior `j = 0` chain |
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
"how hard the machine is"; that is now seven waves running**
(`docs/LADDER_PLAN.md` §4s).

| interior / overflow | n | what stops us (pre-wave-30 labels) |
|---|---:|---|
| `HIGHER`/`HIGHER` | 7 | 6 the word-valued run unit (wave 4v), 1 no family at any anchor |
| `EXP3`/`EXP3` | 3 | 3 no interior chain |
| `-`/`no-anchor` | 2 | 2 no overflow phase at K=6 |
| `AFFINE`/`HIGHER` | 2 | 2 no inner interior chain |
| `AFFINE`/`EXP2` | 1 | 1 no inner family |

**What that table now says, and it is the shape of the endgame:** the
residue has inverted.  It used to be dominated by `AFFINE` machines our
emitter could not frame; **10 of the 15 measure NON-AFFINE on both
branches** (`HIGHER` 7, `EXP3` 3) — shapes whose lap cost the certificate
language cannot write as `a*j + b` — plus 2 whose tape never decodes as a
counter under any alphabet.  Only 3 rows are affine on at least one branch.

**The `QUAD` column is gone, and it is the caution worth keeping.**  It held
four rows whose arm really is quadratic — a second difference of exactly 2,
corroborated independently by `QUAD_TERMINAL_MEASUREMENT.md` and re-measured
a third time in §4t — and this file said they were "not coming back without a
new arm shape".  **All four boarded, none with a new arm shape**: #115 took
three as `Counters/LinC_*` and #116 took the last as
`Counters/BinCarry_*` off John's carry reading, with its two shadows.  A
shape measurement bounds the ladder, never the machine.

**`HIGHER` was never a verdict — it was a base-2 clock, and this bucket has
been re-read three times.**  The `HIGHER`/`HIGHER` rows are the FIBONACCI
counters (`docs/CORE_3STATE.md` §3): `ovfshape.py` measured their lap against
a base-2 anchor, and their radix is **φ**.  `tools/counters/radix_clock.py`
reads `ratio = 1.6180`, spread 0.00 across every digit; the raw per-cell toggle
counts satisfy `F(n) = F(n−1) + F(n−2)` exactly, and re-running the anchor scan
with the ladder `1,1,2,3,5,8,…` decodes them to `0,1,2,3,4,…` with nothing
skipped.  Wave 4p measured the ladder ARM costs affine; **wave 4r built the
numeration** (`LadderFam`'s `Fib` code, `LadderCheck` 3c/5c/11) and the five
rows that had partial ladder boards now carry `iqh_*` theorems.

**Where it stands now (wave 4v, measured):** SIX rows remain, they are one
sub-machine — identical value-to-string tables at their own anchors, so one
instance boards all six — and **the numeration needs nothing built**.  They
count in the kernel's own `fibw = 1,1,2,3,5,8`, with `fam_lim`, the width
spans and the top of a width all matching `LadderFam` exactly.  4s's reading
of the weights as `1,2,3,5,8` (Zeckendorf) came from a fit that had dropped a
column — the lowest digit is a constant 1, so `fit_weights` cannot pin it and
abandons the fit.  What actually differs is the **representative**: `fibw 0 =
fibw 1 = 1`, so a value does not determine a string, `fibdec`/`fibokb` pick
the greedy member, and these six stand on the lazy one (LSB-first, top digit
1, no two ZEROS adjacent) on all 23,614 measured values — 4r's five boarded
rows being the exact complement.  **What blocks them is `Class`, not `Code`**:
the increment sends `1^(2m) 0 rest -> (1 0)^m 1 rest` and `cs_t : nat` is a run
of one repeated digit, so the widening is `cs_t`/`cs_t'`/`f_mid` to
`list nat`.  A seventh row once counted here — `1RB0RB_0LC1RD_1LC1LA_0LA1RB`
finds no family at any anchor and belongs in the `no anchor` block.
`docs/LADDER_PLAN.md` §4v.

So the honest count of rows whose cost the certificate language genuinely
cannot write is **3** — the `EXP3` rows — and not the 14 that measure
non-affine.  The six φ rows are not among them (their arm costs are affine and
their arithmetic is denotable; only the string form is out of reach), and
neither were the four `QUAD` rows, every one of which has now boarded.

The easy framings are spent.  What is left wants either a closer that never
needs the cost (`LapGlue`'s lap obligation is an EXISTENTIAL over step counts,
which is how the wave-19 fractals boarded with a `3^k` lap), a route that never
models the lap at all, like ReachSt, or — for the six — one field widened in
the generic half.

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

1. **The six Fibonacci rows — they want a second REPRESENTATIVE, not a
   second code (wave 4v).**  Wave 4r built `(Fib, 1)` and boarded the five φ
   rows that had partial ladder boards on disk.  The rest had "never been
   through `emit_ladder` at all", and wave 4s found out why: `find_families`
   runs its numeration pass only `if not found`, and these rows return 26-odd
   junk positional families at chain 8 — `min_chain`, the floor — which
   switched the pass off.  Under `valfam.py --numeration` six of the seven
   read as Fibonacci counters at chains of 232–376.

   Wave 4s read their weights as `1, 2, 3, 5, 8` and called them Zeckendorf.
   **Wave 4v measured that they are the kernel's own `1, 1, 2, 3, 5, 8` with
   a constant marker cell dropped** — `fit_weights` cannot pin a column that
   never varies, so it discards the bottom rung instead of completing it.
   Read with that cell, every number is `LadderFam`'s: `fibw`, `fam_lim k =
   S (fibsum k)`, widths spanning `[fibw k .. fibsum k]`, the top of a width
   `1^k` at `fibsum k`, value = anchor visit index.

   What differs is which member of each value's class the counter stands on.
   `fibw` is redundant, `fibdec`/`fibokb` pick the greedy member, and these
   six stand on the LAZY one — LSB-first, top digit 1, no two zeros adjacent
   — on all 23,614 measured values and at every anchor.  Their two interior
   classes and two fills are measured and validated against the orbit in
   `tools/ladder/fiblazy.py`, and the kernel gap is one field: `Class`'s and
   `Fill`'s run unit is a single digit where these laws need a two-cell WORD.
   Six of the six carry no shadow, and all six are the same sub-machine, so
   one instance boards all six.  Per-row anchors and ladders:
   `tools/counters/FIB_ELEVEN.txt`, `tools/counters/fibform.py`,
   `docs/CORE_3STATE.md` §3, `docs/LADDER_PLAN.md` §4v.

   **The seventh is not one of them.**  `1RB0RB_0LC1RD_1LC1LA_0LA1RB` finds
   no family at ANY anchor — `digit_words` names nothing — so it belongs in
   the `no anchor` population.  It carries a shadow.
2. **The five 0RB shadows on five core rows — but there is nothing to do.**
   A shadow satisfies the `skipped` disjunct only while its core row is
   deferred, so it needs a board of its own exactly when its core row boards,
   and not before.  All five carriers are still undecided.  And when one does
   board, **its shadows now fall with it automatically**: the whole argument
   is one lemma (`Census/ShadowBoard.shadow_nqh` — the prefix is all blanks,
   what is left is the boarded row relabelled, three `vm_compute`s), and
   `make closeout` runs `gen_shadow.py --harvest` to emit it.  Wave 4u is the
   first time that fired in anger: `1RB1LA_0LA1RC_0RD0RB_1RA---` boarded and
   `SH_0RB1LC_1LA1RB_0LD0LA_1LB___.v` came with it, nobody typing anything.
   So these five rows are not a task, they are 5 of the 20 that come free
   with whatever settles their partners.  (That reading used to end "five of
   them sit on three of the four quadratic rows, so those five are not coming
   back either".  All four quadratic rows have since boarded and every one of
   those shadows came with them — which is the harvest doing exactly what it
   is for.)
3. **The two live routes**, both with named next steps: ReachSt's mirror
   transport lemma and its measured-unreachable rows
   (`docs/REACHST_TIER.md` §6), and the ladder's refused arms — SIX boards
   now stop at a single arm with every other rule proved
   (`tools/coqproject_exempt.txt` lists them, four on the interior arm and
   two on the fill arm; wave 4p measured the four and their interior cost has
   a constant SECOND difference, so no threshold or stride reaches them).
4. **The non-affine seven.**  The gate says "the certificate language cannot
   write this cost" — but `LapGlue`'s obligation never needs the cost
   written down.  Check what the closer actually demands before believing
   the gate; that check is what turned the old "non-affine 23" into 7.

## Reproducing the map

```bash
python3 tools/counters/ovfshape.py --list tools/closeout/frozen_unproven.txt --json ovf.json
python3 tools/counters/emit_lapcert.py --list tools/closeout/frozen_unproven.txt --json emit.json
```

Both are untrusted and neither needs Coq.  The first is ~20 min over the whole
list (shard it), the second similar.  `--emit` on the second writes and
`coqc`-checks a board for every machine it can derive, which is how this list
first shrank from 883 to 511 (and, wave by wave, to the current 20).
