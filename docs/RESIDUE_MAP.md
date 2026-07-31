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

_**42 rows as of this commit — 30 distinct core machines + 12 0RB
re-root shadows.**  A shadow needs no new mathematics, but it does need its
own board: boarding a core machine moves its shadow into `core_rows.txt`
rather than settling it, so budget the pair (2026-07-31; worked example
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
| 14 | no interior `j = S j'` chain | | 1 | no boot chain |
| 10 | no gap-free two-form family | | 1 | no interior `j = 0` chain |
| 2 | no inner interior chain | | 1 | register step does not close |
| | | | 1 | no inner family at `pow2 j` |

(The two re-root rows wave 4o promoted out of the shadow table —
`0RB0LA_1LA1RC_0RD1RD_1LB0LB` and `0RB0LA_1RC1LA_1RD0RD_1LB0LB` — boarded
the same day and are gone from this list; they never needed a gate, only
the re-root transport.)

| interior / overflow | n | what stops us (pre-wave-30 labels) |
|---|---:|---|
| `-`/`no-anchor` | 12 | 10 no anchor, 2 no overflow phase at K=6 |
| `HIGHER`/`HIGHER` | 7 | 7 no interior chain |
| `QUAD`/`QUAD` | 4 | 4 no interior chain |
| `EXP3`/`EXP3` | 3 | 3 no interior chain |
| `AFFINE`/`EXP2` | 2 | 1 no boot chain, 1 no inner family |
| `AFFINE`/`HIGHER` | 2 | 1 no boot chain, 1 no inner interior chain |

**What that table now says, and it is the shape of the endgame:** the
residue has inverted.  It used to be dominated by `AFFINE` machines our
emitter could not frame; **14 of the 30 measure NON-AFFINE on both
branches** (`HIGHER` 7, `QUAD` 4, `EXP3` 3) — shapes whose lap
cost the certificate language cannot write as `a*j + b` — plus 12 whose
tape never decodes as a counter under any alphabet.  Only 4 rows are
affine on at least one branch.

**And `HIGHER` was never a verdict — on this bucket it was a misreading,
and five of those rows have since BOARDED.**  The `HIGHER`/`HIGHER` rows are
the FIBONACCI counters (`docs/CORE_3STATE.md` §3): `ovfshape.py` measured
their lap against a base-2 anchor, and their radix is **φ**.
`tools/counters/radix_clock.py` reads `ratio = 1.6180`, spread 0.00 across
every digit; the raw per-cell toggle counts satisfy `F(n) = F(n−1) + F(n−2)`
exactly, and re-running the anchor scan with the ladder `1,1,2,3,5,8,…`
decodes them to `0,1,2,3,4,…` with nothing skipped.  Wave 4p measured the
ladder ARM costs affine and named the numeration as the only blocker; **wave
4r built it** — `LadderFam`'s `Fib` code, `LadderCheck` 3c's third
`ClassSucc` instance, 5c's iteration and 11's quasihalter board — and the
five rows that had partial ladder boards on disk now carry `iqh_*` theorems.
**Seven remain**, and they are the whole `HIGHER` column.  So the honest
count of rows whose cost the certificate language genuinely cannot write is
**7**, not 14: `QUAD` 4 (measured on the arm in wave 4p) and `EXP3` 3.

The easy framings are spent, but what is left wants either a closer that
never needs the cost (`LapGlue`'s lap obligation is an EXISTENTIAL over
step counts, which is how the wave-19 fractals boarded with a `3^k` lap),
or a route that never models the lap at all, like ReachSt.  The numeration
route is no longer speculative — it exists, and the seven `HIGHER` rows are
what is left of the population it was built for.

### What each blocker means

* **no anchor** / **no overflow phase** — the tape never decodes as a counter
  under any of the 21 alphabets in the zoo, so there is no anchor family to
  build a lap around.  These need `tools/counters/alphabet_infer.py` to read a
  new `(A,B,C)` triple off the tape first; `gen_alphabet.py` then generates a
  PROVED Coq module for it (a wrong triple fails to compile).
* **no interior chain** — the ordinary lap is not expressible as one affine
  `srun`.  For `QUAD`/`EXP3` that is a statement about the
  machine, not the search: the certificate language carries `a*j + b`.
  **For `HIGHER` it is not** — those seven rows are the φ counters, the
  label came from measuring a Fibonacci lap on a base-2 clock, and the
  kernel can now denote that numeration (above, `docs/CORE_3STATE.md` §3,
  `docs/LADDER_PLAN.md` §4r).
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
(`Machines/Counters/Champion_1RB1LD_1RC1RB_1LC1LA_0RC0RD.v`, in the tree
and compiling).  **A closeout regen will not consume it, and no number of
re-runs will**: it proves `QHBound 32779478`, and `boarded` demands
`QHBound B_board` with `B_board` = 66,349, the PREVIOUS champion's score
(`Closeout/CloseoutKit.v`).  32,779,478 ≰ 66,349, so `inventory.py` refuses
it by the same comparison and the champion stays on this list.  Admitting
it is a `CloseoutKit` change — raise `B_board`, or give `boarded` a third
disjunct for exact-score quasihalters above it — and it buys the LOWER
bound only.  See `docs/CLAIMS.md` "What this is NOT" §1.

Measured dead along the way (all do-not-retry): the `cycR-gap` primitive,
the double peel, the SOLO-cascade route on the boot bucket, every FRAMING
of the nested-lap bucket, the flat `emit_lapcert` route, the ladder's
far-side template and its glue (§4k: measured before building it),
uniform step bounds for avoid sub-machines without sweep acceleration, a
flat arm stated with `stride = 0` (no chain at ANY depth, because `srot 0`
is the identity — it reads like "not affine" and is not), **every base-2
anchor search on the φ rows** (four waves' worth, and now explained), and the ladder ARM_GRID on the four `QUAD` rows (wave 4p
measured a second difference of exactly 2 on the arm itself; no threshold
or stride reaches a quadratic).

## Where a newcomer should probably start

1. **The seven remaining Fibonacci rows — and the kernel already speaks
   their numeration.**  Wave 4r built `(Fib, 1)` (`LadderFam`'s `Fib` code,
   `LadderCheck` 3c/5c/11) and boarded the five φ rows that had partial
   ladder boards on disk.  The other seven — six `1RB---` rows plus
   `1RB0RB_0LC1RD_1LC1LA_0LA1RB` — have **never been through `emit_ladder`
   at all**; there is no board for them on disk, partial or otherwise.  So
   nobody has yet measured whether the new code reaches them, and that
   measurement is an emitter run, not a kernel build.  It is the cheapest
   unexplored thing on the list.  Six of the seven carry no shadow;
   `1RB0RB_0LC1RD_1LC1LA_0LA1RB` carries one, so the block is 8 of the 42.
   Per-row anchors and ladders: `tools/counters/FIB_ELEVEN.txt`,
   `docs/CORE_3STATE.md` §3.
2. **The twelve 0RB shadows on ten core rows — but there is nothing to do.**
   A shadow satisfies the `skipped` disjunct only while its core row is
   deferred, so it needs a board of its own exactly when its core row boards,
   and not before.  All ten carriers are still undecided.  And when one does
   board, **its shadows now fall with it automatically**: the whole argument
   is one lemma (`Census/ShadowBoard.shadow_nqh` — the prefix is all blanks,
   what is left is the boarded row relabelled, three `vm_compute`s), and
   `make closeout` runs `gen_shadow.py --harvest` to emit it.  So these twelve
   rows are not a task, they are 12 of the 42 that come free with whatever
   settles their partners.  Five of them sit on three of the four quadratic
   rows, so those five are not coming back either.
3. **The two live routes**, both with named next steps: ReachSt's mirror
   transport lemma and its measured-unreachable rows
   (`docs/REACHST_TIER.md` §6), and the ladder's refused arms — ELEVEN
   boards now stop at a single arm with every other rule proved
   (`tools/coqproject_exempt.txt` lists them, nine on the interior arm and
   two on the fill arm; wave 4p re-measured the nine and they are five
   Fibonacci rows whose arms DERIVE plus four base-2 rows whose arm is
   genuinely quadratic).
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
first shrank from 883 to 511 (and, wave by wave, to the current 42).
