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

_**86 rows as of this commit — 65 distinct core machines + 21 0RB
re-root shadows that fall with them.**  The count moves every wave, so
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
| 40 | no interior `j = S j'` chain | | 2 | no inner family at `pow2 j` |
| 10 | no gap-free two-form family | | 2 | no inner interior chain |
| 5 | register step does not close | | 1 | no visit witness (StA) |
| 4 | no interior `j = 0` chain | | 1 | no boot chain |

| interior / overflow | n | what stops us (pre-wave-30 labels) |
|---|---:|---|
| `-`/`no-anchor` | 81 | 70 no overflow phase, 11 no anchor |
| `AFFINE`/`EXP2` | 25 | 16 no inner family at `pow2 j`, 4 no interior chain, 2 no boot chain, 2 no second exit chain, 1 no inner interior chain |
| `HIGHER`/`HIGHER` | 12 | 12 no interior chain |
| `AFFINE`/`AFFINE` | 9 | 8 no interior chain, 1 no inner family |
| `EXP3`/`EXP3` | 8 | 8 no interior chain |
| `PARITY-AFFINE` | 7 | 7 no interior chain |
| `QUAD`/`QUAD` | 4 | 4 no interior chain |
| `EXP4`/`EXP4` | 4 | 4 no interior chain |
| `AFFINE`/`HIGHER` | 2 | 1 no boot chain, 1 no inner interior chain |

### What each blocker means

* **no anchor** / **no overflow phase** — the tape never decodes as a counter
  under any of the 21 alphabets in the zoo, so there is no anchor family to
  build a lap around.  These need `tools/counters/alphabet_infer.py` to read a
  new `(A,B,C)` triple off the tape first; `gen_alphabet.py` then generates a
  PROVED Coq module for it (a wrong triple fails to compile).
* **no interior chain** — the ordinary lap is not expressible as one affine
  `srun`.  For `QUAD`/`HIGHER`/`EXP3`/`EXP4` that is a statement about the
  machine, not the search: the certificate language carries `a*j + b`.
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
has paid out: nick's lists sized the `no interior chain` bucket, then
seeded BOTH ReachSt waves (`docs/REACHST_TIER.md` — liveness of the
sparse state as termination of the state-DELETED sub-machine, 107 boards
across five flavours plus the parity-witness fix `LapCertGluePar`);
John's one-line reads exposed the bit-polarity inversion that emptied the
old 70-row interior gate (`WAVE30_FINDINGS.md` §6b); and the Inductive
prover's layer read cracked the CHAMPION — the machine blanks its whole
10,239-cell region and returns to a blank tape in `StC` at step
32,779,478, so its board is one ~17 s binary-fuel `vm_compute`
(`Machines/Counters/Champion_1RB1LD_1RC1RB_1LC1LA_0RC0RD.v`, in the tree,
awaiting the closeout regen).

Measured dead along the way (all do-not-retry): the `cycR-gap`
primitive, the double peel, the SOLO-cascade route on the boot bucket,
every framing of the 40-row interior bucket, the flat `emit_lapcert`
route, and uniform step bounds for avoid sub-machines without sweep
acceleration.

## Where a newcomer should probably start

1. **The nested interior lap** — 40 of the 65: the interior lap is
   itself a NESTED (double) lap, the one route that does not exist yet
   (`docs/WAVE33_PROMPT.md` item 1).  Everything else is a thin tail.
2. **The ReachSt leftovers** — the mirror transport lemma and the 7 rows
   PR #82 measured as unreachable by the avoid-machine method
   (`docs/REACHST_TIER.md` §6).
3. **The two-form 10** (champion aside): the Gray-code pair
   `1RB0RD_1LC0L{B,C}_1LD0LB_1RD0RA` still carries a fully specified,
   unexecuted build (`WAVE29_BOUNCER_FINDINGS.md` §7a).

## Reproducing the map

```bash
python3 tools/counters/ovfshape.py --list tools/closeout/frozen_unproven.txt --json ovf.json
python3 tools/counters/emit_lapcert.py --list tools/closeout/frozen_unproven.txt --json emit.json
```

Both are untrusted and neither needs Coq.  The first is ~20 min over the whole
list (shard it), the second similar.  `--emit` on the second writes and
`coqc`-checks a board for every machine it can derive, which is how this list
first shrank from 883 to 511 (and, wave by wave, to the current 65).
