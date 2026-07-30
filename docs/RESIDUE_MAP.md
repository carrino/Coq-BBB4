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

_**226 rows as of this commit — 150 distinct core machines + 76 0RB
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
CURRENT gate partition — measured post-reader-fix and post-`lift`, one
committed row list per gate — is `tools/counters/buckets31/*.txt`
(`WAVE31_FINDINGS.md` §8; the lists partition `core_rows.txt` exactly):

| n | furthest gate today | | n | furthest gate today |
|--:|---|---|--:|---|
| 40 | no interior `j = S j'` chain | | 6 | inner fill lands off the endpoint |
| 33 | no inner family at `pow2 j` | | 4 | no interior `j = 0` chain |
| 26 | no gap-free two-form family | | 2 | no inner interior chain |
| 20 | no boot chain | | 1 | no visit witness |
| 17 | register step does not close | | 1 | no exit chain |

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

nickdrozd read the published version of this map and posted 64 machines he
was "pretty sure are all solvable"; John's live hand-reads ran alongside.
The scorecard so far: nick's checkable 12 were 12-for-12 (all boarded by
routes that did not exist a fortnight earlier), John's hand-inspections
stand at 36-for-36, and two of his one-line reads ("msb on the left",
"like a grey counter, up then down") exposed a **bit-polarity inversion in
the reader itself** — the tape was being decoded under alphabets with the
two digit words swapped, so 51 machines "counting down" were ordinary
ascending counters all along (`docs/WAVE30_FINDINGS.md` §6b).  Fixing the
reader emptied the interior gate of the 70-row bucket outright.

Three sized routes have since been *measured dead* (all do-not-retry):
the `cycR-gap` primitive fires nowhere sound and the double peel is
irrelevant (`WAVE30_FINDINGS.md` §§2, 4), and the SOLO-cascade route
boards 0 of the boot-chain bucket for five distinct causes
(`WAVE31_FINDINGS.md`, PR #74).  Wave-31 delivered the two-form board
RENDERER (14 boards, PRs #73/#74) and built the `lift` interior fallback,
which re-measured the whole frontier into the gate table above.  The
structure now:

* **39 rows** are the **bounded inner carrier**'s measured target — the
  33 `no inner family at pow2 j` plus the 6 off-endpoint fills
  (`tailcert_innerfam33.txt` / `tailcert_filloff6.txt`) — the only
  wave-31 item whose stated size survived contact with the data, and the
  only one needing new Coq.  First build of `docs/WAVE32_PROMPT.md`.
* **40 rows, `no interior j = S j' chain`** — 38 of them dead at BOTH
  parities on the successor half while `j = 0` derives exactly.  Never
  had a route item written for it; the standing do-not-retry on "a
  deeper peel" covers only the `j = 0` half, so the obvious experiment
  is open, not closed (WAVE32_PROMPT item 2).
* **17 rows, `register step does not close`** — the measured
  `Theta(4^k)` DOUBLE nesting (wall +4 per overflow, mechanising John's
  read); the single-nesting register step cannot close them.
* **26 rows, no gap-free two-form family** (the champion among them) —
  re-measured at every anchor family, both mirrors, tolerant and
  parity-split readers; all survive.  Where the difficulty looks real.

## Where a newcomer should probably start

1. **The wave-32 prompt's ordered builds** (`docs/WAVE32_PROMPT.md`):
   the bounded inner carrier (39 rows, one lemma), then the 40-row
   `j = S j'` bucket.
2. **The 11 no-anchor.** Their resting tapes are regular families that are
   NOT digit words (five are solid blocks of ones — index the family by
   the wall, do not hunt for an alphabet; `WAVE29_BOUNCER_FINDINGS.md`
   §§7–8 has a measured reading for every one, including two Gray-code
   counters whose build is fully specified and unexecuted).
3. **The no gap-free two-form 26.**  Fresh eyes on the decomposition;
   every mechanical re-read has been tried and is recorded.

## Reproducing the map

```bash
python3 tools/counters/ovfshape.py --list tools/closeout/frozen_unproven.txt --json ovf.json
python3 tools/counters/emit_lapcert.py --list tools/closeout/frozen_unproven.txt --json emit.json
```

Both are untrusted and neither needs Coq.  The first is ~20 min over the whole
list (shard it), the second similar.  `--emit` on the second writes and
`coqc`-checks a board for every machine it can derive, which is how this list
first shrank from 883 to 511 (and, wave by wave, to the current 150).
