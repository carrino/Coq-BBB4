# The residue, characterised

_The frontier of this project, published as a target list rather than as an
apology.  Companion data: `tools/closeout/residue_map.tsv`, one row per
machine, regenerated with the commands at the bottom._

_**621 rows as of this commit.**  The count moves every wave, so treat the TSV
as the authority and this prose as a snapshot.  With tower #20 boarded on
2026-07-28 the (4,2) HOLDOUT list is closed, so all 621 are residue and this
is the entire remaining problem._

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
kernel-checked fact about these 621 rows is that they are *absent* from the
boarded set.

## The families

| interior / overflow | n | what stops us |
|---|---:|---|
| `AFFINE`/`EXP2` | 242 | 134 no inner family at `pow2 j`, 65 no exit chain, 20 no boot chain, 8 no interior chain, 8 no shift chain, 5 no second exit chain, 2 no inner interior chain |
| `-`/`no-anchor` | 235 | 211 no overflow phase, 24 no anchor |
| `AFFINE`/`AFFINE` | 52 | 23 no inner family, 15 no visit witness (`StA`), 14 no interior chain |
| `QUAD`/`QUAD` | 41 | 41 no interior chain |
| `PARITY-AFFINE` | 13 | 13 no interior chain |
| `HIGHER`/`HIGHER` | 13 | 13 no interior chain |
| `EXP3`/`EXP3` | 10 | 10 no interior chain |
| `AFFINE`/`HIGHER` | 9 | 5 no inner family, 2 no boot chain, 2 no inner interior chain |
| `EXP4`/`EXP4` | 6 | 6 no interior chain |

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
* **no boot / exit / shift / second exit chain** — the nested overflow's
  pieces; the ones that say *shift* or *second exit* already have BOTH inner
  families identified and are missing only one affine chain.  **These 13 are
  the cheapest machines on the list.**
* **no visit witness (`StA` is targeted)** — a complete lap, but one state
  never fires inside it.  `docs/WAVE16_FINDINGS.md` §6b has the full analysis:
  these are quasihalters whose quiet state is `StA` (last visit at step 4-11,
  simulated), and what is actually true of them is symbol-aware — `StD` never
  READS `S1` after the boot.  `QHBound 12` covers all 15.

## Where a newcomer should probably start

1. **The 13 `no shift chain` / `no second exit chain`.** Both inner families
   found, one chain missing.
2. **The 15 `no visit witness`.** The analysis is done and written up; what is
   missing is a symbol-aware closer, and the bound is tiny.
3. **The 41 `QUAD`/`QUAD`.** The largest family in the residue that has never
   had a design pass — a quadratic interior AND overflow.  `Bounce_8.v`'s
   `MeasureGlue` nesting is the precedent.
4. **The 235 no-anchor.** Largest single bucket, and the cheapest per machine
   *if* the alphabet inference generalises: wave-14 inferred 18 alphabets from
   tapes this way.

## Reproducing the map

```bash
python3 tools/counters/ovfshape.py --list tools/closeout/frozen_unproven.txt --json ovf.json
python3 tools/counters/emit_lapcert.py --list tools/closeout/frozen_unproven.txt --json emit.json
```

Both are untrusted and neither needs Coq.  The first is ~20 min over the whole
list (shard it), the second similar.  `--emit` on the second writes and
`coqc`-checks a board for every machine it can derive, which is how this list
shrank from 883 to 621.
