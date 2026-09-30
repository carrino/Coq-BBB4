# The transition-level closeout: working on the 10,924 rows in parallel

The instruction-level census is **frozen at v10**. `census_tr` is walked
(96/96 units) and says every (4,2) machine satisfies `QHBoundTr B_tr` or is
in the orbit of one of 10,924 deferred rows. From now on those rows are
settled **outside** the census, in batch files, the same way the state-level
proof settled its 5,156 (`theories/Closeout/`). No batch forces a cut, a
re-walk or a box run. Each one is a small file that CI kernel-checks in
seconds.

```
census_tr                  : forall tm, QHBoundTr B_tr tm \/ Deferred D_tr tm      (frozen, box)
closeout_tr_partial        : Deferred D_tr tm -> QHBoundTr B_tr tm \/ Deferred D_remaining_tr tm   (CI)
bbbt4_target               : forall tm, QHBoundTr B_tr tm \/ Deferred D_remaining_tr tm           (box)
```

When `closeouttr_remaining.txt` is empty, `Deferred [] tm` is uninhabited and
the transition-level bound is unconditional.

## The pieces

| File | What it is |
|---|---|
| `theories/CloseoutTr/CloseoutKitTr.v` | `coversTr`, the entry lemmas (`coversTr_nqh`, `coversTr_qh`, `coversTr_qh3`, the `_at` variants), the orbit induction `deferred_split_tr`, the fast reflective membership check |
| `theories/CloseoutTr/CBT_<TAG>_<NN>.v` | a batch: rows, each with a `coversTr` proof |
| `theories/CloseoutTr/RemainingTr.v`, `CloseoutTr.v` | **generated** by `tools/closeouttr/gen_closeout_tr.py` |
| `theories/CloseoutTr/CloseoutFinalTr.v` | the chain through `census_tr` (needs the walk's `.vo`, so box only: `make closeout-tr-final`) |
| `closeouttr_remaining.txt`, `closeouttr_boarded.tsv` | **generated**: the open rows, and which batch boarded each closed one |
| `closeouttr_classes.tsv` | the fixed class of every v10 row (from the 1e8-step scan) |
| `tools/closeouttr/` | `cbt.py` (batch writer), `rw_batch.py`, `qh_batch.py`, `qc_batch.py` (lap boards inline, quiet cyclers), `qe_probe.py` (lap-emitter failure buckets, every anchor; `--tr` for the never-QH side), `ng_batch.py` (n-gram rank tier, probe + batch), `qs_batch.py` (sweep counters: certificate search + batch, `SweepGlueTr`), `sw_batch.py` (never-QH sweep counters: family-cycle certificate search + batch, `SweepGlueNeverTr`), `dx_char.py` (class characterisation), `dx_tc_batch.py` (translated cyclers), `dx_irqh_batch.py` (irules QH certificates, `MetaBlkPfxQHTr`), `hy_batch.py` (bouncer + counter hybrids: certificate search + batch, `HybridGlueTr`), `hy2_batch.py` (HY's residue: hybrids whose counter is base 3/4, has a long or cycling top, or no top digit; `HybridCtrTr`), `ti_batch.py` + `ti_coq.py` (multi-block sweeps: block-family exploration, rankings, batch; `TriGlueTr`), `mb_batch.py` (multi-block RepWL rows from `tools/censustr/mb_cert_find.py`, `RepWLMBTr`), `bl_ti.py` (`TriGlueTr` families on exponent lattices seeded by a concrete pass; the BL rows), `bl/classify.py` (fire regularity and block-list growth), `ta/dump.py` + `ta/nu_find.py` + `ta/nu_batch.py` (TriGlue family graphs whose rankings fail, the l-adic lexicographic liveness, batch; `TriNuTr`), `gen_closeout_tr.py`, `classes.py` |

A batch row is proved by any means at all. The only requirement is a lemma
`coversTr (row_to_tm r)`:

- never-quasihalting: `apply coversTr_nqh.`, then any `NeverQuasiHaltsTr` proof;
- quasihalting: `apply coversTr_qh.`, then `NonHalt` and `QHBoundTr B_close`
  (`B_close` is the literal `32779478`), or `coversTr_qh3` for the
  `NonHalt /\ QHBoundTr 32779478 /\ QuasiHaltsTr` triple the proven-QH stages
  produce.

## Workstreams

| Class | Rows | What they are | Route | Batch tag |
|---|---:|---|---|---|
| DN | 4,033 | dense: every instruction still firing at 1e8 | the RepWL finder with the block-length ladder takes only ~5% (193 of 4,038 on the box), the n-gram rank tier at window 4–6 about a quarter (`ng_batch.py`; 969 of 3,922 probed, §7.4.NG); then translated cyclers, `bin/irules` (the sweep counters) and lap boards (the log counters) take 1,442 more (§7.4.DX).  Of the ~1,470 left, the bouncer + counter hybrids go to the counter-and-block lap glue `HybridGlueTr` (`hy_batch.py`, §7.4.HY), the counters' emitter ports (parity split, inferred alphabets) take 148 of the 538 log counters (§7.4.CE), and the multi-family sweep glue `SweepGlueNeverTr` 239 of the 287 sweep counters irules leaves (§7.4.SW); the block-family glue `TriGlueTr` takes 48 of the SW and HY residues (§7.4.TI), and the value-family ladder in base 3/4, Fibonacci and Gray more of CE's residue (§7.4.CE2); nested arms (`LadderNest`, the quadratic carry) and closing from valfam's family alone (`famclose.py`) 108 of CE2's (§7.4.CE3); HY's residue with a base-b counter and a top table goes to `HybridCtrTr` (`hy2_batch.py`, §7.4.HY2); of the 358 hybrids and multi-block bouncers left after that, `TriGlueTr` on exponent lattices (`bl_ti.py`), the multi-block RepWL with 64-cell words and `HybridCtrTr` at a 1,800 s budget take 15.  Most of the rest are block-list counters, whose blocks follow a neighbour recurrence (`b_(i+1) = 2 b_i - 3`); no checker for them exists yet (§7.4.BL).  Of the 227 DN log counters still open, the ladder emitter's closure gaps (fill arms off by a written blank, nested arms whose rounds need a respell, the visit phase at a larger threshold) take 47; the other 172 stop in the finder, not the emitter (§7.4.LE).  Of the flat-block hybrids and bouncers (§7.4.HY3), HY2's "unary counters" are two-block transfers with a reset, which `TriGlueTr` takes once its families are seeded from the sweep-turn anchors (`hy3_ti.py`): 32 DN rows (47 with QH).  The two-lap overflow has a checker (`HybridCtr2Tr`) but no board yet.  `TriNuTr`'s 2-adic liveness takes 9 DN Collatz-like transfers (§7.4.TA); BX's cube sweep counters stay open | `RW`, `NG`, `DX0`..`DX3`, `HY`, `CE`, `SW`, `TI`, `CE2`, `CE3`, `HY2`, `BL`, `LE`, `HY3`, `TA` |
| SP | 4,154 | sparse: the quietest instruction fires in rare bursts | `bin/irules` (the doubling bouncers) and lap boards (§7.4.SP); then CE's emitter ports take 775 of the log counters and CE2's value-family ladder 351 more (`tools/closeouttr/spb/`, §7.4.SPB).  Of the 1,107 left, 605 are wide doubling bouncers and 502 counters whose ladder closure the emitter cannot build (227) or the finder does not close.  Of the 605 wide rows, the block-family glue `TriGlueTr` takes 260 (it splits by residue, so it takes the Collatz-like 3/2 maps), and `bin/irules` at 2M steps takes 100 through the v5c engine at transition level (`MetaBlkPfxV5cTr`) and the matrix meta map (`MetaBlkPfxMVTr`); 245 are left, multi-block doubling tapes and rows with no ranking (§7.4.SPW).  Of those, the lattice TriGlue finder takes 4 more.  152 fire at irregular (Collatz-like) intervals, 42 are block-list counters, and the rank tier takes none at windows 4-5 (§7.4.BL).  Of the 482 narrow counters (extent under 1,000 cells), valfam closes 171 and the emitter builds 128, 23 of them through a visit phase per instruction (`LadderCheckNestPvTr`); 23 more have a fill that narrows the counter, which `LadderFam` cannot state (§7.4.LE).  The Collatz-like rows (BL's irregular fires, HY3's parity resets) are TriGlue families whose non-firing round is `c -> 3c/2`: the 2-adic lexicographic liveness `TriNuTr` (`ta/nu_find.py`, §7.4.TA) takes 134 SP rows | `SP`, `RW`, `HY`, `SPB`, `SPW`, `BL`, `LE`, `TA` |
| QH | 2,715 | quiet: an instruction silent from before 1e7 | mostly counters, not bouncers: the wrapped RepWL finder (`--qh`, pinned from the 1e8 scan) certified 1 of a random 40 (27 no closure, 12 timeouts at 20 s). Diagnosed in §7.4.QC: counters (lap boards, `LAPQ_*`; §7.4.QE ports the emitter), sweep counters (the two-index glue `SweepGlueTr`, §7.4.QS), hybrids; §7.4.CE takes 66 more of QE's residue; the ladder on the QH side (`LadderCheckQHTr`, `sp_ladder_batch.py --qh`) 157 of CE's (§7.4.CE2), and 45 of CE2's (§7.4.CE3); of the 144 left, the emitter fixes of §7.4.LE take 6, and the rest stop in the finder; the anchor-seeded TriGlue of §7.4.HY3 15 two-block transfers whose reset rounds outgrow the 1e7 quiet window | `QH`, `QC`, `QE`, `QS`, `CE`, `CE2`, `CE3`, `LE`, `HY3` |
| ED | 22 | the scanner's edge rows | RepWL (6 of the first 9 certify) | `RW` |

Get your rows with a fixed, non-overlapping slice:

```
python3 tools/closeouttr/classes.py shard DN 0 4 > my_rows.txt   # slice 0 of 4 of class DN
python3 tools/closeouttr/classes.py stats                        # progress per class
```

**Tags are per workstream AND per slice** when several sessions share a
route: `RW0`..`RW3` for four RepWL sessions on DN, for example. Two sessions
must never write the same `CBT_<TAG>_<NN>.v`. Tags are 1–8 characters of
`[A-Z0-9]`, starting with a letter.

Ready-to-paste session prompts for each workstream: [`CLOSEOUT_TR_WORKSTREAMS.md`](CLOSEOUT_TR_WORKSTREAMS.md).

## The loop (container, no box needed)

```
# 1. find parameters (untrusted, resumable; 4 jobs fit a 16 GB container)
cd tools/censustr
python3 rw_cert_find.py find /dev/null ../../found.json --list ../../my_rows.txt --jobs 4 --timeout 60
#    quasihalting rows:  add  --qh --scan ../../censustr_v9_scan_1e8.txt
cd ../..

# 2. write batches (the rows already boarded elsewhere are skipped)
python3 tools/closeouttr/rw_batch.py found.json --tag RW0        # or qh_batch.py ... --tag QH0

# 3. kernel-check the new batches, then regenerate and check the split
make -f Makefile.coq theories/CloseoutTr/CBT_RW0_00.vo           # a rejected row: --skip SPEC, regenerate
make closeout-tr

# 4. invariants, then commit and push
python3 tools/closeouttr/gen_closeout_tr.py --check
python3 tools/check_coqproject.py
python3 tools/census_cache.py --check
```

Commit the batch files **and** the regenerated files (`RemainingTr.v`,
`CloseoutTr.v`, `closeouttr_remaining.txt`, `closeouttr_boarded.tsv`,
`_CoqProject`).

## Merging parallel work

The generated files are the only files two workstreams share. On a merge
conflict in any of them, take either side and regenerate:

```
git checkout --theirs theories/CloseoutTr/RemainingTr.v theories/CloseoutTr/CloseoutTr.v \
    closeouttr_remaining.txt closeouttr_boarded.tsv _CoqProject
python3 tools/closeouttr/gen_closeout_tr.py && make closeout-tr
```

If a row ends up in two batches, the split still holds; the first batch
alphabetically is recorded in `closeouttr_boarded.tsv`. The duplicate is
harmless, but it is wasted work, so stick to your slice.

## CI

CI kernel-checks every batch and the split on each push, sharded
(`.github/workflows/ci.yml`): `closeout-shard` runs on 6 runners, each
building the slice of `CBT_*.vo` that `tools/closeouttr/ci_shard.py K 6`
names, and ships its `.vo`; `closeout-final` merges them (a file two shards
both built must be byte-identical), checks with `make -q` that make will
rebuild no batch, then compiles `CloseoutTr.vo` and runs
`gen_closeout_tr.py --check`.  The slices are balanced on the per-batch
costs in `tools/closeouttr/ci_costs.tsv`; an unlisted batch counts as 20 s.
**If your batch takes more than about a minute to compile, add it there**
(`ci_shard.py --costs` reads the `make TIMED=1` logs every shard uploads),
or it may share a shard with another slow batch.  `ci_shard.py --plan 6`
shows the split.

## Rules

- Never edit `CensusTr/DeferredTr_*`, `RunTr.v` or the walk. The census is
  frozen, and anything that changes `D_tr` would need a re-walk.
- Never edit a generated file by hand. Rerun the generator.
- A batch must carry a `(* spec <bbchallenge text> *)` comment before every
  row. That is how the generator knows what it boards, and the kernel's
  split check catches a wrong comment.
- Compile your batch before you push. CI compiles all of them, and one bad
  row fails the whole PR.
- Record what you learned about your class (yields, failure modes, timings)
  in `SCOPING_INSTR.md` under §7.4 with real counts.
