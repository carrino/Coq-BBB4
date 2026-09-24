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
| `tools/closeouttr/` | `cbt.py` (batch writer), `rw_batch.py`, `qh_batch.py`, `gen_closeout_tr.py`, `classes.py` |

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
| DN | 4,033 | dense: every instruction still firing at 1e8 | the RepWL finder with the block-length ladder first (a 20-row sample: 11 certify), then the n-gram route at window 4–6 for the rest | `RW`, `NG` |
| SP | 4,154 | sparse: the quietest instruction fires in rare bursts | a new counter-aware recurrence checker (research); RepWL on the side | `SP`, `RW` |
| QH | 2,715 | quiet: an instruction silent from before 1e7 | the wrapped RepWL finder (`--qh`) pinned from the 1e8 scan; QH counters need a diagnosis first | `QH`, `QC` |
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
