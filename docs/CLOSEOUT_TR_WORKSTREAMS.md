# Closeout workstream prompts

Paste one of these into a new Claude Code session, one session per prompt. The prompts are self-contained, and their slices and batch tags never overlap. The workflow they all follow is in [`CLOSEOUT_TR.md`](CLOSEOUT_TR.md).

| # | Workstream | Tag | Rows |
|---|---|---|---:|
| 1–4 | Dense rows by RepWL, slices 0–3 (slice 0 also takes the edge rows) | RW0–RW3 | ~1,006 each |
| 5 | Quiet (QH) rows: diagnose, then board | QC, QH | 2,715 |
| 6 | Sparse hybrids: a new checker (research) | SP | 4,154 |
| 7 | The n-gram route on dense rows RepWL misses | NG | whatever RW0–RW3 fail |

## 1. Dense rows by RepWL, slice 0 of 4 (`RW0`)

```text
Repository carrino/Coq-BBB4. Base: if PR #146 is merged, branch from `main`; otherwise fetch `claude/instruction-beeping-proof-scope-ww7zdk` and branch from it (it carries the closeout scaffold).

Context: the instruction-level census is frozen at v10 with 10,924 deferred rows, settled OUTSIDE the census in batch files `theories/CloseoutTr/CBT_<TAG>_<NN>.v`. Read `docs/CLOSEOUT_TR.md` first; it has the whole workflow. Never edit `theories/CensusTr/DeferredTr_*`, `RunTr.v` or anything that would force a census re-walk.

Your workstream: class DN (dense: every instruction still firing at 1e8 steps), slice 0 of 4, batch tag `RW0`. Also take the class ED rows (22 edge rows): append `python3 tools/closeouttr/classes.py shard ED 0 1` to your list.

1. `python3 tools/closeouttr/classes.py shard DN 0 4 > my_rows.txt`
2. `make Makefile.coq && make -f Makefile.coq -j4 theories/CloseoutTr/CloseoutTr.vo theories/CensusTr/RepWLTr.vo`
3. `cd tools/censustr && python3 rw_cert_find.py find /dev/null ../../found_rw0.json --list ../../my_rows.txt --jobs 4 --timeout 60` in the background (untrusted, resumable, 2 GB per worker). Process results in chunks of ~200 as they land.
4. `python3 tools/closeouttr/rw_batch.py found_rw0.json --tag RW0`; compile each new `CBT_RW0_NN.v` (`make -f Makefile.coq theories/CloseoutTr/CBT_RW0_NN.vo`); if Coq rejects a row, regenerate with `--skip SPEC`. Then `make closeout-tr`.
5. Before each commit: `python3 tools/closeouttr/gen_closeout_tr.py --check`, `python3 tools/check_coqproject.py`, `python3 tools/census_cache.py --check`. Commit the batches plus the regenerated files, push, open a PR. On merge conflicts in generated files, take either side and rerun `gen_closeout_tr.py`.
6. Record the yield (certified / no closure / timeout / no cert, timings) in `SCOPING_INSTR.md` §7.4 with real counts, and commit the failed specs as `closeouttr_fail_rw0.txt` for the n-gram workstream.

Done: the slice fully judged, every certified row boarded in CI-green batches, the yields recorded.
```

## 2. Dense rows by RepWL, slice 1 of 4 (`RW1`)

```text
Repository carrino/Coq-BBB4. Base: if PR #146 is merged, branch from `main`; otherwise fetch `claude/instruction-beeping-proof-scope-ww7zdk` and branch from it (it carries the closeout scaffold).

Context: the instruction-level census is frozen at v10 with 10,924 deferred rows, settled OUTSIDE the census in batch files `theories/CloseoutTr/CBT_<TAG>_<NN>.v`. Read `docs/CLOSEOUT_TR.md` first; it has the whole workflow. Never edit `theories/CensusTr/DeferredTr_*`, `RunTr.v` or anything that would force a census re-walk.

Your workstream: class DN (dense: every instruction still firing at 1e8 steps), slice 1 of 4, batch tag `RW1`.

1. `python3 tools/closeouttr/classes.py shard DN 1 4 > my_rows.txt`
2. `make Makefile.coq && make -f Makefile.coq -j4 theories/CloseoutTr/CloseoutTr.vo theories/CensusTr/RepWLTr.vo`
3. `cd tools/censustr && python3 rw_cert_find.py find /dev/null ../../found_rw1.json --list ../../my_rows.txt --jobs 4 --timeout 60` in the background (untrusted, resumable, 2 GB per worker). Process results in chunks of ~200 as they land.
4. `python3 tools/closeouttr/rw_batch.py found_rw1.json --tag RW1`; compile each new `CBT_RW1_NN.v` (`make -f Makefile.coq theories/CloseoutTr/CBT_RW1_NN.vo`); if Coq rejects a row, regenerate with `--skip SPEC`. Then `make closeout-tr`.
5. Before each commit: `python3 tools/closeouttr/gen_closeout_tr.py --check`, `python3 tools/check_coqproject.py`, `python3 tools/census_cache.py --check`. Commit the batches plus the regenerated files, push, open a PR. On merge conflicts in generated files, take either side and rerun `gen_closeout_tr.py`.
6. Record the yield (certified / no closure / timeout / no cert, timings) in `SCOPING_INSTR.md` §7.4 with real counts, and commit the failed specs as `closeouttr_fail_rw1.txt` for the n-gram workstream.

Done: the slice fully judged, every certified row boarded in CI-green batches, the yields recorded.
```

## 3. Dense rows by RepWL, slice 2 of 4 (`RW2`)

```text
Repository carrino/Coq-BBB4. Base: if PR #146 is merged, branch from `main`; otherwise fetch `claude/instruction-beeping-proof-scope-ww7zdk` and branch from it (it carries the closeout scaffold).

Context: the instruction-level census is frozen at v10 with 10,924 deferred rows, settled OUTSIDE the census in batch files `theories/CloseoutTr/CBT_<TAG>_<NN>.v`. Read `docs/CLOSEOUT_TR.md` first; it has the whole workflow. Never edit `theories/CensusTr/DeferredTr_*`, `RunTr.v` or anything that would force a census re-walk.

Your workstream: class DN (dense: every instruction still firing at 1e8 steps), slice 2 of 4, batch tag `RW2`.

1. `python3 tools/closeouttr/classes.py shard DN 2 4 > my_rows.txt`
2. `make Makefile.coq && make -f Makefile.coq -j4 theories/CloseoutTr/CloseoutTr.vo theories/CensusTr/RepWLTr.vo`
3. `cd tools/censustr && python3 rw_cert_find.py find /dev/null ../../found_rw2.json --list ../../my_rows.txt --jobs 4 --timeout 60` in the background (untrusted, resumable, 2 GB per worker). Process results in chunks of ~200 as they land.
4. `python3 tools/closeouttr/rw_batch.py found_rw2.json --tag RW2`; compile each new `CBT_RW2_NN.v` (`make -f Makefile.coq theories/CloseoutTr/CBT_RW2_NN.vo`); if Coq rejects a row, regenerate with `--skip SPEC`. Then `make closeout-tr`.
5. Before each commit: `python3 tools/closeouttr/gen_closeout_tr.py --check`, `python3 tools/check_coqproject.py`, `python3 tools/census_cache.py --check`. Commit the batches plus the regenerated files, push, open a PR. On merge conflicts in generated files, take either side and rerun `gen_closeout_tr.py`.
6. Record the yield (certified / no closure / timeout / no cert, timings) in `SCOPING_INSTR.md` §7.4 with real counts, and commit the failed specs as `closeouttr_fail_rw2.txt` for the n-gram workstream.

Done: the slice fully judged, every certified row boarded in CI-green batches, the yields recorded.
```

## 4. Dense rows by RepWL, slice 3 of 4 (`RW3`)

```text
Repository carrino/Coq-BBB4. Base: if PR #146 is merged, branch from `main`; otherwise fetch `claude/instruction-beeping-proof-scope-ww7zdk` and branch from it (it carries the closeout scaffold).

Context: the instruction-level census is frozen at v10 with 10,924 deferred rows, settled OUTSIDE the census in batch files `theories/CloseoutTr/CBT_<TAG>_<NN>.v`. Read `docs/CLOSEOUT_TR.md` first; it has the whole workflow. Never edit `theories/CensusTr/DeferredTr_*`, `RunTr.v` or anything that would force a census re-walk.

Your workstream: class DN (dense: every instruction still firing at 1e8 steps), slice 3 of 4, batch tag `RW3`.

1. `python3 tools/closeouttr/classes.py shard DN 3 4 > my_rows.txt`
2. `make Makefile.coq && make -f Makefile.coq -j4 theories/CloseoutTr/CloseoutTr.vo theories/CensusTr/RepWLTr.vo`
3. `cd tools/censustr && python3 rw_cert_find.py find /dev/null ../../found_rw3.json --list ../../my_rows.txt --jobs 4 --timeout 60` in the background (untrusted, resumable, 2 GB per worker). Process results in chunks of ~200 as they land.
4. `python3 tools/closeouttr/rw_batch.py found_rw3.json --tag RW3`; compile each new `CBT_RW3_NN.v` (`make -f Makefile.coq theories/CloseoutTr/CBT_RW3_NN.vo`); if Coq rejects a row, regenerate with `--skip SPEC`. Then `make closeout-tr`.
5. Before each commit: `python3 tools/closeouttr/gen_closeout_tr.py --check`, `python3 tools/check_coqproject.py`, `python3 tools/census_cache.py --check`. Commit the batches plus the regenerated files, push, open a PR. On merge conflicts in generated files, take either side and rerun `gen_closeout_tr.py`.
6. Record the yield (certified / no closure / timeout / no cert, timings) in `SCOPING_INSTR.md` §7.4 with real counts, and commit the failed specs as `closeouttr_fail_rw3.txt` for the n-gram workstream.

Done: the slice fully judged, every certified row boarded in CI-green batches, the yields recorded.
```

## 5. Quiet (QH) rows (`QC`)

```text
Repository carrino/Coq-BBB4. Base: if PR #146 is merged, branch from `main`; otherwise fetch `claude/instruction-beeping-proof-scope-ww7zdk` and branch from it (it carries the closeout scaffold).

Context: the instruction-level census is frozen at v10 with 10,924 deferred rows, settled OUTSIDE the census in batch files `theories/CloseoutTr/CBT_<TAG>_<NN>.v`. Read `docs/CLOSEOUT_TR.md` first; it has the whole workflow. Never edit `theories/CensusTr/DeferredTr_*`, `RunTr.v` or anything that would force a census re-walk.

Your workstream: class QH (2,715 rows, `python3 tools/closeouttr/classes.py shard QH 0 1`), batch tags `QC` (and `QH` for RepWL wins). These have some instruction silent from before 1e7 steps in the 1e8 scan (`censustr_v9_scan_1e8.txt`): quasihalting candidates. A random 40 through the wrapped RepWL finder (`rw_cert_find.py find --qh --scan censustr_v9_scan_1e8.txt`) certified only 1: 27 had no closure, 12 timed out. An earlier sample found 56 of 70 QH counter rows with no visible counter phase.

1. Diagnose: sample ~100 rows, simulate them (`tools/censustr/trcensus.c`, or a small simulator), and classify by behaviour: counters (and their base), bouncers, translated cyclers after a long prefix, start-up transients, and so on. Record the breakdown with real counts in `SCOPING_INSTR.md` §7.4.
2. For each sizable sub-class, name the route that fits and try it. Existing machinery: quiet-instruction translated cyclers (`Checkers/TCyclerQHTr.v`, `tools/censustr/tc_find.py`, `gen_provtr_tcqh.py`), lap-certificate counter boards (`Counters/LapGlueQHTr.v`, `LAPQ_*`, `tools/censustr/qh_lap_emit.sh`, `gen_provtr_lapqh.py`), and the wrapped RepWL tier (`QHConveyorTr.rwqh_stage`, `tools/closeouttr/qh_batch.py`).
3. Board what certifies (a row needs `coversTr (row_to_tm r)`, via `CloseoutKitTr.coversTr_qh` or `coversTr_qh3`; `tools/closeouttr/cbt.py` writes a batch for any proof text), then `make closeout-tr`. Before each commit: `python3 tools/closeouttr/gen_closeout_tr.py --check`, `python3 tools/check_coqproject.py`, `python3 tools/census_cache.py --check`. Commit the batches plus the regenerated files, push, open a PR. On merge conflicts in generated files, take either side and rerun `gen_closeout_tr.py`.

Done: a written diagnosis with counts, the fitting route per sub-class, and whatever the existing machinery can board, boarded.
```

## 6. Sparse hybrids (`SP`)

```text
Repository carrino/Coq-BBB4. Base: if PR #146 is merged, branch from `main`; otherwise fetch `claude/instruction-beeping-proof-scope-ww7zdk` and branch from it (it carries the closeout scaffold).

Context: the instruction-level census is frozen at v10 with 10,924 deferred rows, settled OUTSIDE the census in batch files `theories/CloseoutTr/CBT_<TAG>_<NN>.v`. Read `docs/CLOSEOUT_TR.md` first; it has the whole workflow. Never edit `theories/CensusTr/DeferredTr_*`, `RunTr.v` or anything that would force a census re-walk.

Your workstream: class SP (4,154 rows, `python3 tools/closeouttr/classes.py shard SP 0 1`), batch tag `SP`. In the 1e8-step scan every instruction still fires, but the quietest one last fires between 1e7 and 9e7: it fires in geometric bursts (a counter's carry). The obligation is `NeverQuasiHaltsTr`: every fired instruction fires again. The state-level proof never had this problem, because a state recurs via either of its two instructions; here the rare carry instruction itself must be proved to recur. RepWL (`CensusTr/RepWLTr.v`) forgets the counter, and n-gram closures cannot see it. `SCOPING_INSTR.md` §7.3f has the class anatomy.

1. Sample ~50 rows, simulate, and characterise the bursts (period growth, the tape at each fire of the rare instruction). Record findings with counts in `SCOPING_INSTR.md` §7.4.
2. Design a sound criterion proving the rare instruction recurs: for example an inductive-rule / counter-segment argument (prior art: the state level's ladder in `docs/LADDER_PLAN.md`, the lap certificates in `theories/Counters/LapGlueTr.v`), or a closure variant that carries a counter abstraction. Prefer reusing an existing checker's soundness proof with a new target over writing a new one.
3. Prototype the finder (untrusted Python) and measure its yield on the sample. If it works, build the Coq side with a soundness theorem concluding `NeverQuasiHaltsTr`, and board a first batch via `tools/closeouttr/cbt.py` (entry lemma `CloseoutKitTr.coversTr_nqh`). Before each commit: `python3 tools/closeouttr/gen_closeout_tr.py --check`, `python3 tools/check_coqproject.py`, `python3 tools/census_cache.py --check`. Commit the batches plus the regenerated files, push, open a PR. On merge conflicts in generated files, take either side and rerun `gen_closeout_tr.py`.

Done: a written characterisation with counts, a design with its soundness argument, and either a first CI-green batch or a clear report of what blocks it.
```

## 7. The n-gram route (`NG`)

```text
Repository carrino/Coq-BBB4. Base: if PR #146 is merged, branch from `main`; otherwise fetch `claude/instruction-beeping-proof-scope-ww7zdk` and branch from it (it carries the closeout scaffold).

Context: the instruction-level census is frozen at v10 with 10,924 deferred rows, settled OUTSIDE the census in batch files `theories/CloseoutTr/CBT_<TAG>_<NN>.v`. Read `docs/CLOSEOUT_TR.md` first; it has the whole workflow. Never edit `theories/CensusTr/DeferredTr_*`, `RunTr.v` or anything that would force a census re-walk.

Your workstream: the dense rows RepWL misses, batch tag `NG`. Class DN (4,033 rows) is being run through the RepWL finder by four sessions (tags RW0..RW3); the rows they fail land as `closeouttr_fail_rw*.txt`. `SCOPING_INSTR.md` §7.1y records that at instruction level the rank gap on log counters is a window-size gap: they need n-gram window 4 to 6, where the state level got by with less.

1. Until the fail lists land, use a sample: `python3 tools/closeouttr/classes.py shard DN 0 40` (about 100 rows).
2. Find the transition-level n-gram and history n-gram checkers (`theories/Checkers/NGramHistTr.v`, `theories/ClosureTr.v`, the rank rungs in `CensusTr/RunTr.v`) and their untrusted drivers under `tools/`. Measure the certify rate and time per row at windows 4, 5 and 6 on the sample, and record a table with real counts in `SCOPING_INSTR.md` §7.4.
3. Write a batch generator, modelled on `tools/closeouttr/rw_batch.py` (`tools/closeouttr/cbt.py` writes the file), that proves `coversTr (row_to_tm r)` via `CloseoutKitTr.coversTr_nqh` and the checker's soundness theorem, with Coq re-running the check (avoid large certificate literals where possible). Board what certifies. Before each commit: `python3 tools/closeouttr/gen_closeout_tr.py --check`, `python3 tools/check_coqproject.py`, `python3 tools/census_cache.py --check`. Commit the batches plus the regenerated files, push, open a PR. On merge conflicts in generated files, take either side and rerun `gen_closeout_tr.py`.

Done: a measured yield table, a working `NG` batch generator, and the first batches boarded.
```
