#!/bin/bash
# Overnight box run (2026-09-09): the QH-side counter boards, end to end.
#   1. build the trusted files the boards import (QHConveyorTr and below)
#   2. emit + kernel-check a LAPQ_ board per log-extent QH row (16 shards,
#      ~1 h), collect them into ProvTr_QH_03.. (qh_lap_emit.sh)
#   3. wire the new stages into _CoqProject and [provqh_tr] (RunTr.v)
#   4. cut the v9 deferred list (v8 minus everything the stages prove) and
#      regenerate the DeferredTr tables
#   5. native code for the boards (the emitter compiles them with
#      -native-compiler no; the walk's stages link against their native
#      modules, so coqnative them first), then the re-walk:
#      make census-tr-walk WALK_JOBS=7 (~3 h), Print Assumptions
# Nothing is committed: review `git status`, then commit and push.
# Run as:  nohup tools/censustr/overnight_qh.sh > overnight_qh.log 2>&1 &
# Resume from phase N (earlier phases already done):  FROM=N tools/censustr/overnight_qh.sh
# Every phase aborts the run on failure (set -e), so a partial state is
# always visible in the log rather than walked over.
set -eu -o pipefail
cd "$(dirname "$0")/../.."
eval $(opam env --switch=census --set-switch)
OLD=${OLD:-censustr_deferred_v8.txt}; NEW=${NEW:-censustr_deferred_v9.txt}
JOBS=${JOBS:-16}; WALK_JOBS=${WALK_JOBS:-7}; FROM=${FROM:-1}
if [ "$FROM" -le 1 ]; then
  date; echo ">>> pull (origin = the Windows checkout; pull there first)"
  git pull --no-rebase || true
  date; echo ">>> 1. build QHConveyorTr.vo (TCyclerQHTr, LapGlueQHTr and below)"
  coq_makefile -f _CoqProject -o Makefile.coq
  make -f Makefile.coq theories/CensusTr/QHConveyorTr.vo
fi
if [ "$FROM" -le 2 ]; then
  date; echo ">>> 2. emit the LAPQ boards ($JOBS shards) and collect the stages"
  tools/censustr/qh_lap_emit.sh censustr_qh_log_rows.txt $JOBS 3
fi
if [ "$FROM" -le 3 ]; then
  date; echo ">>> 3. wire the stages"
  python3 tools/censustr/wire_qh_stages.py
  python3 tools/check_coqproject.py
fi
if [ "$FROM" -le 4 ]; then
  date; echo ">>> 4. cut $NEW"
  python3 tools/censustr/cut_deferred.py $OLD $NEW
  python3 tools/check_coqproject.py
  python3 tools/census_cache.py --check
fi
date; echo ">>> 5a. native code for the boards ($JOBS at once)"
# a board's .vo from the emitter has no .coq-native module; coqnative
# adds it without re-checking the proof (idempotent: skipped when the
# .cmxs is newer than the .vo)
for vo in theories/Machines/CountersTr/LAPQ_*.vo; do
  cmxs="theories/Machines/CountersTr/.coq-native/NBBB4_Machines_CountersTr_$(basename "$vo" .vo).cmxs"
  [ -f "$cmxs" ] && [ "$cmxs" -nt "$vo" ] || echo "$vo"
done | xargs -r -P $JOBS -n 1 coqnative -Q theories BBB4
echo ">>> boards with native code: $(ls theories/Machines/CountersTr/.coq-native/NBBB4_Machines_CountersTr_LAPQ_*.cmxs | wc -l) / $(ls theories/Machines/CountersTr/LAPQ_*.vo | wc -l)"
date; echo ">>> 5b. re-walk (WALK_JOBS=$WALK_JOBS)"
make census-tr-walk WALK_JOBS=$WALK_JOBS
date; echo ">>> axioms"
echo 'Require Import BBB4.CensusTr.Compute.Census_TheoremTr. Print Assumptions census_tr.' \
  | coqtop -Q theories BBB4 -w none 2>&1 | grep -v '^$' | tail -5
date; echo ">>> done: review, commit, push"
git status --short | grep -v '^??' | head -20
echo "new stages: $(ls theories/CensusTr/ProvTr_QH_*.v | wc -l) files, boards: $(ls theories/Machines/CountersTr/LAPQ_*.v | wc -l), $NEW: $(wc -l < $NEW) rows"
