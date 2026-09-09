#!/bin/bash
# Overnight box run (2026-09-09): the QH-side counter boards, end to end.
#   1. build the trusted files the boards import (QHConveyorTr and below)
#   2. emit + kernel-check a LAPQ_ board per log-extent QH row (16 shards,
#      ~1 h), collect them into ProvTr_QH_03.. (qh_lap_emit.sh)
#   3. wire the new stages into _CoqProject and [provqh_tr] (RunTr.v)
#   4. cut the v9 deferred list (v8 minus everything the stages prove) and
#      regenerate the DeferredTr tables
#   5. re-walk: make census-tr-walk WALK_JOBS=7 (~3 h), Print Assumptions
# Nothing is committed: review `git status`, then commit and push.
# Run as:  nohup tools/censustr/overnight_qh.sh > overnight_qh.log 2>&1 &
# Every phase aborts the run on failure (set -e), so a partial state is
# always visible in the log rather than walked over.
set -eu -o pipefail
cd "$(dirname "$0")/../.."
eval $(opam env --switch=census --set-switch)
OLD=${OLD:-censustr_deferred_v8.txt}; NEW=${NEW:-censustr_deferred_v9.txt}
JOBS=${JOBS:-16}; WALK_JOBS=${WALK_JOBS:-7}
date; echo ">>> pull (origin = the Windows checkout; pull there first)"
git pull --no-rebase || true
date; echo ">>> 1. build QHConveyorTr.vo (TCyclerQHTr, LapGlueQHTr and below)"
coq_makefile -f _CoqProject -o Makefile.coq
make -f Makefile.coq theories/CensusTr/QHConveyorTr.vo
date; echo ">>> 2. emit the LAPQ boards ($JOBS shards) and collect the stages"
tools/censustr/qh_lap_emit.sh censustr_qh_log_rows.txt $JOBS 3
date; echo ">>> 3. wire the stages"
python3 tools/censustr/wire_qh_stages.py
python3 tools/check_coqproject.py
date; echo ">>> 4. cut $NEW"
python3 tools/censustr/cut_deferred.py $OLD $NEW
python3 tools/check_coqproject.py
python3 tools/census_cache.py --check
date; echo ">>> 5. re-walk (WALK_JOBS=$WALK_JOBS)"
make census-tr-walk WALK_JOBS=$WALK_JOBS
date; echo ">>> axioms"
echo 'Require Import BBB4.CensusTr.Compute.Census_TheoremTr. Print Assumptions census_tr.' \
  | coqtop -Q theories BBB4 -w none 2>&1 | grep -v '^$' | tail -5
date; echo ">>> done: review, commit, push"
git status --short | grep -v '^??' | head -20
echo "new stages: $(ls theories/CensusTr/ProvTr_QH_*.v | wc -l) files, boards: $(ls theories/Machines/CountersTr/LAPQ_*.v | wc -l), $NEW: $(wc -l < $NEW) rows"
