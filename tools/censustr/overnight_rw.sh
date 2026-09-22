#!/bin/bash
# Overnight box run (2026-09-18): the bouncers, both sides, by the RepWL
# PARAMETER route (SCOPING_INSTR 7.3e): the untrusted finder
# (rw_cert_find.py, the Python mirror of RepWL.v) finds, per machine, a
# block length / threshold / start / closure size at which a per-
# instruction rank certificate exists; Coq's own tier (rw_tier_tr,
# rw_tier_qhbtr) then re-runs the search at exactly those parameters --
# measured within 4-10x of the finder -- and the stages are the existing
# parameter-closed ones (no certificate literal is stored).
#   1. build QHConveyorTr.vo (RepWLTr and below)
#   2. never-QH finder over LIVE_LIST (default the 1,031 open bouncers;
#      censustr_live_sqrt.txt for the whole sqrt class) with the
#      tape-period rows censustr_live_sqrt_rows.tsv -> censustr_rw_param_rows.tsv
#   3. RW probe (Coq search at the parameters, 1 machine per file, cap
#      PROBE_TIMEOUT, PROBE_JOBS=8: a 25K-node search is minutes and
#      GBs; closures past 30K nodes are not probed) + stage ProvTr_RW_11..
#   4. QH finder over the 2,998 quiet-instruction bouncers
#      (censustr_qh_bouncer_rows.tsv, pins from censustr_v9_scan_1e6.txt)
#      -> probe-qh (rw_tier_qhbtr) -> stage-qh ProvTr_QH_16..
#   5. wire every new stage (QH, Lap, RW), cut v10, coqnative the boards
#      emitted on the box (LAPT and LAPQ), re-walk, axioms
# Nothing is committed.  Run it from an Ubuntu shell you keep open (the
# window is what keeps the WSL distro alive; nohup/tmux die with it):
#   FROM=2 tools/censustr/overnight_rw.sh > overnight_rw.log 2>&1
# Resume from phase N:  FROM=N tools/censustr/overnight_rw.sh
# Stop after phase N:    TO=N;  re-judge the earlier passes' timeouts and
# no-closures (RETRY_WHY) as pass N:  RETRY=N FROM=2 TO=2
# Box lessons of 2026-09-21 (five VM deaths/wedges in one day): the VM
# froze with 18 GB of 32 in use and no swap, while C: ran low on the
# WINDOWS side -- the WSL swap image and the pagefile compete for that
# disk, and a full C: stalls the VM (clean teardown or wedge; the WSL
# service itself hangs).  Fixes: .wslconfig [wsl2] swap=0 memory=32GB
# vmIdleTimeout=-1, `wsl --manage Ubuntu --set-sparse true`, and 8
# workers instead of 14, then 6 (a worker on a timeout row sits at ~4 GB,
# eight of them filled the VM; --mem-gb 4 caps each).  census_probes/memlog.txt
# is a 10 s memory trace for the
# post-mortem of the next death: its last timestamp is the freeze time.
# The finders are resumable (their OUT.json is written per machine and an
# existing one is skipped over), the finder logs are
# census_probes/rw/live_find.log and census_probes/rwqh/qh_find.log (appended,
# so the rows of a run the VM killed stay visible after the resume).
set -eu -o pipefail
cd "$(dirname "$0")/../.."
eval $(opam env --switch=census --set-switch)
OLD=${OLD:-censustr_deferred_v9.txt}; NEW=${NEW:-censustr_deferred_v10.txt}
# the never-QH list: the 1,031 open bouncers by default (35% certify); the
# full 4,240-row sqrt class (censustr_live_sqrt.txt) certifies at ~8%
# because its other 3,200 rows are not RepWL shapes -- run it another night
LIVE_LIST=${LIVE_LIST:-censustr_bouncers_open.txt}
JOBS=${JOBS:-16}; FIND_JOBS=${FIND_JOBS:-12}; PROBE_JOBS=${PROBE_JOBS:-8}; WALK_JOBS=${WALK_JOBS:-7}
FROM=${FROM:-1}; TO=${TO:-5}; RETRY=${RETRY:-0}
FIND_TIMEOUT=${FIND_TIMEOUT:-300}; PROBE_TIMEOUT=${PROBE_TIMEOUT:-1800}
# the next free stage numbers (the RW stages resume at 11, the QH ones at 16)
next_stage() { local n; n=$(ls theories/CensusTr/$1_[0-9][0-9].v 2>/dev/null | sed 's/.*_\([0-9][0-9]\)\.v$/\1/' | sort -n | tail -1); n=$((10#${n:-0} + 1)); [ "$n" -lt "$2" ] && n=$2; echo $n; }
RW_START=${RW_START:-$(next_stage ProvTr_RW 11)}; QH_START=${QH_START:-$(next_stage ProvTr_QH 16)}
# RETRY=1: phases 2-3 re-judge the machines the first pass failed for a
# resource reason (timeout / past MAX_NODES / memory cap) into their own
# files -- the finder now caps closures at MAX_NODES and two of the box's
# 300 s timeouts certify in 4 s and 7 s that way -- and probe + stage only
# those (the first pass's stages stay; RW_START moves past them)
mkdir -p census_probes/rw census_probes/rwqh
CERTS=census_probes/rw/live_certs.json; ROWS=censustr_rw_param_rows.tsv
# RETRY=N re-judges the machines whose latest verdict over the first pass
# and retries 1..N-1 is a resource failure or a no-closure (RETRY_WHY):
# retry 1's files are live_certs_retry.json / censustr_rw_param_rows_retry.tsv,
# retry N's live_certs_retryN.json / censustr_rw_param_rows_retryN.tsv
if [ "$RETRY" != 0 ]; then
  prev=$CERTS; n=1
  while [ "$n" -lt "$RETRY" ]; do
    f=census_probes/rw/live_certs_retry$([ "$n" = 1 ] || echo $n).json; [ -f "$f" ] && prev="$prev $f"; n=$((n + 1))
  done
  sfx=$([ "$RETRY" = 1 ] || echo $RETRY)
  python3 tools/censustr/rw_cert_find.py failed $prev --why "${RETRY_WHY:-timeout|MAX_NODES|memory cap|no closure}" > census_probes/rw/retry_list$sfx.txt
  LIVE_LIST=census_probes/rw/retry_list$sfx.txt; CERTS=census_probes/rw/live_certs_retry$sfx.json; ROWS=censustr_rw_param_rows_retry$sfx.tsv
  echo ">>> RETRY $RETRY over: $prev"
  echo ">>> RETRY: $(wc -l < $LIVE_LIST) machines to re-judge -> $CERTS, $ROWS, ProvTr_RW_$RW_START.."
fi
# memory trace every 10 s (survives a VM death on the Linux disk)
( while true; do date +%T; free -m | sed -n 2,3p; sleep 10; done >> census_probes/memlog.txt ) &
MEMLOG_PID=$!; trap 'kill $MEMLOG_PID 2>/dev/null' EXIT
if [ "$FROM" -le 1 ]; then
  date; echo ">>> pull (origin = the Windows checkout; pull there first)"
  git pull --no-rebase || true
  date; echo ">>> 1. build QHConveyorTr.vo"
  coq_makefile -f _CoqProject -o Makefile.coq
  make -f Makefile.coq theories/CensusTr/QHConveyorTr.vo
fi
if [ "$FROM" -le 2 ] && [ "$TO" -ge 2 ]; then
  date; echo ">>> 2. never-QH finder ($FIND_JOBS jobs, ${FIND_TIMEOUT}s per machine) over $LIVE_LIST"
  python3 tools/censustr/rw_cert_find.py find --list $LIVE_LIST censustr_live_sqrt_rows.tsv $CERTS \
    --jobs $FIND_JOBS --timeout $FIND_TIMEOUT --rows-out $ROWS >> census_probes/rw/live_find.log 2>&1
  tail -3 census_probes/rw/live_find.log
fi
if [ "$FROM" -le 3 ] && [ "$TO" -ge 3 ]; then
  date; echo ">>> 3. RW probe (Coq search at the finder's parameters) + stage ProvTr_RW_$RW_START.."
  make census-tr-rwprobe RWPROBE_ROWS=$ROWS RWPROBE_TIMEOUT=$PROBE_TIMEOUT RWPROBE_JOBS=$PROBE_JOBS RWPROBE_CHUNK=1 | tail -3
  make census-tr-rwstage RWPROBE_ROWS=$ROWS RWSTAGE_START=$RW_START | tail -2
fi
if [ "$FROM" -le 4 ] && [ "$TO" -ge 4 ]; then
  date; echo ">>> 4. QH finder + probe + stage"
  python3 tools/censustr/rw_cert_find.py find --qh --scan censustr_v9_scan_1e6.txt --list censustr_qh_bouncers.txt censustr_qh_bouncer_rows.tsv \
    census_probes/rwqh/qh_certs.json --jobs $FIND_JOBS --timeout $FIND_TIMEOUT >> census_probes/rwqh/qh_find.log 2>&1
  tail -3 census_probes/rwqh/qh_find.log
  rm -f census_probes/rwqh/ProbeRQ_*
  python3 tools/censustr/rw_cert_find.py probe-qh census_probes/rwqh/qh_certs.json census_probes/rwqh --chunk 1
  ls census_probes/rwqh/ProbeRQ_*.v | xargs -P $PROBE_JOBS -I{} sh -c \
    'b=$(echo {} | sed "s/\.v$//"); timeout '"$PROBE_TIMEOUT"' coqc -Q theories BBB4 -w -abstract-large-number {} > $b.out 2>&1; true'
  echo ">>> QH probes: $(cat census_probes/rwqh/ProbeRQ_*.out | grep -c '= true') true / $(cat census_probes/rwqh/ProbeRQ_*.out | grep -c '= false') false"
  python3 tools/censustr/rw_cert_find.py stage-qh census_probes/rwqh/qh_certs.json census_probes/rwqh theories/CensusTr --start $QH_START
fi
[ "$TO" -ge 5 ] || { date; echo ">>> stopped after phase $TO (TO=$TO)"; exit 0; }
date; echo ">>> 5a. wire the stages, cut $NEW"
python3 tools/censustr/wire_qh_stages.py
python3 tools/check_coqproject.py
python3 tools/censustr/cut_deferred.py $OLD $NEW
python3 tools/check_coqproject.py
python3 tools/census_cache.py --check
date; echo ">>> 5b. native code for the boards emitted on the box"
for vo in theories/Machines/CountersTr/LAPQ_*.vo theories/Machines/CountersTr/LAPT_*.vo; do
  [ -f "$vo" ] || continue
  cmxs="theories/Machines/CountersTr/.coq-native/NBBB4_Machines_CountersTr_$(basename "$vo" .vo).cmxs"
  [ -f "$cmxs" ] && [ "$cmxs" -nt "$vo" ] || echo "$vo"
done | xargs -r -P $JOBS -n 1 coqnative -Q theories BBB4
date; echo ">>> 5c. re-walk (WALK_JOBS=$WALK_JOBS)"
make census-tr-walk WALK_JOBS=$WALK_JOBS
date; echo ">>> axioms"
echo 'Require Import BBB4.CensusTr.Compute.Census_TheoremTr. Print Assumptions census_tr.' \
  | coqtop -Q theories BBB4 -w none 2>&1 | grep -v '^$' | tail -5
date; echo ">>> done: review, commit, push"
git status --short | grep -v '^??' | head -20
echo "RW stages: $(ls theories/CensusTr/ProvTr_RW_*.v | wc -l), QH stages: $(ls theories/CensusTr/ProvTr_QH_*.v | wc -l), $NEW: $(wc -l < $NEW) rows"
