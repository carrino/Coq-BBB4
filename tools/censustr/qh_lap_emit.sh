#!/bin/bash
# Emit the QUASIHALTING-side counter boards (Machines/CountersTr/LAPQ_*.v)
# for the log-extent QH rows, in parallel, then collect them into
# ProvTr_QH stages.  Box job (16 cores): ~3,745 rows, a derive is seconds
# and a board compile ~10-30 s, so JOBS=16 is about an hour.
#   tools/censustr/qh_lap_emit.sh [ROWS=censustr_qh_log_rows.txt] [JOBS=16] [START=3]
# START is the first free ProvTr_QH_NN number (00..02 are the cyclers).
set -eu -o pipefail
ROWS=${1:-censustr_qh_log_rows.txt}; JOBS=${2:-16}; START=${3:-3}
cd "$(dirname "$0")/../.."
mkdir -p census_probes/qhlap
# a rerun with fewer JOBS must not pick up the previous run's higher shards
rm -f census_probes/qhlap/rows_*
split -n l/$JOBS -d -a 2 "$ROWS" census_probes/qhlap/rows_
# a shard's emitter exits 0 when it ran (failed derives are counted in its
# log); a nonzero status is a crash (coqc missing, a Python exception) and
# aborts the job before collection, so a partial stage cannot look complete
ls census_probes/qhlap/rows_* | xargs -P $JOBS -I{} sh -c \
  'python3 tools/counters/emit_lapcert.py --list {} --qh --emit --json {}.json > {}.log 2>&1; st=$?; echo ">>> $(basename {}): $(tail -1 {}.log) (exit $st)"; exit $st'
echo ">>> boards: $(ls theories/Machines/CountersTr/LAPQ_*.v 2>/dev/null | wc -l)"
python3 tools/censustr/gen_provtr_lapqh.py --start $START
echo ">>> add the new theories/CensusTr/ProvTr_QH_*.v to _CoqProject and [provqh_tr] (RunTr.v), then push"
