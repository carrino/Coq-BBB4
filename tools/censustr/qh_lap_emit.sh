#!/bin/bash
# Emit the QUASIHALTING-side counter boards (Machines/CountersTr/LAPQ_*.v)
# for the log-extent QH rows, in parallel, then collect them into
# ProvTr_QH stages.  Box job (16 cores): ~3,745 rows, a derive is seconds
# and a board compile ~10-30 s, so JOBS=16 is about an hour.
#   tools/censustr/qh_lap_emit.sh [ROWS=censustr_qh_log_rows.txt] [JOBS=16] [START=3]
# START is the first free ProvTr_QH_NN number (00..02 are the cyclers).
set -u
ROWS=${1:-censustr_qh_log_rows.txt}; JOBS=${2:-16}; START=${3:-3}
cd "$(dirname "$0")/../.."
mkdir -p census_probes/qhlap
split -n l/$JOBS -d -a 2 "$ROWS" census_probes/qhlap/rows_
ls census_probes/qhlap/rows_* | xargs -P $JOBS -I{} sh -c \
  'python3 tools/counters/emit_lapcert.py --list {} --qh --emit --json {}.json > {}.log 2>&1; echo ">>> $(basename {}): $(tail -1 {}.log)"'
echo ">>> boards: $(ls theories/Machines/CountersTr/LAPQ_*.v 2>/dev/null | wc -l)"
python3 tools/censustr/gen_provtr_lapqh.py --start $START
echo ">>> add the new theories/CensusTr/ProvTr_QH_*.v to _CoqProject and [provqh_tr] (RunTr.v), then push"
