#!/bin/bash
# Emit NEVER-quasihalting counter boards (Machines/CountersTr/LAPT_*.v,
# emit_lapcert.py --tr) for a row list, in parallel, then collect them
# into ProvTr_Lap stages.  Twin of qh_lap_emit.sh.  Box job (16 cores).
#   tools/censustr/tr_lap_emit.sh ROWS [JOBS=16] [START=12]
# START is the first free ProvTr_Lap_NN number (00..11 exist).
# A board already on disk with a .vo newer than it is skipped (resumable).
# Nothing is wired: run tools/censustr/wire_qh_stages.py at the next cut.
set -eu -o pipefail
ROWS=${1:?rows file}; JOBS=${2:-16}; START=${3:-12}
cd "$(dirname "$0")/../.."
mkdir -p census_probes/trlap
rm -f census_probes/trlap/rows_*
split -n l/$JOBS -d -a 2 "$ROWS" census_probes/trlap/rows_
ls census_probes/trlap/rows_* | xargs -P $JOBS -I{} sh -c \
  'python3 tools/counters/emit_lapcert.py --list {} --tr --emit --json {}.json > {}.log 2>&1; st=$?; echo ">>> $(basename {}): $(tail -1 {}.log) (exit $st)"; exit $st'
echo ">>> LAPT boards on disk: $(ls theories/Machines/CountersTr/LAPT_*.v | wc -l)"
python3 tools/censustr/gen_provtr_lap.py --start $START
echo ">>> commit the new boards, the new theories/CensusTr/ProvTr_Lap_*.v and _CoqProject; wiring + cut + walk come with the next batch"
