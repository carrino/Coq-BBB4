#!/bin/bash
# LE2: the box run (SCOPING_INSTR 7.4.LE2).  Resumable: famclose skips the
# rows already in its --json, so a killed run just restarts.
#
#   tools/closeouttr/le2/box.sh [JOBS]        # default 12
#
# famclose with the LE2 emitter (the respell fallback) over the "families
# found but none closed" rows still open.  Then the boards and batches:
#
#   python3 tools/closeouttr/sp_ladder_batch.py tools/closeouttr/le2/fc_sp.jsonl \
#       tools/closeouttr/le2/fc_dn.jsonl --tag LE2 --chunk 40
#   python3 tools/closeouttr/sp_ladder_batch.py tools/closeouttr/le2/fc_qh.jsonl \
#       --tag LE2 --chunk 40 --qh
#   tools/closeouttr/le/board_chunk.sh CBT_LE2_NN ...
#
# Measured wall time: famclose costs 10-40 min a row here (each family goes
# through the emitter's full grid, and a family the old reading cannot close
# is re-emitted with up to four respellings).  At 12 jobs: SP 79 rows ~3 h,
# QH 43 rows ~1.5 h, DN 51 rows ~2 h.
set -e
J=${1:-12}
cd "$(dirname "$0")/../../ladder"
L=../closeouttr/le2
REM=../../../closeouttr_remaining.txt
for k in sp qh dn; do
  grep -Fxf $REM $L/rows_${k}_fam.txt > $L/todo_${k}_fam.txt || true
done
python3 famclose.py --list $L/todo_sp_fam.txt --json $L/fc_sp.jsonl --jobs $J
python3 famclose.py --list $L/todo_qh_fam.txt --json $L/fc_qh.jsonl --jobs $J --qh
python3 famclose.py --list $L/todo_dn_fam.txt --json $L/fc_dn.jsonl --jobs $J
