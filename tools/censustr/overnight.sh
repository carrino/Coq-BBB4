#!/bin/bash
# Overnight box run (2026-09-06): RepWL pass 2 on the 1,073 uncertified
# bouncers, then the first genuine --deep list-burn over the 9,657 in-walk
# rows of the v7 list (LIVE remainder first, then the quiet-instruction
# machines).  Run as:  nohup tools/censustr/overnight.sh > overnight.log 2>&1 &
# LISTBURN_JOBS=8 is a memory budget (each native shard process can take
# 3-4 GB; 31 GB box).  Outputs: theories/CensusTr/ProvTr_RW_1*.v (pass 2),
# census_probes/listburn/*.out + censustr_survivors.txt (the burn).
set -e
cd "$(dirname "$0")/../.."
eval $(opam env --switch=census --set-switch)
date; echo ">>> pull"
git pull --no-rebase carrino claude/instruction-beeping-proof-scope-ww7zdk || true
date; echo ">>> RepWL pass 2"
make census-tr-rwprobe RWPROBE_ROWS=censustr_rw_rows_v6_pass2.tsv RWPROBE_TIMEOUT=900 RWPROBE_JOBS=16
make census-tr-rwstage RWPROBE_ROWS=censustr_rw_rows_v6_pass2.tsv RWSTAGE_START=10
ls theories/CensusTr/ProvTr_RW_1*.v 2>/dev/null | wc -l
date; echo ">>> deep list-burn over the in-walk rows of v7"
make census-tr-listburn LISTBURN_SRC=censustr_deferred_v7_inwalk.txt LISTBURN_JOBS=8
date; echo ">>> done"
wc -l censustr_survivors.txt censustr_unburned.txt 2>/dev/null || true
