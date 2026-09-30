#!/bin/bash
# LE: after sp_ladder_batch.py wrote new CBT_LE_* batches: regenerate the
# split, build the new batches, run the invariant checks.
#   tools/closeouttr/le/board_chunk.sh CBT_LE_01 CBT_LE_02 ...
set -e
cd "$(dirname "$0")/../../.."
python3 tools/closeouttr/gen_closeout_tr.py | tail -1
make Makefile.coq > /dev/null
for b in "$@"; do
  s=$(date +%s); make -f Makefile.coq -j4 theories/CloseoutTr/$b.vo > /dev/null; echo "$b $(( $(date +%s) - s )) s"
done
python3 tools/closeouttr/gen_closeout_tr.py --check
python3 tools/check_coqproject.py
python3 tools/census_cache.py --check | tail -1
python3 tools/closeouttr/ci_shard.py --check 6 | tail -1
