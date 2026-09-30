#!/bin/bash
# LE: valfam over the LE rows CE3's vf_dn_qh.jsonl does not cover, one shard
# per job.  Resumable: valfam skips rows already in vf_K.jsonl.
#   tools/closeouttr/le/drive_vf.sh K        (K = 0, 1, 2)
cd "$(dirname "$0")"
ulimit -v 5000000
K=$1
CAP=${CAP:-150}
(cd ../../ladder && python3 valfam.py --list ../closeouttr/le/vf_todo_$K.txt --cap $CAP --json ../closeouttr/le/vf_$K.jsonl >> ../closeouttr/le/vf_$K.log 2>&1)
