#!/bin/bash
# LE3: vf_step.py over one shard (resumable: valfam skips rows already in its --json).
#   tools/closeouttr/le3/drive_step.sh TODO OUT.jsonl
T=$(realpath "$1"); O=$(realpath -m "$2")
cd "$(dirname "$0")"
ulimit -v ${VMEM:-3500000}
python3 vf_step.py --list "$T" --cap ${CAP:-300} --json "$O" >> "$O.log" 2>&1
