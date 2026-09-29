#!/bin/bash
# SPB: the invariant checks on a clean worktree of HEAD (what CI sees).
set -e
cd "$(dirname "$0")/../../.."
W=$(mktemp -d)/wt
git worktree add -q "$W" HEAD
trap 'git worktree remove --force "$W"' EXIT
cd "$W"
python3 tools/check_coqproject.py
python3 tools/closeouttr/gen_closeout_tr.py --check
python3 tools/closeouttr/ci_shard.py --check 6
