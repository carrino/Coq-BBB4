#!/bin/bash
# Per-transition flip sweep over a machine list (UNTRUSTED measurement).
#   usage: sweep_bucket.sh LIST BUDGET OUT     e.g.
#   tools/censustr/sweep_bucket.sh censustr_buckets/deferred_inwalk.txt 100000000 inwalk_sweep_1e8.txt
# Output line per machine: text, per-transition cnt:last, verdict
# (SUSPECT = some fired transition silent for the trailing 90%).
set -e
LIST=$1; BUDGET=${2:-100000000}; OUT=${3:-sweep.out}
HERE=$(dirname "$0")
BIN=$(mktemp -u /tmp/trcensus.XXXX)
gcc -O3 -o "$BIN" "$HERE/trcensus.c"
J=$(nproc)
TMP=$(mktemp -d)
split -n l/$J "$LIST" "$TMP/part_"
pids=""
for f in "$TMP"/part_*; do "$BIN" "$BUDGET" < "$f" > "$f.out" & pids="$pids $!"; done
wait $pids
cat "$TMP"/part_*.out > "$OUT"
rm -rf "$TMP" "$BIN"
echo "done: $(wc -l < "$OUT") machines -> $OUT"
echo "SUSPECT: $(grep -c SUSPECT "$OUT" || true)  LIVE: $(grep -c LIVE "$OUT" || true)  EDGE: $(grep -c EDGE "$OUT" || true)  HALT: $(grep -c HALT "$OUT" || true)"
