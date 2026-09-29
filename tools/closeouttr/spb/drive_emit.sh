#!/bin/bash
# SPB driver: emit lap boards for each new batch of probe-derived SP rows.
# Emits once >= CH new rows derive, or on whatever is left when the probe ends.
cd "$(dirname "$0")/../../.."
D=tools/closeouttr/spb
CH=${CH:-200}
ulimit -v 5000000
# resume: a chunk whose row list exists but whose emit never finished
# (container restart) is emitted again; boards with a fresh .vo are skipped
for f in $D/ok_c*.txt; do
  c=$(basename $f .txt); c=${c#ok_}
  if [ ! -f $D/lap_$c.json ]; then
    echo "emit chunk $c (resume): $(wc -l < $f) rows"
    (cd tools/counters && python3 emit_lapcert.py --tr --emit --list ../closeouttr/spb/ok_$c.txt --json ../closeouttr/spb/lap_$c.json > ../closeouttr/spb/emit_$c.log 2>&1)
    echo "emitted $c: $(tail -1 $D/emit_$c.log)"
  fi
done
while true; do
  n=$(ls $D/ok_c*.txt 2>/dev/null | wc -l)
  python3 - "$D" > $D/pending.txt <<'P'
import json, glob, sys
D = sys.argv[1]
seen = set()
for f in glob.glob(D + '/ok_c*.txt'):
    seen |= set(l.strip() for l in open(f))
for l in open(D + '/probe.jsonl'):
    r = json.loads(l)
    if r['ok'] and r['spec'] not in seen:
        print(r['spec'])
P
  p=$(wc -l < $D/pending.txt)
  done_probe=0; pgrep -f 'qe_probe.py tools/closeouttr/spb' >/dev/null || done_probe=1
  if [ "$p" -ge "$CH" ] || { [ "$done_probe" = 1 ] && [ "$p" -gt 0 ]; }; then
    cp $D/pending.txt $D/ok_c$n.txt
    echo "emit chunk c$n: $p rows"
    (cd tools/counters && python3 emit_lapcert.py --tr --emit --list ../closeouttr/spb/ok_c$n.txt --json ../closeouttr/spb/lap_c$n.json > ../closeouttr/spb/emit_c$n.log 2>&1)
    echo "emitted c$n: $(tail -1 $D/emit_c$n.log)"
  elif [ "$done_probe" = 1 ]; then
    echo "driver done"; exit 0
  else
    sleep 30
  fi
done
