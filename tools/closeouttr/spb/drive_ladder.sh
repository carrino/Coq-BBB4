#!/bin/bash
# SPB ladder driver: valfam.py (the value-family finder) on every row the lap
# probe failed, as the probe reports them.  Resumable (valfam skips rows in vf.jsonl).
cd "$(dirname "$0")"
ulimit -v 5000000
CAP=${CAP:-150}
while true; do
  python3 - > lad_todo.txt <<'P'
import json, os
done = set()
if os.path.exists('vf.jsonl'):
    done = set(json.loads(l)['spec'] for l in open('vf.jsonl') if l.strip())
for l in open('probe.jsonl'):
    r = json.loads(l)
    if not r['ok'] and r['spec'] not in done:
        print(r['spec'])
P
  n=$(wc -l < lad_todo.txt)
  if [ "$n" -gt 0 ]; then
    (cd ../../ladder && python3 valfam.py --list ../closeouttr/spb/lad_todo.txt --cap $CAP --json ../closeouttr/spb/vf.jsonl >> ../closeouttr/spb/valfam.log 2>&1)
  elif ! pgrep -f 'qe_probe.py tools/closeouttr/spb' >/dev/null; then
    echo "ladder driver done"; exit 0
  else
    sleep 60
  fi
done
