#!/bin/bash
# Run learn3.find on the rows of ROWS.txt not yet in OUT.jsonl, one process a
# row under a hard kill (multiprocessing workers can deadlock on the SIGALRM
# timeout).  Usage: one_by_one.sh ROWS.txt OUT.jsonl [SECONDS]
set -u
ROWS=$1; OUT=$2; SECS=${3:-300}
HERE=$(cd "$(dirname "$0")" && pwd)
touch "$OUT"
for s in $(python3 -c "
import json, sys
done = set(json.loads(l)['spec'] for l in open('$OUT'))
for l in open('$ROWS'):
    s = l.split()[0] if l.strip() else ''
    if s and not s.startswith('#') and s not in done:
        print(s)"); do
  out=$(timeout -s KILL $((SECS + 120)) python3 -c "
import sys, json; sys.path.insert(0, '$HERE'); sys.path.insert(0, '$HERE/..')
import learn3, lg_batch as G
print(json.dumps(G.jsonable(learn3.find('$s', $SECS))))" 2>/dev/null | tail -1)
  [ -z "$out" ] && out="{\"spec\": \"$s\", \"err\": \"hard timeout\"}"
  echo "$out" >> "$OUT"
  echo "$s $(echo "$out" | python3 -c 'import sys, json; print(json.loads(sys.stdin.read()).get("err", "OK")[:120])')"
done
