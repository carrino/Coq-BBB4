#!/bin/bash
# SPB: board one emitted lap chunk, check, build, commit (push separately).
#   tools/closeouttr/spb/board_chunk.sh c2
set -e
cd "$(dirname "$0")/../../.."
c=$1
D=tools/closeouttr/spb
before=$(ls theories/CloseoutTr/CBT_SPB_*.v | wc -l)
python3 tools/closeouttr/sp_lap_batch.py $D/lap_$c.json --tag SPB --chunk 40
python3 tools/closeouttr/gen_closeout_tr.py | tail -1
new=$(ls theories/CloseoutTr/CBT_SPB_*.v | tail -n +$((before + 1)))
make Makefile.coq > /dev/null 2>&1
make -f Makefile.coq -j3 $(echo $new | sed 's/\.v/.vo/g') theories/CloseoutTr/RemainingTr.vo 2>&1 | grep -v '^COQC\|^COQDEP' || true
for v in $new; do [ -f ${v%.v}.vo ] || { echo "NOT BUILT: $v"; exit 1; }; done
python3 tools/closeouttr/gen_closeout_tr.py --check
python3 tools/check_coqproject.py
python3 tools/census_cache.py --check > /dev/null && echo "CENSUS CACHE: MATCH"
python3 tools/closeouttr/ci_shard.py --check 6
python3 - <<'P'
import json
D = 'tools/closeouttr/spb/'
with open(D + 'probe.tsv', 'w') as f:
    f.write('spec\tok\tsecs\tbest\n')
    for l in open(D + 'probe.jsonl'):
        r = json.loads(l); t = r['tries']
        ok = [x for x in t if x[3] == 'OK']
        best = ('OK ' + ok[0][4]) if ok else (t[-1][3] if t else 'no anchor')
        f.write('%s\t%d\t%s\t%s\n' % (r['spec'], r['ok'], r['secs'], best))
P
# only the boards this chunk wired into _CoqProject (a later chunk may be mid-emit)
git diff _CoqProject | sed -n 's/^+\(theories\/Machines\/.*\.v\)$/\1/p' | xargs git add
git add $new theories/CloseoutTr/RemainingTr.v theories/CloseoutTr/CloseoutTr.v _CoqProject \
    closeouttr_boarded.tsv closeouttr_remaining.txt $D/probe.tsv $D/ok_$c.txt $D/lap_$c.json
