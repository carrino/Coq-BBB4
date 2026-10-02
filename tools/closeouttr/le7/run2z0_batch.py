#!/usr/bin/env python3
"""LE7 marker-run boards (UNTRUSTED; SCOPING_INSTR 7.4.LE7): LE6's
`run2z_batch.py` over `run2_all.py`'s candidate lists, each candidate
emitted by `emit_run2z0.py` ([LadderCheckRun2zTr], a plain refill restated
with `z = [0]`) and compiled, the first that boards kept.

    python3 tools/closeouttr/le7/run2z0_batch.py CANDS.jsonl --tag LE7 [--chunk 10] [--jobs 4] [--dry]

Boards go to theories/Machines/LadderTr/LDRZM_<ID>.v / LDRZMQ_<ID>.v, into
_CoqProject after LadderCheckRun2zTr.v.  Then run gen_closeout_tr.py.
"""
import argparse
import json
import os
import shutil
import sys
import tempfile
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..'))
sys.path.insert(0, os.path.join(HERE, '..', 'le6'))
sys.path.insert(0, os.path.join(HERE, '..', 'le3'))
from cbt import REPO, next_free, write_batch  # noqa: E402
import step_batch as SB  # noqa: E402
import run2z_batch as RZ  # noqa: E402

RZ.EMIT = os.path.join(HERE, 'emit_run2z0.py')
RZ.EMIT_TIMEOUT = 150


def _board(t):
    spec, cands, tmp, qh = t
    whys = []
    for i, c in enumerate(cands):
        d = os.path.join(tmp, '%s_c%d' % (SB.mid(spec), i))
        os.makedirs(d, exist_ok=True)
        det = os.path.join(d, 'det.jsonl')
        with open(det, 'w') as f:
            f.write(json.dumps(c) + '\n')
        v, why = RZ.board(spec, det, d, qh)
        if v is not None:
            return spec, qh, v, i, c
        whys.append('c%d %s' % (i, why[:80]))
    return spec, qh, None, None, '; '.join(whys[:4])


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('cands')
    ap.add_argument('--tag', default='LE7')
    ap.add_argument('--chunk', type=int, default=10)
    ap.add_argument('--jobs', type=int, default=4)
    ap.add_argument('--max-cands', type=int, default=8)
    ap.add_argument('--skip', action='append', default=[])
    ap.add_argument('--dry', action='store_true', help='board only, no batch / _CoqProject')
    ap.add_argument('--log', default=None, help='append {spec, ok, cand} lines here')
    a = ap.parse_args()
    remaining = set(l.strip() for l in open(os.path.join(REPO, 'closeouttr_remaining.txt')))
    qhc = set(l.split('\t')[0] for l in open(os.path.join(REPO, 'closeouttr_classes.tsv'))
              if l.split('\t')[1:2] == ['QH'])
    todo = []
    for l in open(a.cands):
        r = json.loads(l)
        if r['cands'] and r['spec'] in remaining and r['spec'] not in a.skip:
            todo.append(r)
    kept = []
    logf = open(a.log, 'a') if a.log else None
    with tempfile.TemporaryDirectory() as tmp, Pool(a.jobs) as pool:
        jobs = [(r['spec'], r['cands'][:a.max_cands], tmp, r['spec'] in qhc) for r in todo]
        for s, qh, v, i, c in pool.imap_unordered(_board, jobs):
            if logf:
                logf.write(json.dumps(dict(spec=s, ok=v is not None,
                                           cand=c if v else None, why=None if v else c)) + '\n')
                logf.flush()
            if v is None:
                print('%-30s no board: %s' % (s, c[:200]), flush=True)
                continue
            print('%-30s board (cand %d: %s M=%s T=%s %s)' % (s, i, c['anchor'], c['M'], c['T'],
                                                               c['words']), flush=True)
            if not a.dry:
                shutil.copy(v, os.path.join(SB.BOARDS, os.path.basename(v)))
            kept.append((s, qh))
    if a.dry or not kept:
        print('%d of %d rows board' % (len(kept), len(todo)))
        return
    kept.sort()
    anchor = 'theories/Checkers/LadderCheckRun2zTr.v'
    p = os.path.join(REPO, '_CoqProject')
    lines = open(p).read().splitlines()
    new = ['theories/Machines/LadderTr/%s_%s.v' % ('LDRZMQ' if qh else 'LDRZM', SB.mid(s))
           for s, qh in kept]
    new = [x for x in new if x not in set(lines)]
    i = lines.index(anchor) + 1
    while i < len(lines) and lines[i].startswith('theories/Machines/LadderTr/LDRZM'):
        i += 1
    lines[i:i] = new
    open(p, 'w').write('\n'.join(lines) + '\n')
    nn = next_free(a.tag)
    made = []
    for j in range(0, len(kept), a.chunk):
        chunk = kept[j:j + a.chunk]
        req = ['From BBB4.Machines.LadderTr Require %s.'
               % ' '.join('%s_%s' % ('LDRZMQ' if qh else 'LDRZM', SB.mid(s)) for s, qh in chunk)]
        entries = []
        for s, qh in chunk:
            m = SB.mid(s)
            if qh:
                entries.append((s, 'apply (coversTr_qh3_at LDRZMQ_%s.tm_%s); '
                                   '[exact LDRZMQ_%s.qhtr_%s | intros q s; destruct q, s; '
                                   'reflexivity].' % (m, m, m, m)))
            else:
                entries.append((s, 'apply (coversTr_nqh_at LDRZM_%s.tm_%s); '
                                   '[exact LDRZM_%s.nqhtr_%s | intros q s; destruct q, s; '
                                   'reflexivity].' % (m, m, m, m)))
        made.append(write_batch(a.tag, nn, req, entries,
                                'binary marker-run counters with a plain refill, re-anchored '
                                '(LE6 B2 rows), by LadderCheckRun2zTr with z = [0]'))
        nn += 1
    print('%d of %d rows boarded -> %d batch file(s): %s'
          % (len(kept), len(todo), len(made), ' '.join(os.path.relpath(x, REPO) for x in made)))


if __name__ == '__main__':
    main()
