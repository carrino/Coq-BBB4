#!/usr/bin/env python3
"""Run an emitter over certificates in parallel and record where each stops
(UNTRUSTED; SCOPING_INSTR 7.4.LE4).  `--nonest` runs emit_ladder with
its nested-program search off, the fast first pass.  Boards whose closure is built are left
in OUTDIR for a batch script to compile; nothing is compiled here.

    python3 try_emit.py CERTS.jsonl OUTDIR RESULT.tsv [--emitter ladder|zeck2] [--jobs 4]
"""
import argparse
import json
import os
import subprocess
import sys
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, '..', '..', '..'))
EMIT = {'ladder': (os.path.join(REPO, 'tools', 'ladder', 'emit_ladder.py'), ['--tr'], 'LDRT', 'LDRQ'),
        'zeck2': (os.path.join(HERE, 'emit_zeck2.py'), [], 'LDRZ2', 'LDRZ2Q')}
# emit_ladder with its nested-program search off: the fast first pass
NONEST = os.path.join(HERE, 'emit_ladder_nonest.py')
QHC = set(l.split('\t')[0] for l in open(os.path.join(REPO, 'closeouttr_classes.tsv'))
          if l.split('\t')[1:2] == ['QH'])


def one(a):
    cert, outdir, kind, timeout, nonest = a
    spec = cert['spec']
    m = spec.replace('-', '_')
    qh = spec in QHC
    exe, flags, p, pq = EMIT[kind]
    j = os.path.join(outdir, m + '.json')
    json.dump(cert, open(j, 'w'))
    v = os.path.join(outdir, '%s_%s.v' % (pq if qh else p, m))
    try:
        env = dict(os.environ, LE4_NONEST='1') if nonest else None
        subprocess.run([sys.executable, NONEST if nonest else exe] + flags
                       + (['--qh'] if qh else []) + [j, '-o', v],
                       capture_output=True, text=True, timeout=timeout,
                       cwd=os.path.dirname(exe), env=env)
    except subprocess.TimeoutExpired:
        return spec, 'timeout', ''
    if not os.path.exists(v):
        return spec, 'emit-failed', ''
    txt = open(v).read()
    if 'Theorem %s_%s ' % ('qhtr' if qh else 'nqhtr', m) in txt:
        return spec, 'BUILT', v
    why = [l for l in txt.splitlines() if 'NOT BUILT' in l]
    return spec, 'no-closure', (why[0].split('--', 1)[-1].strip() if why else '?')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('certs')
    ap.add_argument('outdir')
    ap.add_argument('result')
    ap.add_argument('--emitter', default='ladder', choices=sorted(EMIT))
    ap.add_argument('--jobs', type=int, default=4)
    ap.add_argument('--timeout', type=int, default=900)
    ap.add_argument('--nonest', action='store_true',
                    help='emit_ladder only: no nested programs (fast first pass)')
    a = ap.parse_args()
    os.makedirs(a.outdir, exist_ok=True)
    done = set()
    if os.path.exists(a.result):
        done = set(l.split('\t')[0] for l in open(a.result))
    certs = [json.loads(l) for l in open(a.certs) if l.strip()]
    todo = [(c, a.outdir, a.emitter, a.timeout, a.nonest) for c in certs
            if c.get('closed') and c['spec'] not in done]
    with Pool(a.jobs) as pool, open(a.result, 'a') as fo:
        for spec, st, why in pool.imap_unordered(one, todo):
            fo.write('%s\t%s\t%s\n' % (spec, st, why))
            fo.flush()
            print(spec, st, why[:150], flush=True)


if __name__ == '__main__':
    main()
