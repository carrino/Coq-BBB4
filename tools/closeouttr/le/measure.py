#!/usr/bin/env python3
"""LE: where each LE row stops (UNTRUSTED measurement, no proof weight).

    python3 tools/closeouttr/le/measure.py OUT.tsv VF.jsonl... [--rows F] [--coqc] [--jobs N]

For every row of the value-family finder's output (valfam.py --json, or
famclose.py) that is in the row list and still open: the finder's own verdict
if it did not close, else the emitter's (emit_ladder.py --tr, with --qh for a
class-QH row): 'built', or the NOT BUILT reason, and with --coqc whether the
board compiles.  One line per row: spec, class, stage, reason.
"""
import argparse
import json
import multiprocessing as mp
import os
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, '..', '..', '..'))
EMIT = os.path.join(REPO, 'tools', 'ladder', 'emit_ladder.py')


def mid(spec):
    return spec.replace('-', '_')


def classes():
    out = {}
    for l in open(os.path.join(REPO, 'closeouttr_classes.tsv')):
        if l.startswith('#'):
            continue
        f = l.rstrip('\n').split('\t')
        out[f[0]] = f[1]
    return out


def emit_one(args):
    cert, qh, coqc = args
    m = mid(cert['spec'])
    with tempfile.TemporaryDirectory() as tmp:
        j = os.path.join(tmp, m + '.json')
        json.dump(cert, open(j, 'w'))
        v = os.path.join(tmp, '%s_%s.v' % ('LDRQ' if qh else 'LDRT', m))
        try:
            r = subprocess.run([sys.executable, EMIT, '--tr'] + (['--qh'] if qh else [])
                               + [j, '-o', v], capture_output=True, text=True,
                               timeout=900)
        except subprocess.TimeoutExpired:
            return cert['spec'], 'emit', 'emit timeout'
        if r.returncode != 0 or not os.path.exists(v):
            return cert['spec'], 'emit', 'emit failed: ' + \
                (r.stderr.strip().splitlines() or ['?'])[-1][:150]
        txt = open(v).read()
        if 'Theorem %s_%s ' % ('qhtr' if qh else 'nqhtr', m) not in txt:
            why = [l for l in txt.splitlines() if 'NOT BUILT' in l]
            w = why[0].split('NOT BUILT for this row --')[-1].strip() if why else 'no closure'
            return cert['spec'], 'closure', w[:200]
        if not coqc:
            return cert['spec'], 'built', ''
        try:
            r = subprocess.run(['coqc', '-Q', os.path.join(REPO, 'theories'), 'BBB4', v],
                               capture_output=True, text=True, cwd=tmp, timeout=900)
        except subprocess.TimeoutExpired:
            return cert['spec'], 'coqc', 'coqc timeout'
        if r.returncode != 0:
            out = (r.stdout + r.stderr).strip().splitlines()
            return cert['spec'], 'coqc', ' | '.join(out[-3:])[:300]
        return cert['spec'], 'boarded', ''


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('out')
    ap.add_argument('found', nargs='+')
    ap.add_argument('--rows')
    ap.add_argument('--coqc', action='store_true')
    ap.add_argument('--jobs', type=int, default=2)
    a = ap.parse_args()
    cls = classes()
    rem = set(l.strip() for l in open(os.path.join(REPO, 'closeouttr_remaining.txt')))
    rows = set(l.strip() for l in open(a.rows)) if a.rows else rem
    rows &= rem
    best = {}
    for f in a.found:
        for line in open(f):
            if not line.strip():
                continue
            c = json.loads(line)
            s = c.get('spec')
            if s not in rows:
                continue
            if c.get('closed') or s not in best:
                best[s] = c
    todo, lines = [], []
    for s, c in sorted(best.items()):
        if c.get('closed'):
            todo.append((c, cls[s] == 'QH', a.coqc))
        else:
            why = c.get('reason') or ', '.join(map(str, c.get('famclose_tried') or []))
            lines.append((s, 'finder', str(why)[:120]))
    with mp.Pool(a.jobs) as p:
        for s, st, why in p.imap_unordered(emit_one, todo):
            lines.append((s, st, why))
            print(s, st, why, flush=True)
    with open(a.out, 'w') as o:
        for s, st, why in sorted(lines):
            o.write('%s\t%s\t%s\t%s\n' % (s, cls[s], st, why))


if __name__ == '__main__':
    main()
