#!/usr/bin/env python3
"""Dump the TriGlue family graph of rows whose rankings fail (UNTRUSTED).

    python3 tools/closeouttr/ta/dump.py ROWS.txt OUT.jsonl [--jobs 4] [--timeout 300]

For each row, run the TriGlue finders in turn (ti_batch at its defaults,
the lattice finder bl_ti, the anchor-seeded hy3_ti) and keep the first
family set that CLOSES, i.e. whose only failure is the ranking.  The
record is the certificate without P/S/ranks (families, leaves, boot) plus
the instructions each leaf fires: the exact piecewise-affine round map
that §7.4.TA studies.  A row the finders certify outright is recorded as
'ok' (a ranking exists).
"""
import argparse
import json
import os
import signal
import sys
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
import ti_batch as T                            # noqa: E402
import ti_coq as C                              # noqa: E402

STASH = []
_orig_live = T.live_search


def _live(cert, tabw, fired, P):
    if P == T.PLIST[0]:
        STASH.append(dict(cert=json.loads(json.dumps(T.jsonable(cert))),
                          fired=[sorted(f) for f in fired]))
    return _orig_live(cert, tabw, fired, P)


T.live_search = _live


class Timeout(Exception):
    pass


def _alarm(signum, frame):
    raise Timeout()


def run(spec, finder, timeout):
    signal.signal(signal.SIGALRM, _alarm)
    signal.alarm(timeout)
    try:
        if finder == 'ti':
            cls = T.classes().get(spec, ('DN', 0))
            r = T.find(spec, 0, *cls)
        elif finder == 'bl':
            import bl_ti as B
            B.install()
            cls = T.classes().get(spec, ('DN', 0))
            r = T.find(spec, 0, *cls)
        else:
            import hy3_ti as H
            r = H.find_dir(T.parse(spec))
    except Timeout:
        r = dict(err='timeout')
    finally:
        signal.alarm(0)
    return r


def one(args):
    spec, finder, timeout = args
    r = run(spec, finder, timeout)
    out = dict(spec=spec, finder=finder)
    if 'err' not in r:
        out['verdict'] = 'ok'
        out['P'] = r.get('P')
        return out
    out['verdict'] = 'norank' if 'norank' in r['err'] else 'fail'
    out['err'] = r['err'][:300]
    if out['verdict'] == 'norank' and STASH:
        out.update(STASH[-1])
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('rows')
    ap.add_argument('out')
    ap.add_argument('--jobs', type=int, default=4)
    ap.add_argument('--timeout', type=int, default=300)
    ap.add_argument('--finders', default='ti,bl,hy3')
    a = ap.parse_args()
    specs = [l.split()[0] for l in open(a.rows) if l.strip() and not l.startswith('#')]
    done = {}
    if os.path.exists(a.out):
        for l in open(a.out):
            d = json.loads(l)
            done.setdefault(d['spec'], []).append(d)
    with open(a.out, 'a') as f:
        for finder in a.finders.split(','):
            todo = [(s, finder, a.timeout) for s in specs
                    if not any(d['verdict'] in ('norank', 'ok') for d in done.get(s, []))
                    and not any(d['finder'] == finder for d in done.get(s, []))]
            with Pool(a.jobs, maxtasksperchild=1) as pool:
                for r in pool.imap_unordered(one, todo):
                    f.write(json.dumps(r) + '\n')
                    f.flush()
                    done.setdefault(r['spec'], []).append(r)
            print(finder, sum(1 for s in specs
                              if any(d['verdict'] == 'norank' for d in done.get(s, []))),
                  'norank so far', flush=True)


if __name__ == '__main__':
    main()
