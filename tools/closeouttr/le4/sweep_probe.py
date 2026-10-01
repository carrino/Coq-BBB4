#!/usr/bin/env python3
"""LE4 (UNTRUSTED measurement): is the interior arm of a `pos_detect.py`
family a SWEEP (SCOPING_INSTR 7.4.LE2, 7.4.LE4)?

    python3 sweep_probe.py CERTS.jsonl OUT.jsonl [--jobs 4]

For each digit d < top, the interior arm `t^0 d X -> (d+1) X` at r = 0 with
X opaque (`plain`), and with X = `t^m z Y` (Y opaque) for m = 0..4
(`sweep_m`), and with X = `t^m T` (both tails known) for m = 0..3 (`end_m`).
A row whose plain arm has no chain but whose `t^m z` arms all do is a carry
that walks across the run of top digits after the digit it increments."""
import argparse
import json
import os
import sys
from multiprocessing import Pool

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'ladder'))
import emit_ladder as E  # noqa: E402
import nest  # noqa: E402


def chain_ok(tab, el, er, c0, c1):
    ch = E.LC.derive_chain(tab, el, er, c0, c1, maxdepth=32, nmax=120, lift=True)
    if ch is None:
        return False
    got = E.LC.srun(tab, el, er, ch, c0)
    return got is not None and got[2] > 0 and (got[0] == c1 or nest.ceqL(el, er, got[0], c1))


def probe(c):
    f = c['family']
    spec = c['spec']
    tab = E.parse_tm(spec)
    digs = [tuple(d) for d in f['digits']]
    b = f['base']
    pre = tuple(f['near_head_prefix'])
    T = tuple(f['terminator'])
    q = ord(f['state']) - 65
    hs = f['head']
    left = f['side'] == 'L'
    OTHER = (tuple(f['other_side_cells']), (), 0, 0, ())

    def conf(cells):
        sd = (tuple(cells), (), 0, 0, ())
        return (q, sd, hs, OTHER) if left else (q, OTHER, hs, sd)
    el, er = (not left), left
    t, z = digs[b - 1], digs[0]
    out = []
    for d in range(b - 1):
        v = dict(d=d)
        a0, a1 = pre + digs[d], pre + digs[d + 1]
        v['plain'] = chain_ok(tab, el, er, conf(a0), conf(a1))
        v['sweep_m'] = [m for m in range(0, 5)
                        if chain_ok(tab, el, er, conf(a0 + t * m + z), conf(a1 + t * m + z))]
        v['end_m'] = [m for m in range(0, 4)
                      if chain_ok(tab, True, True, conf(a0 + t * m + T), conf(a1 + t * m + T))]
        out.append(v)
    if all(v['plain'] for v in out):
        verdict = 'plain'
    elif all(v['plain'] or len(v['sweep_m']) == 5 for v in out):
        verdict = 'sweep'
    else:
        verdict = 'other'
    return dict(spec=spec, verdict=verdict, digits=out)


def work(c):
    try:
        return probe(c)
    except Exception as e:  # noqa: BLE001
        return dict(spec=c['spec'], verdict='error %r' % e)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('certs')
    ap.add_argument('out')
    ap.add_argument('--jobs', type=int, default=4)
    a = ap.parse_args()
    done = set()
    if os.path.exists(a.out):
        done = set(json.loads(l)['spec'] for l in open(a.out))
    cs = [json.loads(l) for l in open(a.certs) if l.strip()]
    cs = [c for c in cs if c.get('closed') and c['spec'] not in done]
    with Pool(a.jobs) as pool, open(a.out, 'a') as fo:
        for r in pool.imap_unordered(work, cs):
            fo.write(json.dumps(r) + '\n')
            fo.flush()
            print(r['spec'], r['verdict'], flush=True)


if __name__ == '__main__':
    main()
