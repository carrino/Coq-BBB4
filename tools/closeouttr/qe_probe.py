#!/usr/bin/env python3
"""Bucket quasihalting counter rows by the lap emitter's failure reason
(UNTRUSTED diagnostic, no Coq).

    python3 tools/closeouttr/qe_probe.py ROWS.txt OUT.jsonl [--jobs 4] [--timeout 300] [--tr]

--tr probes the never-quasihalting side instead (emit_lapcert.py --tr, the
LapGlueTr boards: the DN log counters of SCOPING_INSTR 7.4.DX/7.4.CE).

emit_lapcert.py --qh reports only the LAST anchor's failure, and the last
anchor tried is the mirrored S1-head one, so its "no overflow chain (nested
route is S0-only)" line says little about why the S0 anchors failed.  This
runs the same search (both orientations, both head symbols, every anchor
family) and records every attempt: the derive's reason, or for a derived
certificate the --qh renderer's reason.  One JSON line per row:
{spec, ok, secs, tries: [[tag, edge, enc, why-or-"OK"(, route)], ...]}
(route: the derived certificate's flags -- trmiss, nest-*, peel, islack,
oslack -- or flat).
Resumable: rows already in OUT are skipped.
"""
import argparse
import json
import multiprocessing as mp
import os
import signal
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'counters'))


class Timeout(Exception):
    pass


def _alarm(*_):
    raise Timeout()


def probe(args):
    spec, tmo, qh = args
    import emit_lapcert as E
    from mirror_common import mirror_spec
    E.TR_MODE = True
    E.QH_MODE = qh
    t0 = time.time()
    tries, ok = [], False
    signal.signal(signal.SIGALRM, _alarm)
    signal.alarm(tmo)
    try:
        for mirrored in (False, True):
            dspec = mirror_spec(spec) if mirrored else spec
            for hd in (0, 1):
                E.HD = hd
                for (edge, tail, p0, enc, far) in E.anchors(dspec, hd):
                    tag = ('M' if mirrored else '') + ('S1' if hd else 'S0')
                    try:
                        D = E.derive(dspec, edge, tail, p0, enc, far)
                    except Timeout:
                        raise
                    except Exception as e:                    # noqa: BLE001
                        tries.append([tag, edge, enc, 'derive: %s' % e])
                        continue
                    try:
                        E.render_tr(D, spec, dspec, mirrored)
                    except Timeout:
                        raise
                    except Exception as e:                    # noqa: BLE001
                        tries.append([tag, edge, enc, 'render: %s' % e])
                        continue
                    N = D.get('nest') or {}
                    route = ','.join(f for f, on in (
                        ('trmiss', D.get('trmiss')),
                        ('par%d' % (D.get('par') or {}).get('M', 0), D.get('par')),
                        ('opar%d' % (D.get('opar') or {}).get('M', 0), D.get('opar')),
                        ('nest-' + str(N.get('route', 'plain')), N),
                        ('peel', D.get('opeel')), ('islack', D.get('islack')),
                        ('oslack', D.get('oslack'))) if on) or 'flat'
                    tries.append([tag, edge, enc, 'OK', route])
                    ok = True
                    raise StopIteration
    except StopIteration:
        pass
    except Timeout:
        tries.append(['-', '-', '-', 'timeout'])
    finally:
        signal.alarm(0)
        E.HD = 0
    return dict(spec=spec, ok=ok, secs=round(time.time() - t0, 1), tries=tries)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('rows')
    ap.add_argument('out')
    ap.add_argument('--jobs', type=int, default=4)
    ap.add_argument('--timeout', type=int, default=300)
    ap.add_argument('--tr', action='store_true',
                    help='never-QH side (LapGlueTr) instead of --qh')
    a = ap.parse_args()
    done = set()
    if os.path.exists(a.out):
        done = set(json.loads(l)['spec'] for l in open(a.out) if l.strip())
    specs = [l.split()[0] for l in open(a.rows) if l.strip() and l.split()[0] not in done]
    with mp.Pool(a.jobs, maxtasksperchild=20) as pool, open(a.out, 'a') as out:
        for i, r in enumerate(pool.imap_unordered(probe, [(s, a.timeout, not a.tr) for s in specs])):
            out.write(json.dumps(r) + '\n')
            out.flush()
            print('%5d/%d %s %s %.0fs' % (i + 1, len(specs), r['spec'],
                  'OK' if r['ok'] else (r['tries'][-1][3][:70] if r['tries'] else 'no anchor'),
                  r['secs']), flush=True)


if __name__ == '__main__':
    main()
