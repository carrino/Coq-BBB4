#!/usr/bin/env python3
"""UNTRUSTED sweep driver: run valfam.close over a row list with a HARD
per-machine wall-clock cap (subprocess kill, not a cooperative deadline) and
append one JSON object per row to a JSONL file.

Usage: sweep.py --list rows.txt --out results.jsonl [--cap 240] [--jobs 3]
       sweep.py --summary results.jsonl
"""

import argparse
import json
import os
import subprocess
import sys
import tempfile
import time
from collections import Counter
from concurrent.futures import ThreadPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))


def run_one(spec, steps, cap, kmax):
    fd, path = tempfile.mkstemp(suffix='.jsonl')
    os.close(fd)
    t0 = time.time()
    try:
        subprocess.run(
            [sys.executable, os.path.join(HERE, 'valfam.py'), '--spec', spec,
             '--steps', str(steps), '--cap', str(cap), '--kmax', str(kmax),
             '--json', path],
            cwd=HERE, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE,
            timeout=cap + 120)
        with open(path) as f:
            line = f.readline()
        r = json.loads(line) if line.strip() else {
            'spec': spec, 'closed': False, 'reason': 'no output'}
    except subprocess.TimeoutExpired:
        r = {'spec': spec, 'closed': False, 'reason': 'hard timeout'}
    except Exception as e:                                # noqa: BLE001
        r = {'spec': spec, 'closed': False,
             'reason': 'crash: %s' % type(e).__name__, 'detail': str(e)[:200]}
    finally:
        os.unlink(path)
    r['wall'] = round(time.time() - t0, 1)
    return r


def bucket(r):
    """Failure taxonomy, coarse-to-fine."""
    if r.get('closed'):
        return 'closed'
    why = r.get('reason') or ''
    if 'halt' in why and 'timeout' not in why:
        return 'halts'
    if 'timeout' in why or 'time cap' in why:
        return 'timeout'
    if why.startswith('crash'):
        return 'crash'
    if 'no local rules' in why or 'differential validation' in why:
        return 'no-ladder'
    if 'no value family' in why:
        return 'no-counter-shape'
    tried = r.get('tried') or []
    reasons = {t.get('reason') for t in tried}
    if 'no arm replayed to anchor' in reasons:
        return 'arm-replay-failed'
    if 'no boot into the family' in reasons:
        return 'no-boot'
    if 'coverage not stable at kmax+2' in reasons:
        return 'coverage-unstable'
    if 'overflow leaves the family' in reasons:
        return 'overflow-leaves-family'
    if 'family not covered' in reasons:
        if all(t.get('coverage', {}).get('n_wrong') for t in tried
               if t.get('reason') == 'family not covered'):
            return 'arm-lands-off-family'
        return 'interior-not-covered'
    return 'other'


def summarize(path):
    rows = [json.loads(l) for l in open(path) if l.strip()]
    c = Counter(bucket(r) for r in rows)
    print('rows: %d' % len(rows))
    for k, n in c.most_common():
        print('  %-22s %4d' % (k, n))
    cl = [r for r in rows if r.get('closed')]
    if cl:
        print('closed: liveness all-states %d/%d, differential ok %d, '
              'exact step counts %d'
              % (sum(1 for r in cl if r['liveness']['all_states']), len(cl),
                 sum(1 for r in cl if r.get('differential_ok')),
                 sum(1 for r in cl if r.get('differential_steps_ok'))))
        print('closed: median arms %d, median wall %.0fs'
              % (sorted(len(r['arms']) for r in cl)[len(cl) // 2],
                 sorted(r.get('wall', 0) for r in cl)[len(cl) // 2]))
    w = sorted((r.get('wall', 0) for r in rows), reverse=True)
    if w:
        print('wall: total %.0fs  max %.0fs  median %.0fs'
              % (sum(w), w[0], w[len(w) // 2]))
    return rows


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--list')
    ap.add_argument('--out')
    ap.add_argument('--summary')
    ap.add_argument('--steps', type=int, default=20000)
    ap.add_argument('--cap', type=float, default=240.0)
    ap.add_argument('--kmax', type=int, default=7)
    ap.add_argument('--jobs', type=int, default=3)
    a = ap.parse_args()
    if a.summary:
        summarize(a.summary)
        return
    specs = [l.split()[0] for l in open(a.list) if l.strip()]
    done = set()
    if os.path.exists(a.out):
        for l in open(a.out):
            if l.strip():
                done.add(json.loads(l)['spec'])
        specs = [s for s in specs if s not in done]
        print('resuming: %d already done, %d to go' % (len(done), len(specs)))
    t0 = time.time()
    with open(a.out, 'a') as f, ThreadPoolExecutor(a.jobs) as ex:
        futs = [ex.submit(run_one, s, a.steps, a.cap, a.kmax) for s in specs]
        for i, fu in enumerate(futs):
            r = fu.result()
            f.write(json.dumps(r) + '\n')
            f.flush()
            print('[%3d/%3d %5.0fs] %-30s %-18s %ss'
                  % (i + 1, len(specs), time.time() - t0, r['spec'],
                     bucket(r), r.get('wall')))
            sys.stdout.flush()


if __name__ == '__main__':
    main()
