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
    # report how far the BEST candidate family got, not the first
    if 'overflow leaves the family' in reasons:
        return 'overflow-leaves-family'
    if 'coverage not stable at kmax+2' in reasons:
        return 'coverage-unstable'
    if 'no boot into the family' in reasons:
        return 'no-boot'
    if 'family not covered' not in reasons and \
            'no arm replayed to anchor' in reasons:
        return 'arm-replay-failed'
    if 'family not covered' in reasons:
        if all(t.get('coverage', {}).get('n_wrong') for t in tried
               if t.get('reason') == 'family not covered'):
            return 'arm-lands-off-family'
        return 'interior-not-covered'
    return 'other'


NEAR = 'counter signal, odometer model does not fit'


def probe_note(r):
    """Near-miss reading for rows where no family was accepted."""
    pr = r.get('family_probe') or []
    if not pr:
        return ''
    b = pr[0]
    if b.get('no_reading'):
        g = b.get('far_side_groups') or [{}]
        return ('no reading; largest constant-far-side group %s of %s visits '
                'at %s/%s' % (g[0].get('max_constant_far_side_group'),
                              g[0].get('visits'), g[0].get('anchor'),
                              g[0].get('side')))
    return ('best %s/%s l=%d base=%d: +1 on %.0f%% of %d visits %s'
            % (b['anchor'], b['side'], b['digit_len'], b['base'],
               100 * b['plus1_frac'], b['visits'], b['top_deltas'][:2]))


def subbucket(r):
    """Split no-counter-shape by how close the near-miss probe came."""
    if bucket(r) != 'no-counter-shape':
        return bucket(r)
    pr = r.get('family_probe') or []
    if not pr:
        return 'no-counter-shape/no-probe'
    if pr[0].get('no_reading'):
        g = (pr[0].get('far_side_groups') or [{}])[0]
        if (g.get('max_constant_far_side_group') or 0) < 6:
            return 'no-counter-shape/far-side-varies'
        return 'no-counter-shape/no-reading'
    f = pr[0]['plus1_frac']
    if f >= 0.9:
        return 'no-counter-shape/chain-broken'
    if f >= 0.5:
        return 'no-counter-shape/partial-+1'
    return 'no-counter-shape/no-signal'


def table(path, out):
    rows = [json.loads(l) for l in open(path) if l.strip()]
    with open(out, 'w') as f:
        f.write('%-30s %-26s %5s %5s %5s %6s %s\n'
                % ('spec', 'verdict', 'rules', 'arms', 'live', 'wall',
                   'note'))
        for r in sorted(rows, key=lambda r: (not r.get('closed'), r['spec'])):
            liv = r.get('liveness', {}).get('states_infinitely_often', '')
            note = ''
            if r.get('closed'):
                note = ('boot@%s base=%d digits=%s cover=%s stable_k=%s '
                        'diff=%s steps=%s laps=%s'
                        % (r['boot']['steps_from_blank'],
                           r['family']['base'],
                           '/'.join(''.join(map(str, d))
                                    for d in r['family']['digits']),
                           r['coverage']['strings'],
                           r['coverage'].get('stable_to_kmax'),
                           r.get('differential_ok'),
                           r.get('differential_steps_ok'),
                           r.get('chain_check', {}).get('laps_confirmed')))
            else:
                note = probe_note(r) or (r.get('reason') or '')[:70]
            f.write('%-30s %-26s %5s %5s %5s %6s %s\n'
                    % (r['spec'], subbucket(r), r.get('n_rules', ''),
                       len(r.get('arms', [])) or '', liv,
                       r.get('wall', ''), note))
    return rows


def summarize(path):
    rows = [json.loads(l) for l in open(path) if l.strip()]
    c = Counter(subbucket(r) for r in rows)
    print('rows: %d' % len(rows))
    for k, n in c.most_common():
        print('  %-34s %4d' % (k, n))
    cl = [r for r in rows if r.get('closed')]
    if cl:
        print('closed: never-QH (all states i.o.) %d/%d, differential ok %d, '
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
    ap.add_argument('--table')
    ap.add_argument('--steps', type=int, default=20000)
    ap.add_argument('--cap', type=float, default=240.0)
    ap.add_argument('--kmax', type=int, default=7)
    ap.add_argument('--jobs', type=int, default=3)
    a = ap.parse_args()
    if a.summary:
        summarize(a.summary)
        if a.table:
            table(a.summary, a.table)
            print('table -> %s' % a.table)
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
