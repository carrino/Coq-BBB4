#!/usr/bin/env python3
"""LE6: the survey table -- group the target rows by the growth events
(survey2.jsonl from events.py) and report the readings / boards per group.

    python3 tools/closeouttr/le6/survey_table.py [--rows ROWS] [--md]
"""
import json, os, statistics as S, sys
from collections import Counter, defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, '..', '..', '..'))


def load(fn):
    p = os.path.join(HERE, fn)
    return {json.loads(l)['spec']: json.loads(l) for l in open(p)} if os.path.exists(p) else {}


def group(d):
    ev = d.get('ev', {})
    if not ev:
        return 'no growth events (bounded / irregular extent)'
    meds = {s: S.median(e['rat'][-6:]) for s, e in ev.items()}
    reg = {s: (max(e['rat'][-6:]) - min(e['rat'][-6:])) < 0.1 * meds[s] for s, e in ev.items()}
    sides = ''.join(sorted(ev))
    def near(x, y, tol=0.04):
        return abs(x - y) < tol * y
    if any(near(m, 1.618) or near(m, 2.618) for m in meds.values()) and all(reg.values()):
        return 'F: Fibonacci growth (phi per cell / phi^2 per 2 cells)'
    if all(reg.values()) and all(near(m, 2.0) for m in meds.values()):
        return 'B2: binary growth, %s' % ('both ends' if sides == 'LR' else 'one end')
    if all(reg.values()) and all(near(m, 3.0) or near(m, 4.0) or near(m, 2.0) for m in meds.values()):
        return 'B3: base 3 / 4 growth (or 2 and 4 at the two ends)'
    if all(reg.values()):
        return 'R: other constant ratio (%s)' % '/'.join('%.2f' % m for m in sorted(meds.values()))
    return 'I: irregular event ratios (a second level: the ratio cycles with an outer count)'


def main():
    a = sys.argv[1:]
    rows = open(a[a.index('--rows') + 1] if '--rows' in a else os.path.join(HERE, 'rows.txt')).read().split()
    sv = load('survey2.jsonl')
    boarded = {}
    for l in open(os.path.join(REPO, 'closeouttr_boarded.tsv')):
        f = l.split()
        if len(f) >= 2 and f[1].startswith('CBT_LE6'):
            boarded[f[0]] = f[1]
    zeck2 = {s for s, d in load('zeck2.jsonl').items() if d.get('closed')}
    zw = load('zeckw.jsonl')
    G = defaultdict(list)
    for r in rows:
        G[group(sv[r]) if r in sv else 'C: conjugate of a boarded row (boarded before the survey)'].append(r)
    out = []
    for g, rs in sorted(G.items(), key=lambda kv: -len(kv[1])):
        rd = Counter()
        for r in rs:
            if r in zeck2:
                rd['zeck2'] += 1
            elif zw.get(r, {}).get('closed'):
                rd['countdown %s' % tuple(zw[r]['mode'])[1]] += 1
        b = sum(1 for r in rs if r in boarded)
        out.append((g, len(rs), dict(rd), b))
    if '--md' in a:
        print('| group | rows | read | boarded |')
        print('|---|---:|---|---:|')
        for g, n, rd, b in out:
            print('| %s | %d | %s | %d |' % (g, n, ', '.join('%s %d' % kv for kv in sorted(rd.items())) or '-', b))
    else:
        for x in out:
            print(x)


if __name__ == '__main__':
    main()
