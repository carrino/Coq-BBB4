#!/usr/bin/env python3
"""The SPW 40-row sample (UNTRUSTED bookkeeping): per row, bin/irules at
2M / 10M / 50M steps (status, --why failure stage, wall seconds), the kernel
probe of each certificate, and the TriGlue finder's verdict.

    python3 tools/closeouttr/spw/sample_table.py > tools/closeouttr/spw/sample_table.tsv
"""
import json
import os
from collections import Counter

HERE = os.path.dirname(os.path.abspath(__file__))


def irules(budget, m):
    p = os.path.join(HERE, 's%s' % budget, 'res', m)
    if not os.path.exists(p):
        return 'running', '', ''
    f = open(p).read().strip().split(',')
    st, wall = f[1], f[-1].split('=')[1]
    why = f[10].split()[0] if st == 'undecided' and len(f) > 11 else ''
    return st, why, wall


def probes(budget):
    p = os.path.join(HERE, 's%s' % budget, 'probe.tsv')
    out = {}
    if os.path.exists(p):
        for l in open(p):
            q = l.rstrip('\n').split('\t')
            out[q[0]] = q[2] + ('/' + q[4] if len(q) > 4 else '')
    return out


ti = {}
for f in ('ti_sample.jsonl', 'ti_all.jsonl'):
    for l in open(os.path.join(HERE, f)):
        d = json.loads(l)
        ti.setdefault(d['spec'], 'ok' if 'fams' in d else
                      d.get('err', '?').split(' /')[0].split(' (')[0])
grp = {}
for l in open(os.path.join(HERE, 'sample40_char.txt')):
    g, rest = l.split('\t')
    grp[rest.split()[0]] = g
pr = {b: probes(b) for b in ('2M', '10M', '50M')}
cols = ['spec', 'ratio']
for b in ('2M', '10M', '50M'):
    cols += ['irules_' + b, 'why_' + b, 'wall_' + b, 'probe_' + b]
cols += ['triglue']
print('\t'.join(cols))
tally = Counter()
for m in (l.strip() for l in open(os.path.join(HERE, 'sample40.txt'))):
    row = [m, grp[m]]
    for b in ('2M', '10M', '50M'):
        st, why, wall = irules(b, m)
        row += [st, why, wall, pr[b].get(m, '')]
        tally[(b, st)] += 1
    row.append(ti.get(m, ''))
    print('\t'.join(row))
