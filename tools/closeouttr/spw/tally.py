#!/usr/bin/env python3
"""SPW tallies (UNTRUSTED bookkeeping): per burst-ratio group of the 605
wide SP rows, which route boarded each row and why the rest failed.

    python3 tools/closeouttr/spw/tally.py
"""
import json
import os
import re
from collections import Counter, defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, '..', '..', '..'))


def group(r):
    r = float(r)
    if abs(r - 2) < .05:
        return '2'
    if abs(r - 2.25) < .05:
        return '2.25'
    if abs(r - 4) < .2:
        return '4'
    if abs(r - 9) < .3:
        return '9'
    return 'other'


rows = [l.strip() for l in open(os.path.join(HERE, 'spw_rows.txt')) if l.strip()]
grp = {}
for l in open(os.path.join(REPO, 'tools/closeouttr/spb/residue_char.txt')):
    m = re.match(r'(\S+)\s+\S+ fires \d+\s+edge \d+\s+bursts \d+\s+ratio (\S+)\s+width (\d+)', l)
    if m:
        grp[m.group(1)] = group(m.group(2))
board = {}
for l in open(os.path.join(REPO, 'closeouttr_boarded.tsv')):
    p = l.split()
    if len(p) >= 2:
        board[p[0]] = p[1]
batch_route = {}
for f in os.listdir(os.path.join(REPO, 'theories/CloseoutTr')):
    if f.startswith('CBT_SPW_') and f.endswith('.v'):
        txt = open(os.path.join(REPO, 'theories/CloseoutTr', f)).read()
        batch_route[f[:-2]] = 'TriGlueTr' if 'TriGlueTr' in txt else 'irules'
ti = {}
p = os.path.join(HERE, 'ti_all.jsonl')
if os.path.exists(p):
    for l in open(p):
        d = json.loads(l)
        ti[d['spec']] = 'ok' if 'fams' in d else d.get('err', '?').split(' /')[0].split(' (')[0]
tab = defaultdict(Counter)
for r in rows:
    b = board.get(r)
    if b is None:
        k = 'open (TriGlue: %s)' % ti.get(r, 'not run')
    elif b.startswith('CBT_SPW_'):
        k = 'SPW ' + batch_route.get(b, '?')
    else:
        k = 'other session'
    tab[grp.get(r, '?')][k] += 1
keys = sorted(set(k for c in tab.values() for k in c))
gs = ['4', '2.25', '9', '2', 'other']
print('| outcome | ' + ' | '.join(gs) + ' | all |')
print('|---|' + '---:|' * (len(gs) + 1))
for k in keys:
    print('| %s | %s | %d |' % (k, ' | '.join(str(tab[g][k]) for g in gs),
                               sum(tab[g][k] for g in gs)))
print('| rows | %s | %d |' % (' | '.join(str(sum(tab[g].values())) for g in gs), len(rows)))
