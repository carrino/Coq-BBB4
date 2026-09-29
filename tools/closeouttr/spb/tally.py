#!/usr/bin/env python3
"""SPB yield tally (UNTRUSTED bookkeeping): the lap route by port, the probe's
failure buckets, and the ladder route's outcomes.

    python3 tools/closeouttr/spb/tally.py
"""
import collections
import glob
import json
import os
import subprocess

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.join(HERE, '..', '..', '..')
os.chdir(HERE)

# the 18 alphabets CE inferred (commit 21f9cda); every other Alph_* predates CE
ce_alph = set()
out = subprocess.run(['git', 'show', '--stat', '--format=', '21f9cda'],
                     capture_output=True, text=True, cwd=REPO).stdout
for l in out.splitlines():
    if 'Alph_' in l:
        ce_alph.add('Alph_' + l.split('Alph_')[1].split('.v')[0])

probe = {}
for l in open('probe.jsonl'):
    r = json.loads(l)
    probe[r['spec']] = r
lap = {}
for f in sorted(glob.glob('lap_c*.json')):
    for r in json.load(open(f)):
        lap[r['spec']] = r
boarded = set()
for l in open(os.path.join(REPO, 'closeouttr_boarded.tsv')):
    p = l.rstrip('\n').split('\t')
    # spec<TAB>batch (older rows carry a leading index column)
    if len(p) >= 2 and p[-1].startswith('CBT_SPB_'):
        boarded.add(p[-2])


def route(s):
    t = [x for x in probe[s]['tries'] if x[3] == 'OK']
    return t[0][4] if t else '?'


def best(r):
    """the most advanced failure over every anchor tried"""
    w = [x[3] for x in r['tries']]
    if not w:
        return 'no anchor'
    for key in ('render', 'nested', 'no overflow chain', 'no interior chain',
                'no visit', 'timeout'):
        for x in w:
            if key in x:
                return x[:70]
    return w[-1][:70]


ok = [r for r in lap.values() if r['ok']]
print('probe: %d rows, %d derive' % (len(probe), sum(r['ok'] for r in probe.values())))
print('emit: %d rows, %d derive+compile, %d boarded as SPB' %
      (len(lap), len(ok), len([r for r in ok if r['spec'] in boarded])))
C = collections.Counter()
alph = collections.Counter()
enc = collections.Counter()
for r in ok:
    rt = route(r['spec'])
    a = r['enc'].split('/')[0]
    kind = ('parity split' if 'par' in rt else
            'CE-inferred alphabet' if a in ce_alph else 'pre-CE alphabet')
    C[(kind, 'nested' if 'nest' in rt else 'flat')] += 1
    alph[a] += 1
    enc['mirror' if '/mirror' in r['enc'] else 'direct'] += 1
    enc['S1 head' if '/S1' in r['enc'] else 'S0 head'] += 1
print('\nlap boards by port:')
for k, v in sorted(C.items(), key=lambda kv: -kv[1]):
    print('  %-22s %-7s %4d' % (k[0], k[1], v))
print('alphabets:', alph.most_common(15))
print('anchors:', dict(enc))
print('routes:', collections.Counter(route(r['spec']) for r in ok).most_common(12))
print('emit misses:', collections.Counter(r['why'][:70] for r in lap.values() if not r['ok']))

fails = [r for r in probe.values() if not r['ok']]
print('\nprobe failures (%d), best blocker:' % len(fails))
for k, v in collections.Counter(best(r) for r in fails).most_common(20):
    print('  %4d  %s' % (v, k))

vf = {}
for f in ['vf.jsonl'] + sorted(glob.glob('vf_s*.jsonl')):
    if os.path.exists(f):
        for l in open(f):
            if l.strip():
                r = json.loads(l)
                vf[r['spec']] = r
if vf:
    cl = [r for r in vf.values() if r['closed']]
    print('\nladder: %d rows tried, %d close, %d boarded as SPB' %
          (len(vf), len(cl), len([r for r in cl if r['spec'] in boarded])))
    print('  not closed:', collections.Counter((r.get('reason') or '')[:50]
                                              for r in vf.values() if not r['closed']).most_common(8))
