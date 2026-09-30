#!/usr/bin/env python3
"""Convert TriGlue certificates (ti_batch.find, DN mode) to ListGlue certificates
with empty tails and replay them through lg_batch.c_check: the end-to-end
validation of the lg renderer / replica / lg_sound (SCOPING_INSTR.md §7.4.BLC).
UNTRUSTED.

    python3 tools/closeouttr/blc/ti2lg.py OUT.jsonl SPEC...
"""
import os
import sys, json
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import ti_batch as T, lg_batch as G
out = []
for spec in sys.argv[2:]:
    r = T.find(spec, 120, 'DN', 0)
    if 'err' in r:
        print(spec, 'TI fail', r['err'][:100]); continue
    fams = []
    for F in r['fams']:
        tree, ut = [], []
        for nd in F['tree']:
            if nd[0] == 'leaf':
                tree.append(('leaf', len(ut))); ut.append(('uleaf', nd[1]))
            else:
                tree.append(nd)
        fams.append(dict(q=F['q'], h=F['h'], L=F['L'], R=F['R'], n=F['n'], tree=tree, utree=ut, tL=None, tR=None))
    leaves = [dict(f=lf['f'], reg=[tuple(x) for x in lf['reg']], g=lf['g'], tgt=lf['tgt'], c0=lf['c0'], j=lf['j'],
                   el=lf['el'], er=lf['er'], nL=lf['nL'], nR=lf['nR'], chain=lf['chain'], fL=[], fR=[], uL=[], uR=[])
              for lf in r['leaves']]
    ranks = [(t, [dict(V=(v[0], list(v[1])), bL=0, bR=0) for v in V]) for t, V in r['ranks']]
    c = dict(pins=sorted(r['pins']), kinds=[], trans=[], acc=[], mins=[], fams=fams, leaves=leaves, P=r['P'],
             S=[(l, list(rho)) for l, rho in r['S']], ranks=ranks, t0=r['t0'], a0=dict(f=r['f0'], v=r['v0'], L=[], R=[]),
             mir=r['mir'], spec=spec)
    tab = T.parse(spec)
    if c['mir']: tab = T.mirror(tab)
    err = G.c_check(c, tab)
    print(spec, 'replica', err)
    if not err: out.append(c)
with open(sys.argv[1], 'w') as f:
    for c in out: f.write(json.dumps(G.jsonable(c)) + '\n')
