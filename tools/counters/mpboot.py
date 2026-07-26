#!/usr/bin/env python3
"""Decisive test for the Mp class: with the TAPE-DERIVED terminator
C=[S0;S1;S1] (A,B unchanged from Mp), is the boot to the first inner anchor
AFFINE?  If yes, the 'exponential boot' was purely innerfam's key
fragmentation and the class joins the nested-lap population."""
import sys, os
sys.path.insert(0, '/home/user/Coq-BBB4/tools/counters')
os.chdir('/home/user/Coq-BBB4')
import emit_lapcert as EL, innerfam as IF, lapcert as LC
from emit_interleave import parse
from mirror_common import mirror_spec
LAB = 'ABCD'
A, B, C = (0,1), (1,1), (0,1,1)

def decode(w):
    w, bits = tuple(w), []
    for _ in range(64):
        if w == C:
            v = 1
            for b in reversed(bits): v = 2*v + b
            return v
        if w[:2] == A: bits.append(0); w = w[2:]
        elif w[:2] == B: bits.append(1); w = w[2:]
        else: return None
    return None

def first_anchor(tab, start, want, maxT=3000000):
    cfg = start
    for t in range(1, maxT):
        cfg = LC.wstep(tab, False, False, cfg)
        q, l, h, r = cfg
        if q == want[0] and h == want[2] and LC.rstrip0(l) == LC.rstrip0(want[1]) \
           and LC.rstrip0(r) == LC.rstrip0(want[3]): return None, None, None
        if h != 0: continue
        v = decode(LC.rstrip0(l))
        if v is not None and v >= 2: return t, v, LAB[q]
    return None, None, None

def deg(ys):
    if any(y is None for y in ys) or len(ys) < 3: return '?'
    d = [ys[i+1]-ys[i] for i in range(len(ys)-1)]
    if len(set(d)) == 1: return 'AFFINE(+%d)' % d[0]
    r = [ys[i+1]/ys[i] for i in range(len(ys)-1) if ys[i]]
    return 'EXP(~%.2f)' % (sum(r)/len(r)) if r and sum(r)/len(r) > 1.5 else 'OTHER'

for spec0 in [l.split()[0] for l in open(sys.argv[1])][:10]:
    for spec in (spec0, mirror_spec(spec0)):
        r = IF.phase_probe(spec, K=5)
        if r and r['inner']: break
    else:
        print('%-40s --' % spec0); continue
    tab = parse(spec); st_out = LAB.index(r['st0']); encf = EL.ENC[r['enc']]
    to_, fo = tuple(r['tail']), tuple(r['far'])
    ts, vs, qs = [], [], []
    for K in (4,5,6,7):
        s = (st_out, tuple(encf(2**K-1)) + to_, 0, fo)
        w = (st_out, tuple(encf(2**K)) + to_, 0, fo)
        t, v, q = first_anchor(tab, s, w)
        ts.append(t); vs.append(v); qs.append(q)
    print('%-40s first-anchor t=%s v=%s st=%s  -> %s'
          % (spec0, ts, vs, qs[0], deg(ts)), flush=True)
