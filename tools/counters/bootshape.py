#!/usr/bin/env python3
"""Is the BOOT (outer all-ones anchor -> inner anchor at 2^j) AFFINE in j?
If it is, a failing boot is a search gap.  If it is not, the nested-lap design
needs a third level and Stage C is not just an emitter."""
import sys, os
sys.path.insert(0, '/home/user/Coq-BBB4/tools/counters')
os.chdir('/home/user/Coq-BBB4')
import emit_lapcert as EL, innerfam as IF, lapcert as LC
from emit_interleave import parse
from mirror_common import mirror_spec
LAB = 'ABCD'

def boot_len(tab, st_out, encf, to_, fo, st_in, encfi, ti, fi, K, maxT=4000000):
    p = 2**K - 1
    cfg = (st_out, tuple(encf(p)) + to_, 0, fo)
    vw = tuple(encfi(2**(K-1))) + ti
    for t in range(1, maxT):
        cfg = LC.wstep(tab, False, False, cfg)
        q, l, h, r = cfg
        if q == st_in and h == 0 and LC.rstrip0(l) == LC.rstrip0(vw) \
           and LC.rstrip0(r) == LC.rstrip0(fi):
            return t
    return None

def degree(xs, ys):
    if any(y is None for y in ys) or len(ys) < 4: return '?'
    d1 = [ys[i+1]-ys[i] for i in range(len(ys)-1)]
    if len(set(d1)) == 1: return 'AFFINE'
    r = [ys[i+1]/ys[i] for i in range(len(ys)-1) if ys[i]]
    if r and max(r)-min(r) < 0.25 and sum(r)/len(r) > 1.5:
        return 'EXP(ratio~%.2f)' % (sum(r)/len(r))
    d2 = [d1[i+1]-d1[i] for i in range(len(d1)-1)]
    if len(set(d2)) == 1: return 'QUAD'
    return 'HIGHER'

for spec0 in [l.strip() for l in open(sys.argv[1]) if l.strip()]:
    for s in (spec0, mirror_spec(spec0)):
        r = None
        try: r = IF.phase_probe(s, K=5)
        except Exception: pass
        if not r or not r['inner']: continue
        ex = [i for i in r['inner'] if i['kind'].startswith('EXACT')]
        if not ex: continue
        tab = parse(s); st_out = LAB.index(r['st0']); encf = EL.ENC[r['enc']]
        to_, fo = tuple(r['tail']), tuple(r['far'])
        name_in, st_in, tail_in, far_in = ex[0]['key']
        encfi = EL.ENC[name_in]; ti, fi = tuple(tail_in), tuple(far_in)
        Ks = [3,4,5,6,7]
        ys = [boot_len(tab, st_out, encf, to_, fo, st_in, encfi, ti, fi, K) for K in Ks]
        print('%-42s out=%-16s in=%s@%s  boot(K=3..8)=%s  -> %s'
              % (spec0, '%s@%s' % (r['enc'], r['st0']), name_in, LAB[st_in],
                 ys, degree(Ks, ys)), flush=True)
        break
