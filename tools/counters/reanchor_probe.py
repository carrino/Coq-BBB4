#!/usr/bin/env python3
"""For each unproven machine: find the anchor family (state, tail) with the
most consecutive-value snapshots from the blank tape, and test whether the
interior laps from THAT anchor are affine.  Estimates how much of the
residue is unlocked by fixing the anchor search alone."""
import json, sys
from collections import defaultdict
from concurrent.futures import ProcessPoolExecutor
sys.path.insert(0, '/home/user/Coq-BBB4/tools/counters')
from emit_interleave import ENC, LAB, Raw, strip0
from mirror_common import mirror_spec
Ip, Jp = ENC['Ip'], ENC['Jp']

TAILS = [(1,), (1,0), (0,), (), (1,1), (0,0)]
DEC = {}
def build():
    if DEC: return
    for name, f in (('Ip', Ip), ('Jp', Jp)):
        d = {}
        for tl in TAILS:
            for m in range(1, 1 << 11):
                d.setdefault(tuple(f(m)) + tl, (m, tl))
        DEC[name] = d

def probe_one(rspec):
    build()
    out = None
    for mirror in (False, True):
        spec = mirror_spec(rspec) if mirror else rspec
        raw = Raw(spec)
        for enc in ('Ip', 'Jp'):
            d = DEC[enc]
            cfg = (0, [], 0, [])
            fam = defaultdict(list)
            for t in range(1, 25000):
                cfg = raw.step(cfg)
                if cfg is None: break
                q, l, h, r = cfg
                if h == 0 and not strip0(r) and tuple(l) in d:
                    m, tl = d[tuple(l)]
                    fam[(q, tl)].append(m)
            if not fam: continue
            (q, tl), vals = max(fam.items(), key=lambda kv: len(kv[1]))
            if len(vals) < 12: continue
            f = ENC[enc]
            def lap(m, maxs=60000):
                c = (q, f(m) + list(tl), 0, [])
                tg = (q, tuple(strip0(f(m+1) + list(tl))), 0, ())
                for t in range(1, maxs):
                    c = raw.step(c)
                    if c is None: return None
                    if (c[0], tuple(strip0(c[1])), c[2], tuple(strip0(c[3]))) == tg:
                        return t
                return None
            ints = {}
            ok = True
            for j in range(0, 4):
                m = (1 << (j+1)) + (1 << j) - 1 if j else 2
                n = lap(m)
                if n is None: ok = False; break
                ints[j] = n
            if not ok: continue
            ds = [ints[j+1] - ints[j] for j in range(3)]
            if len(set(ds)) == 1:
                return {'spec': rspec, 'mirror': mirror, 'enc': enc,
                        'edge': LAB[q], 'tail': list(tl), 'slope': ds[0],
                        'n': len(vals), 'affine': True}
            out = out or {'spec': rspec, 'mirror': mirror, 'enc': enc,
                          'edge': LAB[q], 'tail': list(tl), 'affine': False}
    return out or {'spec': rspec, 'affine': None}

if __name__ == '__main__':
    specs = [x.strip() for x in open(sys.argv[1]) if x.strip()][:int(sys.argv[3])]
    with ProcessPoolExecutor(max_workers=6) as pool, open(sys.argv[2], 'w') as o:
        for r in pool.map(probe_one, specs, chunksize=4):
            o.write(json.dumps(r) + '\n'); o.flush()
