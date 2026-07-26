import json, sys
from concurrent.futures import ProcessPoolExecutor
sys.path.insert(0, '/home/user/Coq-BBB4/tools/counters')
from emit_interleave import ENC, LAB, Raw, strip0
from mirror_common import mirror_spec

def kind(r):
    spec = mirror_spec(r['spec']) if r['mirror'] else r['spec']
    f = ENC[r['enc']]; E = LAB.index(r['edge']); tl = list(r['tail'])
    raw = Raw(spec)
    res = []
    for K in (2, 3, 4):
        m = (1 << K) - 1
        cfg = (E, f(m) + tl, 0, [])
        land = None
        for t in range(1, 120000):
            cfg = raw.step(cfg)
            if cfg is None: break
            q, l, h, rr = cfg
            if q == E and h == 0 and not strip0(rr):
                w = tuple(strip0(l))
                for v in range(m + 1, 1 << (K + 4)):
                    if tuple(f(v)) + tuple(tl) == w:
                        land = (v, t); break
                if land: break
        res.append(land)
    if any(x is None for x in res): return dict(r, ov='no-close')
    vs = [v for v, _ in res]
    exp = [(1 << K) for K in (2, 3, 4)]
    exp2 = [(1 << (K + 1)) for K in (2, 3, 4)]
    if vs == exp:  return dict(r, ov='standard')
    if vs == exp2: return dict(r, ov='widen')
    return dict(r, ov='other:%s' % vs)

if __name__ == '__main__':
    rs = [json.loads(l) for l in open('reanchor.jsonl')]
    aff = [r for r in rs if r.get('affine') is True]
    with ProcessPoolExecutor(max_workers=6) as p, open('ovkind.jsonl','w') as o:
        for r in p.map(kind, aff, chunksize=4):
            o.write(json.dumps(r)+'\n'); o.flush()
