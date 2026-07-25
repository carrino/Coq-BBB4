#!/usr/bin/env python3
"""Scan the unproven pool for wall-anchored counters: derive_tail_far finds
an anchor with a NONEMPTY far word (direct or mirrored), and the lap from
that anchor closes raw.  Output JSONL."""
import json
import sys
from concurrent.futures import ProcessPoolExecutor

sys.path.insert(0, '/home/user/Coq-BBB4/tools/counters')
from emit_interleave import (ENC, LAB, Raw, strip0, derive_tail_far,
                             DeriveError)
from mirror_common import mirror_spec


def lap_len(spec, E, encf, tail, far, m, maxsteps=300000):
    raw = Raw(spec)
    cfg = (E, encf(m) + list(tail), 0, list(far))
    tgt = (E, tuple(strip0(encf(m + 1) + list(tail))), 0,
           tuple(strip0(far)))
    for t in range(1, maxsteps):
        cfg = raw.step(cfg)
        if cfg is None:
            return None
        q, l, h, r = cfg
        if (q, tuple(strip0(l)), h, tuple(strip0(r))) == tgt:
            return t
    return None


def probe(rspec):
    for mirror in (False, True):
        spec = mirror_spec(rspec) if mirror else rspec
        for enc in ('Jp', 'Ip'):
            try:
                edge, tail, p0, far = derive_tail_far(spec, 'A', encname=enc)
            except (DeriveError, Exception):
                continue
            if not far or not strip0(far):
                continue      # blank far: not a wall machine
            E = LAB.index(edge)
            encf = ENC[enc]
            ints = {}
            bad = False
            for j in range(0, 4):
                m = (1 << (j + 1)) + (1 << j) - 1 if j else 2
                n = lap_len(spec, E, encf, tail, far, m)
                if n is None:
                    bad = True
                    break
                ints[j] = n
            if bad:
                return {'spec': rspec, 'wall': True, 'mirror': mirror,
                        'enc': enc, 'edge': edge, 'tail': tail, 'far': far,
                        'p0': p0, 'laps': None}
            d1 = ints[1] - ints[0]
            d2 = ints[2] - ints[1]
            d3 = ints[3] - ints[2]
            affine = (d1 == d2 == d3)
            return {'spec': rspec, 'wall': True, 'mirror': mirror,
                    'enc': enc, 'edge': edge, 'tail': tail, 'far': far,
                    'p0': p0, 'laps': ints, 'affine': affine}
    return {'spec': rspec, 'wall': False}


def main():
    specs = [x.strip() for x in open(sys.argv[1]) if x.strip()]
    out = open(sys.argv[2], 'w')
    with ProcessPoolExecutor(max_workers=6) as pool:
        for r in pool.map(probe, specs, chunksize=8):
            out.write(json.dumps(r) + '\n')
            out.flush()


if __name__ == '__main__':
    main()
