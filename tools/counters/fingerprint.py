#!/usr/bin/env python3
"""UNTRUSTED fingerprinter for the wave-8 interleaved-counter core.

For each machine: simulate from blank, find the per-increment ANCHOR (a config
with one side empty and a blank head whose visits grow linearly), read the
counter list off the non-empty side, and identify the ENCODING + ORIENTATION:

  encoding  Ip  (ILCounter: xO->S1::S0, xI->S1::S1)   data bit = binary digit
            Jp  (JpCounter: xO->S1::S1, xI->S1::S0)   data bit = complement
  growth    L (counter on the left list, right side empty) | R (mirror)
  edge      the anchor state
  head      the anchor head symbol

Emits one JSON record per machine so the emitter can dispatch on the
fingerprint.  The Coq kernel re-checks every board this targets.
"""
import sys, os, json
from concurrent.futures import ProcessPoolExecutor

def parse(spec):
    tab = {}
    for si, part in enumerate(spec.split('_')):
        for yi in range(2):
            e = part[3*yi:3*yi+3]
            tab[(si, yi)] = None if e == '---' else (
                int(e[0]), +1 if e[1] == 'R' else -1, ord(e[2]) - ord('A'))
    return tab

def Ip(m):
    out = []
    while m > 1:
        out += [1, m & 1]          # xO -> S1::S0 ; xI -> S1::S1
        m >>= 1
    return out + [1]

def Jp(m):
    out = []
    while m > 1:
        out += [1, 1 - (m & 1)]    # xO -> S1::S1 ; xI -> S1::S0
        m >>= 1
    return out + [1]

def enc_tables(bound=4096):
    ti, tj = {}, {}
    for m in range(1, bound):
        ti[tuple(Ip(m))] = m
        tj[tuple(Jp(m))] = m
    return ti, tj

TI, TJ = enc_tables()

def strip_tail0(l):
    while l and l[-1] == 0:
        l = l[:-1]
    return l

def fingerprint(spec, T=30000):
    tab = parse(spec)
    q, l, h, r = 0, [], 0, []
    # candidate anchors: (state, side) -> list of (t, counter_list)
    cand = {}
    for t in range(T):
        e = tab[(q, h)]
        if e is None:
            return {'m': spec, 'cls': 'HALT'}
        if h == 0:
            if not r and l:
                cand.setdefault((q, 'L'), []).append((t, tuple(l)))
            elif not l and r:
                cand.setdefault((q, 'R'), []).append((t, tuple(r)))
        w, d, ns = e
        if d > 0:
            q, l, h, r = ns, [w] + l, (r[0] if r else 0), r[1:]
        else:
            q, l, h, r = ns, l[1:], (l[0] if l else 0), [w] + r
    best = None
    for (st, side), snaps in cand.items():
        if len(snaps) < 8:
            continue
        # decode each snapshot under both encodings (strip the trailing blank)
        seq_i, seq_j = [], []
        for (t, cl) in snaps:
            c = tuple(strip_tail0(list(cl)))
            seq_i.append(TI.get(c))
            seq_j.append(TJ.get(c))
        for name, seq in (('Ip', seq_i), ('Jp', seq_j)):
            vals = [v for v in seq if v is not None]
            if len(vals) < 6:
                continue
            # consecutive-increment test on the decoded values
            runs = sum(1 for a, b in zip(vals, vals[1:]) if b == a + 1)
            frac = runs / max(1, len(vals) - 1)
            hit = len(vals) / len(seq)
            score = frac * hit * len(vals)
            if frac >= 0.75 and hit >= 0.5:
                if best is None or score > best['score']:
                    best = {'score': score, 'enc': name, 'edge': "ABCD"[st],
                            'growth': side, 'nsnap': len(snaps), 'ndec': len(vals),
                            'frac': round(frac, 3), 'p0': vals[0]}
    if best is None:
        return {'m': spec, 'cls': 'NOFIT', 'ncand': len(cand)}
    best.pop('score')
    best['m'] = spec
    best['cls'] = 'COUNTER'
    return best

def main():
    src = sys.argv[1]
    out = sys.argv[2]
    ms = [x.strip() for x in open(src) if x.strip()]
    n = int(os.environ.get('FP_LIMIT', len(ms)))
    ms = ms[:n]
    with open(out, 'w') as f, ProcessPoolExecutor(max_workers=3) as ex:
        for i, r in enumerate(ex.map(fingerprint, ms, chunksize=8)):
            f.write(json.dumps(r) + '\n')
            if (i + 1) % 250 == 0:
                f.flush()
                sys.stderr.write('%d/%d\n' % (i + 1, len(ms)))
    sys.stderr.write('DONE %d\n' % len(ms))

if __name__ == '__main__':
    main()
