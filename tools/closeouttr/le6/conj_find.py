"""LE6: for a target row `dst` that is a state-permuted / mirrored conjugate
of a boarded row `src`, find boots (m, n0) with
    csteps src m c0 = a,  csteps dst n0 c0 = b,  b == cconj p flip a (up to blanks),
and n0 <= m for CConjCoverTr's cover route (n0 > m: its never-QH route).  Output jsonl, one line per target.

    python3 tools/closeouttr/le6/conj_find.py ROWS OUT.jsonl [--steps N]
"""
import itertools, json, sys
from collections import defaultdict
sys.path.insert(0, 'tools/closeouttr/le6')
from conj_check import parse, render, conj, canon

def sim(spec, n):
    tab = parse(spec)
    tape = defaultdict(int); pos = 0; q = 0
    out = []
    for i in range(n + 1):
        out.append((q, pos, dict(tape)) if False else None)
        yield i, q, pos, tape
        v = tab[(q, tape[pos])]
        if v is None:
            return
        tape[pos] = int(v[0]); pos += 1 if v[1] == 'R' else -1; q = v[2]

def key(q, pos, tape, flip):
    ks = [k for k, v in tape.items() if v]
    if not ks:
        lo = hi = pos
    else:
        lo, hi = min(ks + [pos]), max(ks + [pos])
    cells = tuple(tape.get(k, 0) for k in range(lo, hi + 1))
    off = pos - lo
    if flip:
        cells = cells[::-1]; off = len(cells) - 1 - off
    return (q, off, cells)

def find(dst, src, p, flip, steps):
    # src frame: dst state p[q] corresponds to src state q
    pinv = {p[q]: q for q in range(4)}
    seen = {}
    for i, q, pos, tape in sim(src, steps):
        k = key(q, pos, tape, False)
        if k not in seen:
            seen[k] = i
    for j, q, pos, tape in sim(dst, steps):
        k = key(pinv[q], pos, tape, flip)
        if k in seen:
            return seen[k], j     # lockstep from here: the offset is fixed
    return None

def perms_to(dst, src):
    """all (p, flip) with conj(src, p, flip) == dst"""
    t = parse(src); out = []
    for p in itertools.permutations(range(4)):
        for f in (0, 1):
            if render(conj(t, p, f)) == dst:
                out.append((p, f))
    return out

def main():
    rows = open(sys.argv[1]).read().split()
    outp = sys.argv[2]
    steps = int(sys.argv[sys.argv.index('--steps') + 1]) if '--steps' in sys.argv else 200000
    srcs = {}
    for l in open('closeouttr_boarded.tsv'):
        if l.strip() and not l.startswith('#'):
            s, b = l.split()[:2]
            srcs.setdefault(canon(s), []).append((s, b))
    extra = {}
    if '--extra' in sys.argv:   # extra (spec batch) sources, e.g. this session's boards
        for l in open(sys.argv[sys.argv.index('--extra') + 1]):
            s, b = l.split()[:2]
            srcs.setdefault(canon(s), []).append((s, b))
    with open(outp, 'w') as fo:
        for r in rows:
            c = canon(r)
            res = None
            for s, b in srcs.get(c, []):
                if s == r:
                    continue
                for p, f in perms_to(r, s):
                    got = find(r, s, p, f, steps)
                    if got:
                        cand = dict(spec=r, src=s, batch=b, p=list(p), flip=f, m=got[0], n0=got[1])
                        if res is None or 'm' not in res or (res['n0'] > res['m'] and got[1] <= got[0]):
                            res = cand
                    else:
                        res = res or dict(spec=r, src=s, batch=b, p=list(p), flip=f, fail='no sync')
                if res and 'm' in res and res['n0'] <= res['m']:
                    break
            if res:
                fo.write(json.dumps(res) + '\n'); fo.flush()
                print(json.dumps(res))

if __name__ == '__main__':
    main()
