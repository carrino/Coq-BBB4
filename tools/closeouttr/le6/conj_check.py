"""LE6: are any target rows state-permuted / mirrored conjugates of boarded rows
(or of each other)?  Canonical form over the 24 state permutations x mirror."""
import itertools, sys
from collections import defaultdict

def parse(spec):
    ts = spec.split('_')
    tab = {}
    for qi, t in enumerate(ts):
        for s in range(2):
            x = t[3*s:3*s+3]
            tab[(qi, s)] = None if x[2] in '-Z' else (x[0], x[1], 'ABCD'.index(x[2]))
    return tab

def render(tab):
    out = []
    for q in range(4):
        cell = ''
        for s in range(2):
            v = tab[(q, s)]
            cell += '---' if v is None else v[0] + v[1] + 'ABCD'[v[2]]
        out.append(cell)
    return '_'.join(out)

def conj(tab, p, flip):
    inv = {p[q]: q for q in range(4)}
    new = {}
    for q in range(4):
        for s in range(2):
            v = tab[(inv[q], s)]
            if v is None:
                new[(q, s)] = None
            else:
                d = v[1]
                if flip:
                    d = 'L' if d == 'R' else 'R'
                new[(q, s)] = (v[0], d, p[v[2]])
    return new

def canon(spec):
    tab = parse(spec)
    return min(render(conj(tab, p, f)) for p in itertools.permutations(range(4)) for f in (0, 1))

if __name__ == '__main__':
    rows = open(sys.argv[1]).read().split()
    boarded = [l.split('\t') for l in open('closeouttr_boarded.tsv') if l.strip() and not l.startswith('#')]
    bmap = defaultdict(list)
    for b in boarded:
        bmap[canon(b[0])].append((b[0], b[1]))
    rmap = defaultdict(list)
    hits = 0
    for r in rows:
        c = canon(r)
        rmap[c].append(r)
        if c in bmap:
            hits += 1
            print('BOARDED', r, bmap[c][:3])
    print('conjugates of boarded:', hits)
    cls = [v for v in rmap.values() if len(v) > 1]
    print('classes among targets with >1 member:', len(cls), 'rows', sum(len(v) for v in cls))
    for v in cls:
        print('  ', ' '.join(v))
