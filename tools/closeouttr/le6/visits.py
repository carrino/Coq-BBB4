"""LE6: print the tape at anchor visits (head at a tape end turning back),
for eyeballing.  python3 visits.py SPEC STEPS [side L|R] [maxlines]"""
import sys
from collections import defaultdict
sys.path.insert(0, __import__('os').path.dirname(__file__))
from conj_check import parse

def run(spec, N, side='R', maxl=200, start=0):
    tab = parse(spec); tape = defaultdict(int); p = 0; q = 0; lo = hi = 0
    out = []
    last_mv = 0
    for t in range(N):
        v = tab[(q, tape[p])]
        if v is None: break
        mv = 1 if v[1] == 'R' else -1
        at_end = (p == hi if side == 'R' else p == lo)
        if t >= start and at_end and ((side == 'R' and mv == -1) or (side == 'L' and mv == 1)):
            s = ''.join(('ABCD'[q] if x == p else '') + str(tape[x]) for x in range(lo, hi + 1))
            out.append('%9d %s' % (t, s))
            if len(out) >= maxl: break
        tape[p] = int(v[0]); p += mv; q = v[2]
        lo = min(lo, p); hi = max(hi, p)
    return out

if __name__ == '__main__':
    a = sys.argv[1:]
    for l in run(a[0], int(a[1]), a[2] if len(a) > 2 else 'R', int(a[3]) if len(a) > 3 else 200,
                 int(a[4]) if len(a) > 4 else 0):
        print(l)
