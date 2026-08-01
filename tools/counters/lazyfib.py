#!/usr/bin/env python3
"""UNTRUSTED (tools/): which CANONICAL FORM of the fibonacci numeration a
row's anchor words are in.

LADDER_PLAN 4v.  All eleven three-state `1RB---` fibonacci rows decode to
0, 1, 2, ... at a flat one-cell-per-digit anchor under the weights
`fibw = 1, 1, 2, 3, 5, 8` -- the ones `LadderCheck` section 3c states.  The
numeration is REDUNDANT, so that is not enough: `fam_of_value` at `Fib` is
`fibdec`, which picks one representative, and this script asks which one
each row is actually in.

Two predicates, both on the LSB-first digit string:

  fibokb  -- LadderCheck 3c's own membership ("at every 0 the number of 1s
             above it is even", equivalently "every run of 1s is even
             except the one reaching index 0").  The kernel speaks this.
  lazy    -- "d0 = 1 and no two adjacent ZEROS", the dual/lazy form.

Measured: the five rows section 4r boarded score 4000/4000 `fibokb` and
243/4000 `lazy`; the six that remain score 324/4000 and 4000/4000.  The
complement is exact, and it is the whole reason the six do not board.

    python3 tools/counters/lazyfib.py
"""
import re
import sys
from collections import defaultdict

LAB = "ABCD"


def parse(spec):
    tab = {}
    for si, part in enumerate(spec.split('_')):
        for yi in range(2):
            e = part[3 * yi:3 * yi + 3]
            tab[(si, yi)] = None if e == '---' else (
                int(e[0]), +1 if e[1] == 'R' else -1, ord(e[2]) - ord('A'))
    return tab


def run(spec, T):
    """yield (step, state, left, head, right); left and right NEAREST-FIRST,
    trailing blanks trimmed."""
    tab = parse(spec)
    tape = defaultdict(int)
    pos, st, lo, hi = 0, 0, 0, 0
    for n in range(T):
        sym = tape[pos]
        e = tab[(st, sym)]
        if e is None:
            return
        l = [tape[x] for x in range(pos - 1, lo - 1, -1)]
        r = [tape[x] for x in range(pos + 1, hi + 1)]
        while l and l[-1] == 0:
            l.pop()
        while r and r[-1] == 0:
            r.pop()
        yield (n, st, l, sym, r)
        w, d, ns = e
        tape[pos] = w
        lo, hi = min(lo, pos), max(hi, pos)
        pos += d
        st = ns
        lo, hi = min(lo, pos), max(hi, pos)


def fibw(n):
    a, b = 1, 1
    for _ in range(n):
        a, b = b, a + b
    return a


ROWS = ["1RB---_0LC1RD_1LB1RC_1LB0RD","1RB---_0LC1RD_1LB1RD_1LB0RD",
        "1RB---_1LC0RB_0LD1RB_1LC1RB","1RB---_1LC0RB_0LD1RB_1LC1RD",
        "1RB---_1LC1RB_0LB1RD_1LC0RD","1RB---_1LC1RD_0LB1RD_1LC0RD"]
BOARDED = ["1RB---_0LB1RC_1LB0RD_1LC0RD","1RB---_1LC1RD_0LC1RD_1LB0RD",
           "1RB---_1LC0RB_1LD1RB_0LD1RB","1RB---_0LB1RC_1LD0RC_1LB1RC",
           "1RB---_1LC0RD_0LC1RB_1LB0RD"]

def fibval(ds, off=0): return sum(d*fibw(i+off) for i,d in enumerate(ds))
def fibokb(o, ds):   # LadderCheck 3c membership (even runs)
    return all((sum(ds[i+1:])%2==1)==o for i,d in enumerate(ds) if d==0)
def lazy(ds):        # "low digit 1, no two adjacent 0s"
    if not ds: return True
    if ds[0]!=1: return False
    return all(not(ds[i]==0 and ds[i+1]==0) for i in range(len(ds)-1))

def best_anchor(spec, T=200000, cap=4000):
    fams=defaultdict(list)
    for (n,q,l,h,r) in run(spec,T):
        for t in range(3):
            if len(l)==t: fams[(q,h,'R',tuple(l))].append(tuple(r))
    best=None
    for key,ws in fams.items():
        ws=ws[:cap]
        if len(ws)<100: continue
        vs=[fibval(w) for w in ws]
        c=cur=0
        for i,v in enumerate(vs):
            cur=cur+1 if (cur and v==vs[i-1]+1) else 1
            c=max(c,cur)
        if best is None or c>best[0]: best=(c,len(ws),key,ws)
    return best

print("%-32s %-16s %8s %8s %8s" % ("row","anchor","consec","fibokb","lazy"))
for spec in ROWS+["--"]+BOARDED:
    if spec=="--": print("-"*80); continue
    c,tot,key,ws = best_anchor(spec)
    fo=max(sum(1 for w in ws if fibokb(o,list(w))) for o in (False,True))
    lz=sum(1 for w in ws if lazy(list(w)))
    print("%-32s St%s h=S%d o=%-6s %5d/%d %6d %8d" %
          (spec, LAB[key[0]], key[1], ''.join(map(str,key[3])) or "-", c, tot, fo, lz))


def law(spec, T=300000, cap=4000):
    """The lazy form's INCREMENT, checked against the machine: the run of
    ones below the first zero comes back as an ALTERNATING (1 0) run of half
    the length, in two parity classes.  LADDER_PLAN 4v."""
    c, tot, key, ws = best_anchor(spec, T, cap)
    bad, mism = 0, 0
    cls = defaultdict(int)
    for a, b in zip(ws, ws[1:]):
        a, b = list(a), list(b)
        if fibval(b) != fibval(a) + 1:
            bad += 1
            continue
        i = 0
        while i < len(a) and a[i] == 1:
            i += 1
        if i == len(a):
            cls['top'] += 1
            continue
        pred = ([1] if i % 2 else []) + [1, 0] * (i // 2) + [1] + a[i + 1:]
        if pred != b:
            mism += 1
        cls['odd' if i % 2 else 'even'] += 1
    return bad, mism, dict(cls)


if '--law' in sys.argv:
    print()
    print("%-32s %8s %8s  %s" % ("row", "value+1", "law", "classes"))
    for spec in ROWS:
        bad, mism, cls = law(spec)
        print("%-32s %8d %8d  %s" % (spec, bad, mism, cls))
