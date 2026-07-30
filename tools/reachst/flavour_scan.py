#!/usr/bin/env python3
"""UNTRUSTED probe: how many rows of a list have a SPARSE state whose
avoid sub-machine is one of the two ReachSt flavours, up to STATE RELABELLING
and/or MIRRORING?

Relabelling is already exploited by tools/nghist/reachst_prove.py (the four
ReachSt roles are section variables).  Mirroring is NOT -- see
docs/REACHST_TIER.md section 6 for what it would take.

  python3 tools/reachst/flavour_scan.py tools/closeout/core_rows.txt
"""
import sys, itertools
from collections import defaultdict
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from avoid_probe import parse, usage, avoid_table, show, LAB

def spec_of(tab):
    out=[]
    for q in range(4):
        for s in (0,1):
            tr=tab[(q,s)]
            out.append('---' if tr is None else '%d%s%s'%(tr[0],'R' if tr[1]>0 else 'L',LAB[tr[2]]))
    return '_'.join(out[i]+out[i+1] for i in range(0,8,2))

def mirror(tab):
    return {(q,s):(None if tr is None else (tr[0],-tr[1],tr[2])) for (q,s),tr in tab.items()}

def relabel(tab, perm):
    # perm: tuple p with p[i] = new index of old state i
    out={}
    for (q,s),tr in tab.items():
        out[(perm[q],s)] = None if tr is None else (tr[0],tr[1],perm[tr[2]])
    return out

# the two ReachSt flavours, as avoid-tables over states A,B,D with halt at B0
FLAV = {
 'mb': 'A0->1RB A1->0LD B0->HALT B1->1RA D0->0RB D1->1LD',
 'ma': 'A0->1RB A1->0LD B0->HALT B1->1RA D0->0RA D1->1LD',
}

def match(tab, qa):
    return show(avoid_table(tab, qa))

def main():
    specs=open(sys.argv[1]).read().split()
    hits=defaultdict(list)
    for m in specs:
        tab=parse(m)
        cnt=usage(m,200000)
        sp=min(range(4),key=lambda i:cnt[i])
        for mir,t0 in (('fwd',tab),('mir',mirror(tab))):
            for perm in itertools.permutations(range(4)):
                t=relabel(t0,perm)
                qa=perm[sp]
                k=match(t,qa)
                for name,want in FLAV.items():
                    if k==want:
                        hits[m].append((mir,perm,name))
    print('%d of %d rows match a flavour up to relabel/mirror' % (len(hits), len(specs)))
    for m,v in sorted(hits.items()):
        print('  %s  %s' % (m, v[0]))

main()
