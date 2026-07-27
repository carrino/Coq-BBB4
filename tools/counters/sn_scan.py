"""Test mxdys' claim on all 11 live (4,2) holdouts.

S(n) candidates = record configurations grouped by (state, side, head offset,
RLE shape).  A candidate PASSES iff, over the laps it defines, every run
length of S(n) AND every transition's usage count over S(n) -->+ S(n+1)
satisfies a short constant-coefficient linear recurrence (C-finite = 'simple
function of n'), validated on terms beyond those the fit consumed.
"""
import sys, collections, itertools
from sim import Sim, LAB
from snfit import find_rec
from recs import allrecords, TR
TNAME={(q,y):"%s%d"%(LAB[q],y) for q in range(4) for y in range(2)}
def rle(s):
    return [(c,len(list(g))) for c,g in itertools.groupby(s)]
def shape(s): return ''.join(c for c,_ in rle(s))
def rle_str(s): return ' '.join(c if n==1 else '%s^%d'%(c,n) for c,n in rle(s))

def closed_form(d,c):
    if d is None: return None
    if d==0: return 'const 0'
    return 'order-%d: a(n+%d) = %s'%(d,d,' + '.join('(%s)a(n+%d)'%(c[i],d-i-1) for i in range(d) if c[i]!=0) or '0')

def analyse(spec, steps, minlaps=6):
    recs,h=allrecords(spec,steps)
    if h: return None
    cls=collections.defaultdict(list)
    for i,(t,q,sd,off,tp,cum) in enumerate(recs): cls[(q,sd,off,shape(tp))].append(i)
    best=None
    for key,idx in sorted(cls.items(), key=lambda kv:-len(kv[1])):
        if len(idx)<minlaps+2: continue
        for drop in range(0,4):
            J=idx[drop:-1]
            if len(J)<minlaps+1: break
            rl=[[n for _,n in rle(recs[j][4])] for j in J]
            if len(set(map(len,rl)))!=1: continue
            rf=[find_rec([r[c] for r in rl]) for c in range(len(rl[0]))]
            if any(d is None for d,_ in rf): continue
            tf={}
            good=True
            for k in TR:
                vals=[recs[J[a+1]][5][k]-recs[J[a]][5][k] for a in range(len(J)-1)]
                d,c=find_rec(vals)
                if d is None: good=False; break
                tf[k]=(d,c,vals)
            if not good: continue
            cand=(key,J,rf,tf,drop,recs)
            if best is None or len(J)>len(best[1]): best=cand
            break
    return best

FROZEN=set(l.strip() for l in open('/home/user/Coq-BBB4/tools/closeout/frozen_unproven.txt'))
ALL11=['1RB---_1LC0LB_0RC0LD_1RD1RB','1RB---_1RC0RB_0LC0RD_1LD1LB',
 '1RB0LD_1RC0RC_1LA1RB_0LC0LD','1RB0RB_1LC1RA_1RA0LD_0LB0LD',
 '1RB1LC_1LC1RD_1LA0LC_0RD0RB','1RB0LA_1LC0RD_0LB1LA_0RB1LA',
 '1RB0LA_1LC1RD_0LC1LA_0RD0RB','1RB0RC_0LC1LB_0LD1LC_1RD0RA',
 '1RB0RD_1LC1LB_1RA0LB_1LC1RA','1RB1LD_1RC0RB_1LA0RC_0LD0LA',
 '1RB1RA_0RC0RB_1LC1LD_0RA0LA']





FAM={'1RB---_1LC0LB_0RC0LD_1RD1RB':'wrapQH-a','1RB---_1RC0RB_0LC0RD_1LD1LB':'wrapQH-b',
 '1RB0LD_1RC0RC_1LA1RB_0LC0LD':'blockdbl#11','1RB0RB_1LC1RA_1RA0LD_0LB0LD':'blockdbl#13',
 '1RB1LC_1LC1RD_1LA0LC_0RD0RB':'blockdbl#28','1RB0LA_1LC0RD_0LB1LA_0RB1LA':'fractal#3',
 '1RB0LA_1LC1RD_0LC1LA_0RD0RB':'fractal#5','1RB0RC_0LC1LB_0LD1LC_1RD0RA':'wave4#15',
 '1RB0RD_1LC1LB_1RA0LB_1LC1RA':'tower#20','1RB1LD_1RC0RB_1LA0RC_0LD0LA':'double#32',
 '1RB1RA_0RC0RB_1LC1LD_0RA0LA':'v4-irules'}
STEPS=int(sys.argv[1]) if len(sys.argv)>1 else 4000000
for m in ALL11:
    b=analyse(m,STEPS)
    st='PROVED-IN-TREE' if m not in FROZEN else 'unproven'
    print('='*96)
    print('%-32s %-12s [%s]'%(m,FAM[m],st))
    if b is None: print('   no S(n) found among record shape-classes'); continue
    (q,sd,off,shp),J,rf,tf,drop,recs=b
    print('   S(n): state=%s record-side=%s off=%d shape=%s   laps=%d  boot-skip=%d'%(LAB[q],sd,off,shp,len(J)-1,drop))
    for a in range(min(4,len(J))): print('      S(%d) t=%-9d %s'%(a,recs[J[a]][0],rle_str(recs[J[a]][4])))
    print('   run lengths:  %s'%['blk%d:%s'%(c,closed_form(d,co)) for c,(d,co) in enumerate(rf)])
    for k in TR:
        d,c,vals=tf[k]
        print('      %-3s %-46s  %s'%(TNAME[k],closed_form(d,c),vals[:5]))
