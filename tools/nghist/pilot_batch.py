#!/usr/bin/env python3
"""Pilot batch: measure closure-rate and liveness-discharge-rate over a
representative residue sample, plain vs history-augmented."""
import csv, collections, random, sys
import nghist_pilot as P

CSV="/tmp/claude-0/-home-user/14351b7c-8968-51fa-89db-dbaa1c0ae003/scratchpad/residue_provenance.csv"
UNC="/tmp/claude-0/-home-user/14351b7c-8968-51fa-89db-dbaa1c0ae003/scratchpad/pqhs_uncaught.txt"

rows=[r for r in csv.reader(open(CSV))][1:]
by_dec=collections.defaultdict(list)
for r in rows:
    if len(r)>4: by_dec[r[4]].append(r[0])
unc=set(l.strip() for l in open(UNC) if l.strip())

random.seed(42)
sample=[]
# 18 IMPL1(2,2,2) counters
sample += [('IMPL1_222', m) for m in random.sample(by_dec['NGRAM_CPS_IMPL1_params_2_2_2_1600'], 18)]
# 12 IMPL2(1,1) plain
sample += [('IMPL2_11', m) for m in random.sample(by_dec['NGRAM_CPS_IMPL2_params_1_1_100'], 12)]
# 10 wave-4 uncaught (may overlap)
sample += [('w4_uncaught', m) for m in random.sample(sorted(unc), 10)]

def run(m):
    out={}
    # plain closure only
    rp=P.analyze(m,0,2,2,20000,t=150)
    out['plain_close']=rp['closed']
    # history-augmented at (2,2,2) then (4,2,2) then (6,2,2)
    for (k,tag) in [(2,'h2'),(4,'h4'),(6,'h6')]:
        r=P.analyze(m,k,2,2,60000,t=150)
        out[tag+'_close']=r['closed']
        out[tag+'_board']=r['boarded']
        out[tag+'_scc']=r['scc_ok']
        if r['closed']: out[tag+'_r']=r
    return out

stats=collections.Counter()
per_class=collections.defaultdict(collections.Counter)
detail=[]
for cls,m in sample:
    try:
        o=run(m)
    except Exception as e:
        detail.append((cls,m,'ERR',str(e)[:40])); continue
    pc=per_class[cls]
    pc['n']+=1
    if o['plain_close']: pc['plain_close']+=1
    # best history level that boards / closes
    closed_h = any(o.get(t+'_close') for t in ['h2','h4','h6'])
    board_h  = any(o.get(t+'_board') for t in ['h2','h4','h6'])
    scc_h    = any(o.get(t+'_scc') for t in ['h2','h4','h6'])
    if o.get('h2_close'): pc['h2_close']+=1
    if closed_h: pc['hist_close']+=1
    if o.get('h2_board'): pc['h2_board']+=1
    if board_h: pc['hist_board']+=1
    if scc_h: pc['scc_recur']+=1
    lvl='-'
    for t in ['h2','h4','h6']:
        if o.get(t+'_board'): lvl=t; break
    detail.append((cls,m,'plainC' if o['plain_close'] else 'plainX',
                   'h2C' if o.get('h2_close') else 'h2X',
                   'BOARD@'+lvl if board_h else ('scc' if scc_h else 'noLive')))

print("="*72)
print(f"{'class':14s} {'n':>3s} {'plainClose':>10s} {'h2Close':>8s} {'histClose':>9s} "
      f"{'sccRecur':>8s} {'h2Board':>7s} {'histBoard':>9s}")
for cls in ['IMPL1_222','IMPL2_11','w4_uncaught']:
    pc=per_class[cls]; n=pc['n'] or 1
    print(f"{cls:14s} {pc['n']:3d} {pc['plain_close']:10d} {pc['h2_close']:8d} "
          f"{pc['hist_close']:9d} {pc['scc_recur']:8d} {pc['h2_board']:7d} {pc['hist_board']:9d}")
print("="*72)
print("per-machine:")
for d in detail:
    print("  "+" ".join(str(x) for x in d))
