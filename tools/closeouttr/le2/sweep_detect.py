#!/usr/bin/env python3
"""LE2 (UNTRUSTED measurement): is a row's interior arm a SWEEP?

    python3 sweep_detect.py ROWS OUT.jsonl     (resumable)

For famclose's first four families: the r=0 interior arm with an opaque
tail (plain), with one digit of lookahead (0 / top), and with the tail
`top^m 0` for m = 1..4.  A row whose top-lookahead arm has no chain but
whose `top^m 0` arms all do is a carry that sweeps the run of top digits
past the digit it increments (SCOPING_INSTR 7.4.LE2).  `other` is a row
whose r=0 arm is fine, so the arm fails at a longer carry."""
import os
import sys, json
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'ladder'))
import famclose as FC, emit_ladder as E, nest
def chain_ok(tab, el, er, c0, c1):
    ch=E.LC.derive_chain(tab,el,er,c0,c1,maxdepth=32,nmax=120,lift=True)
    if ch is None: return False
    got=E.LC.srun(tab,el,er,ch,c0)
    return got is not None and got[2]>0 and (got[0]==c1 or nest.ceqL(el,er,got[0],c1))
def detect(spec):
    cands=FC.family_certs(spec)
    if not cands: return {'spec':spec,'verdict':'no family'}
    tab=E.parse_tm(spec); res=[]
    for i,c in cands[:4]:
        f=c['family']; digs=[tuple(d) for d in f['digits']]; b=f['base']; pre=tuple(f['near_head_prefix'])
        q=ord(f['state'])-65; hs=f['head']; left=f['side']=='L'
        OTHER=(tuple(f['other_side_cells']),(),0,0,())
        conf=lambda sd:(q,sd,hs,OTHER) if left else (q,OTHER,hs,sd)
        el,er=(not left),left
        t=digs[b-1]; z=digs[0]
        def arm(tail, known):
            c0=conf((pre+z+tail,(),0,0,())); c1=conf((pre+digs[1]+tail,(),0,0,()))
            return chain_ok(tab, el if not left else True, er if left else True, c0, c1) if known else chain_ok(tab,el,er,c0,c1)
        v={'fam':i,'anchor':f['state']+str(hs)+f['side'],'digs':[''.join(map(str,d)) for d in digs]}
        v['plain']=arm((),False)
        v['look_z']=arm(z,False); v['look_t']=arm(t,False)
        v['sweep_m']=[m for m in range(1,5) if arm(t*m+z,False)]
        res.append(v)
    sw=any((not v['plain']) and (not v['look_t']) and len(v['sweep_m'])>=3 for v in res)
    return {'spec':spec,'verdict':'sweep' if sw else 'other','fams':res}
if __name__=='__main__':
    out=open(sys.argv[2],'a')
    done=set()
    try:
        done=set(json.loads(l)['spec'] for l in open(sys.argv[2]))
    except Exception: pass
    for s in open(sys.argv[1]).read().split():
        if s in done: continue
        try: r=detect(s)
        except Exception as e: r={'spec':s,'verdict':'error %r'%e}
        out.write(json.dumps(r)+'\n'); out.flush(); print(s,r['verdict'],flush=True)
