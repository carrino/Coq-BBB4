import sys, os, json
sys.path.insert(0,'/home/user/Coq-BBB4/tools')
import repwl_prover as rp
from concurrent.futures import ProcessPoolExecutor
RUNGS=[(10,2,0),(8,2,0),(12,2,0),(6,2,0),(10,3,0),(16,2,0),(5,2,0),(20,2,0),(14,2,0),(9,2,0),(7,2,0),(11,2,0)]
def work(m):
    try: tbl=rp.parse(m)
    except Exception: return (m,None)
    for (L,T,t) in RUNGS:
        try: r=rp.build_closure(tbl,L,T,t,cap=20000)
        except Exception: continue
        if r is None: continue
        a0,seen=r
        try:
            adj={a: rp.rw_succs(tbl,L,T,a) for a in seen}
            states=sorted({a[0] for a in seen} | rp.warmup_states(tbl,t))
            ok=True
            for qq in states:
                comps=rp.procedure(tbl,seen,adj,qq,rp.MEAS)
                if comps is None or not rp.lex_check(tbl,adj,seen,qq,comps): ok=False; break
        except Exception: ok=False
        if ok: return (m,(L,T,t,len(seen)))
    return (m,None)
if __name__=='__main__':
    src,out=sys.argv[1],sys.argv[2]
    ms=[l.strip() for l in open(src) if l.strip()]
    n=int(os.environ.get('LIM',len(ms))); ms=ms[:n]
    ok=0
    with open(out,'w') as f, ProcessPoolExecutor(max_workers=3) as ex:
        for i,(m,res) in enumerate(ex.map(work, ms, chunksize=4)):
            if res:
                ok+=1; f.write("%s\t%d\t%d\t%d\t%d\n"%(m,res[0],res[1],res[2],res[3])); f.flush()
            if (i+1)%100==0: sys.stderr.write("  %d/%d caught=%d\n"%(i+1,len(ms),ok))
    sys.stderr.write("DONE %d/%d caught\n"%(ok,len(ms)))
