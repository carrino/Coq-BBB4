"""Is the EXPONENTIAL exit a SECOND inner count in a shifted frame?

Split one overflow phase at the first inner all-ones fill and run the
inner-family search separately on each half.  If the second half also carries
a consecutive family, the phase is boot + count + mid + count + exit, which is
mxdys' sync-bouncer-counter shape ("count 8->15, shift, count 8->15 again")
and composes with nested_overflow_lift rather than needing new theory.
"""
import sys, os, collections
sys.path.insert(0,'/home/user/Coq-BBB4/tools/counters'); os.chdir('/home/user/Coq-BBB4')
import emit_lapcert as EL, nestcert as NC, lapcert as LC
from emit_interleave import parse
from mirror_common import mirror_spec
LAB='ABCD'; K=6

def families(mid, ENCDATA, ENCS, want_run, maxtail=3):
    hits={}
    for (q,l,r) in mid:
        for name in ENCS:
            d=ENCDATA[name]
            if d['obS']!=0: continue
            A,B,C=tuple(d['uD']),tuple(d['uS']),tuple(d['soD'])
            for k in range(maxtail+1):
                if k>len(l)-1: break
                head,tl=(l[:len(l)-k],l[len(l)-k:]) if k else (l,())
                v=NC.decode(head,A,B,C)
                if v is not None: hits.setdefault((name,q,tl,r),[]).append(v)
    return [(k,v) for k,v in hits.items() if v==want_run]

tal=collections.Counter()
for spec0 in [l.strip() for l in open(sys.argv[1]) if l.strip()][:int(sys.argv[2])]:
    done=False
    for mirrored in (False,True):
        if done: break
        dspec=mirror_spec(spec0) if mirrored else spec0
        for (edge,tail,p0,enc,far) in EL.anchors(dspec):
            tab=parse(dspec); st0=LAB.index(edge); encf=EL.ENC[enc]
            tail,far=tuple(tail),tuple(far)
            try: keys=NC.inner_keys(tab,EL.ENCDATA,EL.ENCS,st0,encf,tail,far,K=K)
            except Exception: keys=[]
            if not keys: continue
            name_in,st_in,ti,fi=keys[0]
            encin=EL.ENC[name_in]
            # replay the phase, recording blank-head configs, and note where
            # the inner counter first reaches its all-ones fill
            cfg=(st0,tuple(encf(2**K-1))+tail,0,far)
            want=(st0,LC.rstrip0(tuple(encf(2**K))+tail),0,LC.rstrip0(far))
            fillw=LC.rstrip0(tuple(encin(2**K-1))+tuple(ti)); fillf=LC.rstrip0(tuple(fi))
            pre,post,seen_fill=[],[],False
            for t in range(1,400000):
                try: cfg=LC.wstep(tab,False,False,cfg)
                except LC.Halt: break
                q,l,h,r=cfg
                if q==want[0] and h==0 and LC.rstrip0(l)==want[1] and LC.rstrip0(r)==want[3]: break
                if h==0:
                    rec=(q,LC.rstrip0(l),LC.rstrip0(r))
                    if not seen_fill and q==st_in and rec[1]==fillw and rec[2]==fillf:
                        seen_fill=True
                    (post if seen_fill else pre).append(rec)
            wr=list(range(2**(K-1),2**K))
            f2=families(post,EL.ENCDATA,EL.ENCS,wr)
            tal['second count' if f2 else 'none after fill']+=1
            print('%-42s in1=%s@%s  after-fill configs=%4d  SECOND family: %s'
                  % (spec0,name_in,LAB[st_in],len(post),
                     ('%s@%s tail=%s far=%s'%(f2[0][0][0],LAB[f2[0][0][1]],f2[0][0][2],f2[0][0][3]))
                      if f2 else 'NONE'), flush=True)
            done=True; break
    if not done: tal['no-key']+=1
print()
for k,v in tal.most_common(): print('%4d  %s'%(v,k))
