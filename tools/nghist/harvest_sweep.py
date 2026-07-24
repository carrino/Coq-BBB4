#!/usr/bin/env python3
"""Sweep the unboarded census residue with the NGramHist prover (UNTRUSTED).
Emits per-machine results; a second pass emits staged Coq files.
Dedup: census_residue.txt minus the staged-not-wired manifests.
Usage: harvest_sweep.py sweep   (writes results tsv)
       harvest_sweep.py emit     (writes staged files + manifest from tsv)
"""
import sys, os, csv
from concurrent.futures import ProcessPoolExecutor
import nghist_prove as P

ROOT="/home/user/Coq-BBB4"
RES=ROOT+"/tools/census_residue.txt"
OUTDIR=ROOT+"/theories/Machines/NGHStage"
MANI=ROOT+"/tools/nghstage_manifest.tsv"
RESULTS="/home/user/Coq-BBB4/tools/nghist/sweep_results.tsv"
PARAMS=[(2,2,40,20000),(4,2,40,20000)]   # (k,n,t,fuel) escalation
MAXCTX=1200

def col0(path, hdr=False):
    out=set()
    if not os.path.exists(path): return out
    for i,l in enumerate(open(path)):
        if hdr and i==0: continue
        l=l.strip()
        if not l or l.startswith('#'): continue
        out.add(l.split('\t')[0])
    return out

def target_list():
    res=[l.strip() for l in open(RES) if l.strip()]
    ded=set()
    for f,h in [("tools/listc_v5_manifest.tsv",True),("tools/listc_v5b_manifest.tsv",True)]:
        ded|=col0(ROOT+"/"+f,h)
    return [m for m in res if m not in ded], len(res), len(ded)

def try_prove(m):
    for (k,n,t,fuel) in PARAMS:
        try:
            r=P.prove(m,k,n,t,fuel)
        except Exception:
            r=None
        if r is not None and r['nctx']<=MAXCTX:
            return (m,'OK',k,n,t,fuel,r['nctx'])
    return (m,'FAIL',0,0,0,0,0)

def sweep():
    tgt,nres,nded=target_list()
    sys.stderr.write("residue=%d dedup=%d target=%d\n"%(nres,nded,len(tgt)))
    n=int(os.environ.get('NGH_LIMIT', len(tgt)))
    tgt=tgt[:n]
    ok=0
    with open(RESULTS,'w') as f, ProcessPoolExecutor(max_workers=2) as ex:
        for i,res in enumerate(ex.map(try_prove, tgt, chunksize=8)):
            m,st,k,nn,t,fuel,nctx=res
            if st=='OK':
                ok+=1
                f.write("%s\t%d\t%d\t%d\t%d\t%d\n"%(m,k,nn,t,fuel,nctx))
            if (i+1)%200==0:
                f.flush(); sys.stderr.write("  %d/%d swept, %d boardable\n"%(i+1,len(tgt),ok))
    sys.stderr.write("DONE %d/%d boardable\n"%(ok,len(tgt)))

def emit():
    rows=[l.rstrip('\n').split('\t') for l in open(RESULTS) if l.strip()]
    os.makedirs(OUTDIR, exist_ok=True)
    man=open(MANI,'w'); man.write("machine\ttheorem\tfile\tk\tn\tt\tfuel\tnctx\n")
    per=100
    files=[]
    for fi in range((len(rows)+per-1)//per):
        chunk=rows[fi*per:(fi+1)*per]
        fname="NGH_%02d"%fi
        body=[P.HEADER]
        thms=[]
        for j,(m,k,n,t,fuel,nctx) in enumerate(chunk):
            r=P.prove(m,int(k),int(n),int(t),int(fuel))
            idx=fi*per+j
            nm='%05d'%idx
            btext,thm=P.emit(m,r,idx)   # body only, no header
            body.append(btext)
            thms.append((thm,'tm_h_'+nm))
            man.write("%s\t%s\t%s.v\t%s\t%s\t%s\t%s\t%s\n"%(m,thm,fname,k,n,t,fuel,nctx))
        # per-file Forall (nested Forall_cons ... (Forall_nil ...))
        lst="ngh_%02d"%fi
        body.append('Definition {} : list TM :=\n  [{}].'.format(lst,
                    ';\n   '.join(tm for _,tm in thms)))
        term="Forall_nil NeverQuasiHaltsSt"
        for thm,_ in reversed(thms):
            term="Forall_cons _ {} ({})".format(thm, term)
        body.append('Lemma {}_nqh : Forall NeverQuasiHaltsSt {}.'.format(lst,lst))
        body.append('Proof. unfold {}. exact ({}). Qed.'.format(lst, term))
        open(OUTDIR+"/"+fname+".v",'w').write('\n\n'.join(body)+'\n')
        files.append(fname)
    man.close()
    sys.stderr.write("emitted %d files, %d machines\n"%(len(files),len(rows)))
    print('\n'.join(files))


# ================= QHBound / wrap harvest =================
QRESULTS="/home/user/Coq-BBB4/tools/nghist/sweep_qh_results.tsv"
QOUTDIR=ROOT+"/theories/Machines/NGHWStage"
QMANI=ROOT+"/tools/nghwstage_manifest.tsv"
QPARAMS=[(2,2,20000),(4,2,20000)]   # (k,n,fuel)

def try_prove_qh(m):
    for (k,n,fuel) in QPARAMS:
        try: r=P.prove_qh(m,k,n,fuel)
        except Exception: r=None
        if r is not None and r['nctx']<=MAXCTX:
            return (m,r['q'],r['s'],k,n,r['t'],fuel,r['nctx'])
    return None

def sweepqh():
    tgt,nres,nded=target_list()
    sys.stderr.write("target=%d\n"%len(tgt))
    ok=0
    with open(QRESULTS,'w') as f, ProcessPoolExecutor(max_workers=2) as ex:
        for i,r in enumerate(ex.map(try_prove_qh, tgt, chunksize=8)):
            if r:
                ok+=1
                f.write("%s\t%s\t%d\t%d\t%d\t%d\t%d\t%d\n"%r)
            if (i+1)%200==0: f.flush(); sys.stderr.write("  %d/%d, %d boardable\n"%(i+1,len(tgt),ok))
    sys.stderr.write("DONE %d/%d boardable\n"%(ok,len(tgt)))

def emitqh():
    rows=[l.rstrip('\n').split('\t') for l in open(QRESULTS) if l.strip()]
    os.makedirs(QOUTDIR, exist_ok=True)
    man=open(QMANI,'w'); man.write("machine\ttheorem\tfile\tquiet_state\ts\tk\tn\tt\tfuel\tnctx\n")
    per=100
    for fi in range((len(rows)+per-1)//per):
        chunk=rows[fi*per:(fi+1)*per]; fname="NGHW_%02d"%fi
        body=[P.HEADER_QH]; thms=[]
        for j,(m,qst,s,k,n,t,fuel,nctx) in enumerate(chunk):
            r=P.prove_qh(m,int(k),int(n),int(fuel))
            idx=fi*per+j; nm='%05d'%idx
            btext,thm,tmn=P.emit_qh(m,r,idx)
            body.append(btext); thms.append((thm,tmn))
            man.write("%s\t%s\t%s.v\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n"%(m,thm,fname,qst,s,k,n,t,fuel,nctx))
        lst="nghw_%02d"%fi
        body.append('Definition {} : list TM :=\n  [{}].'.format(lst,';\n   '.join(tm for _,tm in thms)))
        term="Forall_nil iqh"
        for thm,_ in reversed(thms): term="Forall_cons _ {} ({})".format(thm,term)
        body.append('Lemma {}_all : Forall iqh {}.'.format(lst,lst))
        body.append('Proof. unfold {}. exact ({}). Qed.'.format(lst,term))
        open(QOUTDIR+"/"+fname+".v",'w').write('\n\n'.join(body)+'\n')
    man.close(); sys.stderr.write("emitted %d files, %d machines\n"%((len(rows)+per-1)//per,len(rows)))

if __name__=='__main__':
    m={'sweep':sweep,'emit':emit,'sweepqh':sweepqh,'emitqh':emitqh}
    m[sys.argv[1]]()
