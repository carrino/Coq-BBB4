"""HY3 hold probe (untrusted, SCOPING_INSTR.md 7.4.HY3): runs hy2_batch's
finder and, at every top word its counter family learns, runs one counter
half from Dm^j ++ X (j = 2, 3).  A 'hold' is a counter half that leaves the
low digits Dm^j in place (the two-lap overflow of 7.4.HY2's residue).
Prints (b, D, X, exit, prefix, held word) per row that shows one.

    python3 tools/closeouttr/hy3/hold_probe.py ROWS.txt > hold_probe.txt
"""
import sys, signal
import os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import hy2_batch as H2, hy_batch as H
from multiprocessing import Pool
def det(spec):
    found=[]
    def lc(tab_, F, q, h, Lpre, Rpre, w, Rpost, m, ex0):
        b, D = F['b'], F['D']; Dm, D0 = tuple(D[b-1]), tuple(D[0])
        for tv,X in F['T'].items():
            X=tuple(X); outs=[]
            for j in (2,3):
                anc=(q, tuple(Lpre)+Dm*j+X, h, tuple(Rpre)+tuple(w)*(m+8)+tuple(Rpost))
                ex=H2.first_exit(tab_, anc, len(Rpre)+m*len(w))
                outs.append(ex)
            if None in outs: continue
            # hold: exit left side contains Dm^j contiguous after some prefix, for both j, and suffix equal
            for (j,ex) in zip((2,3),outs):
                pass
            L2,L3=outs[0][2],outs[1][2]
            for pl in range(0,12):
                if L2[pl:pl+2*len(Dm)]==Dm*2 and L3[pl:pl+3*len(Dm)]==Dm*3 and H.rstrip0(L2[pl+2*len(Dm):])==H.rstrip0(L3[pl+3*len(Dm):]) and L2[:pl]==L3[:pl]:
                    found.append((b,D,X,outs[0][:2],L2[:pl],H.rstrip0(L2[pl+2*len(Dm):])))
                    break
        return orig(tab_, F, q, h, Lpre, Rpre, w, Rpost, m, ex0)
    orig=H2.learn_cycle
    H2.learn_cycle=lc
    def _al(*a): raise TimeoutError()
    signal.signal(signal.SIGALRM,_al)
    signal.alarm(240)
    try:
        for mir in (False,True):
            tab=H.parse(spec)
            if mir: tab=H.mirror(tab)
            try: H2.find_dir(tab)
            except Exception as e: pass
    except BaseException: pass
    signal.alarm(0)
    return spec, found[:2]
if __name__=='__main__':
    rows=open(sys.argv[1]).read().split()
    with Pool(4, maxtasksperchild=1) as p:
        for s,f in p.imap_unordered(det, rows):
            print(s, len(f), f[:1], flush=True)
