"""BLC2 survey (UNTRUSTED measurement, SCOPING_INSTR.md 7.4.BLC2): the tape of each row at 8e6
steps, run-length coded, and the block lists in it (unit, length, neighbour ratios).

    cc -O2 -o /tmp/bl_sim tools/closeouttr/bl/bl_sim.c
    python3 tools/closeouttr/blc2/survey.py ROWS.txt > survey.tsv
"""
import sys,re,subprocess,collections
from multiprocessing import Pool
SIM = __import__('os').environ.get('BL_SIM', '/tmp/bl_sim')
UNITS=['1','0','10','01','110','100','011','001','1100','0011','0111','1110','1000','0001','0110','1001']
def rle(s):
    # greedy: at each position the unit covering the longest run (>=3 copies)
    out=[];i=0;lit=''
    while i<len(s):
        best=None
        for u in UNITS:
            n=0
            while s.startswith(u,i+n*len(u)): n+=1
            if n>=3 and len(u)*n>=6 and (best is None or len(u)*n>len(best[0])*best[1]): best=(u,n)
        if best:
            if lit: out.append(('L',lit)); lit=''
            out.append(('B',)+best); i+=len(best[0])*best[1]
        else: lit+=s[i]; i+=1
    if lit: out.append(('L',lit))
    return out
def lists(r):
    # maximal runs of blocks of one unit with separators <= 4 cells
    res=[];cur=[]
    for x in r:
        if x[0]=='B':
            if cur and cur[-1][0]==x[1]: cur.append((x[1],x[2]))
            else:
                if len(cur)>=4: res.append(cur)
                cur=[(x[1],x[2])]
        elif len(x[1])>4:
            if len(cur)>=4: res.append(cur)
            cur=[]
    if len(cur)>=4: res.append(cur)
    return res
def one(spec):
    out=subprocess.run([SIM,spec,'8000001','8000000'],capture_output=True,text=True).stdout
    tape=''
    for l in out.split('\n'):
        p=l.split()
        if p and p[0]=='T': tape=p[2].strip('0') if len(p)>2 else ''
    r=rle(tape); L=lists(r)
    desc=[]
    for li in L:
        ns=[n for u,n in li]
        rat=[round(max(a,b)/max(1,min(a,b)),1) for a,b in zip(ns,ns[1:])]
        desc.append('%s:%d:%s'%(li[0][0],len(li),','.join(map(str,rat[:6]))))
    comp=' '.join(('%s^%d'%(x[1],x[2]) if x[0]=='B' else x[1]) for x in r)
    return spec,len(tape),len(r),desc,comp[:220]
if __name__=='__main__':
    rows=[l.split()[0] for l in open(sys.argv[1]) if l.strip()]
    with Pool(4) as p:
        for spec,n,nr,desc,comp in p.imap(one,rows):
            print('%s\t%d\t%d\t%s\t%s'%(spec,n,nr,'|'.join(desc) or '-',comp),flush=True)
