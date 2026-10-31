"""Finite controls for the binary trio's universal counter proof; no proof credit."""
import argparse
import hashlib
import itertools
import json
from pathlib import Path
import burn10_marker_history_pilot as helper

ROOT=helper.ROOT
REPORT=ROOT/'research/burn19-binary-trio-native.json'
MACHINES=['1LB0LA0RB3LB_3RB1LB3RA2LB','1LB0LA0RB3LB_3RB2RA3RA2LB','1LB0LA0RB3LB_3RB3LB3RA2LB']

def enc(ds):return[s for d in ds for s in (3,3 if d else 0)]
def value(ds):return sum(d*2**i for i,d in enumerate(ds))
def front(q,l,r):return q,l,r[0]if r else 0,r[1:]
def back(q,l,r):return q,l[1:],l[0]if l else 0,r

def run(table,conf,n):
    q,l,h,r=conf
    for _ in range(n):
        cell=table[4*q+h];w,d,q=cell//4,cell//2%2,cell%2
        if d:l=[w]+l;h,r=(r[0]if r else 0),r[1:]
        else:r=[w]+r;h,l=(l[0]if l else 0),l[1:]
    return q,l,h,r

def valid(v,ds,kind):
    z=value(ds)
    return {'0':z%3==0,'1':z%3==1,'3':len(ds)%2==1,
            '21':len(ds)%2==0 if v==0 else z%3==2,'23':z%3==1}[kind]

def classify(v,conf):
    q,l,h,r=conf
    if q or len(l)%2 or any(l[j]!=3 or l[j+1]not in(0,3)for j in range(0,len(l),2)):return False
    ds=[int(l[j]==3)for j in range(1,len(l),2)]
    if h==2 and r and r[0]in(1,3):kind='2'+str(r[0]);r=r[1:]
    elif h in(0,1,3):kind=str(h)
    else:return False
    return not any(r)and valid(v,ds,kind)

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check',action='store_true');args=parser.parse_args()
    contexts=[[]]+[[s]for s in range(4)]+[list(s)for s in itertools.product(range(4),repeat=2)]
    counts=dict(left_true=0,right_pairs=0,increment=0,overflow_single=0,overflow_double=0)
    normalized=[0,0,0];max_cost=0
    for v,machine in enumerate(MACHINES):
        table=helper.codes(machine)
        for n in range(8):
            for l,r in itertools.product(contexts,repeat=2):
                assert run(table,back(1,enc([True]*n)+l,r),2*n)==back(1,l,[2]*(2*n)+r)
                assert run(table,front(0,l,[2]*(2*n)+r),2*n)==front(0,enc([False]*n)+l,r)
                counts['left_true']+=1;counts['right_pairs']+=1
            for r in contexts:
                for tail in itertools.product((False,True),repeat=3):
                    ds=[True]*n+[False]+list(tail);out=[False]*n+[True]+list(tail)
                    assert run(table,back(1,enc(ds),r),4*n+3)==front(0,enc(out),r)
                    counts['increment']+=1
                for h in range(4):
                    assert run(table,back(1,enc([True]*(n+1)),[h]+r),4*(n+1))==front(0,enc([False]*n+[True]),[2,h]+r)
                    assert run(table,back(1,enc([True]*n),[2,h]+r),4*n+2)==front(0,enc([False]*n+[True]),[h]+r)
                    counts['overflow_single']+=1;counts['overflow_double']+=1
        for n in range(9):
            for ds in itertools.product((False,True),repeat=n):
                for kind in('0','1','3','21','23'):
                    if not valid(v,ds,kind):continue
                    conf=front(0,enc(ds),list(map(int,kind)))
                    for cost in range(1,1000):
                        conf=run(table,conf,1)
                        if classify(v,conf):break
                    else:raise ValueError(('No normalized return',v,ds,kind))
                    normalized[v]+=1;max_cost=max(max_cost,cost)
        conf=run(table,front(0,enc([False]),[1]),8)
        assert conf[0]==1 and conf[2]==0 and not any(conf[3])
    assert normalized==[1026,851,851]
    sources=[Path(__file__),Path(helper.__file__),ROOT/'tools/generate_pipeline_examples.py']
    stable=dict(scope='Finite synthetic controls only; no proof credit.',
        rows=[dict(machine=m,code=sum(c*17**i for i,c in enumerate(helper.codes(m))))for m in MACHINES],
        macro_controls=counts,context_max_length=2,max_carry=8,normalized_bit_length=8,
        normalized_controls=normalized,maximum_normalized_return_cost=max_cost,
        checksum='head0: value mod3=0; head1/head23: value mod3=1; head3: odd length; head21: even length for S001, value mod3=2 for S002/S003',
        excluded_corner='head1 with bit word [false] reaches B on blank with a blank right tail after8 steps',
        source_sha256={str(p.relative_to(ROOT)):helper.sha(p)for p in sources})
    if args.check:
        assert json.loads(REPORT.read_text())==stable
        print('Binary-trio native macro and normalized controls replayed; no proof credit.')
    else:
        if REPORT.exists():raise ValueError('Frozen native report exists; use --check')
        REPORT.write_text(json.dumps(stable,indent=2,sort_keys=True)+'\n')
        print('Binary-trio native controls passed; no proof credit.')
if __name__=='__main__':main()
