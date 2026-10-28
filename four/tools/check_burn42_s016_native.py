"""Finite exact S016 token controls; universal Coq closure supplies proof credit."""
import argparse,itertools,json
from pathlib import Path
import burn10_marker_history_pilot as helper
ROOT=helper.ROOT;PREFIX=ROOT/'research/burn42-s016'
MACHINE='1LB0RA0LB2RB_3RB3LA1RA1RA';TABLE=[5,2,1,11,15,12,6,6]
TOKENS=[list(map(int,s))for s in['13312','012','312','13313312']]
PARENT='4b43d3e48f8ea0fd874c2d357c7741dc0650213944537d03e16f682c5ebf57cf'
FW=list(map(int,'31313'))
def enc(ts):return[s for t in ts for s in TOKENS[t]]
def F(ts):
    if not ts:return[0,1]
    h,*r=ts
    return[0]+F(r)if h==0 else[3]+r if h==1 else[1]+F(r)if h==2 else[0,0,2]+r

def cost(ts):
    if not ts:return 30
    h,*r=ts
    return 38+cost(r)if h==0 else 10 if h==1 else 26+cost(r)if h==2 else 46

def back(q,l,r):return q,l[1:],l[0]if l else 0,r
def cut(ts):return 0,enc(ts)+[3],0,[]
def run(table,c,n):
    q,l,h,r=c
    for _ in range(n):
        z=table[4*q+h];w,d,q=z//4,z//2%2,z%2
        if d:l=[w]+l;h,r=(r[0]if r else 0),r[1:]
        else:r=[w]+r;h,l=(l[0]if l else 0),l[1:]
    return q,l,h,r

def parse(w):
    if not w or w[-1]!=3:return None
    w=w[:-1];ts=[]
    while w:
        i=next((i for i,t in enumerate(TOKENS)if w[:len(t)]==t),None)
        if i is None:return None
        ts.append(i);w=w[len(TOKENS[i]):]
    return ts

def nextcut(ts):
    c=cut(ts)
    for t in range(1,5001):
        c=run(TABLE,c,1);q,l,h,r=c
        if q==h==0 and not r:
            out=parse(l)
            if out and out[0]in[0,3]:return t,out
    raise AssertionError(('No guarded return in finite control budget',ts))

def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--check',action='store_true');args=parser.parse_args()
    checkpoint=ROOT/'research/state-holdouts-78.txt';assert checkpoint.read_text().splitlines()[15]==MACHINE
    table=helper.codes(MACHINE);assert table==TABLE and sum(c*17**i for i,c in enumerate(table))==2625202922
    programs=PREFIX.with_name(PREFIX.name+'-programs.json');data=json.loads(programs.read_text())
    assert data['metadata_revision']==1 and data['machine']==MACHINE and data['table']==TABLE
    assert data['tokens']==['13312','012','312','13313312']and data['normalizer_parent_sha256']==PARENT and len(data['programs'])==34
    normalizer=ROOT/'proof-sources/burn42-s016/Normalizer.v';assert helper.sha(normalizer)==PARENT
    contexts=[[]]+[[s]for s in range(4)]+[list(s)for s in itertools.product(range(4),repeat=2)]
    words=[list(ts)for n in range(5)for ts in itertools.product(range(4),repeat=n)];assert len(words)==341
    counts={k:0 for k in['programs','all_variant_normalizers','guarded_returns','actual_entry','actual_orbit','negative_guards','identity_controls']}
    for row in data['programs']:
        lp,rp=list(map(int,row['left'])),list(map(int,row['right']))
        dl,dr=list(map(int,row['target_left'])),list(map(int,row['target_right']))
        for l in contexts:
            source=(0,lp+l,0,[])if row['source_kind']=='cut'else back(1,lp+l,rp)if row['source_kind']=='back'else(0,lp+l,3,rp)
            target=back(1,l,dr)if row['target_kind']=='back'else(0,dl+l,0,[])
            assert run(TABLE,source,row['steps'])==target,row['name'];counts['programs']+=1
    for variant in[1,2,6]:
        tm=TABLE[:];tm[6]=variant
        for ts in words:
            for r in contexts:
                assert run(tm,back(1,enc(ts)+[3],[0]+FW+r),cost(ts))==(0,enc(F(ts))+[3],3,r);counts['all_variant_normalizers']+=1
    for ts in words:
        for h in[0,3]:
            t,out=nextcut([h]+ts);assert t>0 and out[0]in[0,3];counts['guarded_returns']+=1
    assert run(TABLE,(0,[],0,[]),56)==cut([0,1]);counts['actual_entry']+=1
    ts=[0,1];elapsed=56
    for _ in range(16):t,ts=nextcut(ts);elapsed+=t
    assert run(TABLE,(0,[],0,[]),elapsed)==cut(ts);counts['actual_orbit']+=1
    assert run(TABLE,back(1,TOKENS[3]+[3],list(map(int,'0333031'))),98)!=back(1,[3],[0]+FW+list(map(int,'313103131')));counts['negative_guards']+=1
    assert run(TABLE,back(1,[],[0]+FW+[3,1]),30)!=(0,enc(F([]))+[3],3,[3,1]);counts['negative_guards']+=1
    wrong_zero='1LB0RA0LB2RB_3RB3LA0RA1RA';wrong_left='1LB0RA0LB2RB_3RB3LA0LB1RA'
    for machine in[wrong_zero,wrong_left]:
        wrong=helper.codes(machine);assert wrong!=TABLE
        assert run(wrong,(0,TOKENS[0]+[3],0,[]),120)!=back(1,[3],[0]+FW+list(map(int,'133031')));counts['identity_controls']+=1
    prior=PREFIX.with_name(PREFIX.name+'-prior-state-holdouts.txt');rows=prior.read_text().splitlines();assert len(rows)==3 and MACHINE in rows
    sources=[Path(__file__),Path(helper.__file__),ROOT/'tools/generate_pipeline_examples.py']
    stable=dict(metadata_revision=1,scope='Finite controls only; no universal proof credit.',rows=[dict(machine=MACHINE,code=2625202922)],controls=counts,
        frozen_checkpoint_sha256=helper.sha(checkpoint),prior_remaining_count=3,prior_remaining_report=str(prior.relative_to(ROOT)),prior_remaining_sha256=helper.sha(prior),
        normalizer_parent_sha256=PARENT,normalizer_local_copy=str(normalizer.relative_to(ROOT)),maximum_token_length=4,context_max_length=2,
        invariant='A0 right blank; nearest-first left enc(a::ts)3 or enc(d::ts)3, arbitrary finite token ts',entry_steps=56,entry_tokens=[0,1],
        return_claim='For every guarded word, some positive finite return is guarded; all-variant shared F normalization is universal in Coq.',
        programs_report=str(programs.relative_to(ROOT)),programs_sha256=helper.sha(programs),KD_continuation='313303131',KD_wrong_continuation_negative='313103131',
        actual_orbit=dict(returns=16,total_steps=elapsed),identity_negative_controls=[wrong_zero,wrong_left],source_sha256={str(p.relative_to(ROOT)):helper.sha(p)for p in sources})
    report=PREFIX.with_name(PREFIX.name+'-native.json')
    if args.check:
        assert json.loads(report.read_text())==stable;print('S016 exact headers, copied normalizer and guarded token returns replayed; no proof credit.')
    else:
        if report.exists():raise ValueError('Frozen native report exists; use --check')
        report.write_text(json.dumps(stable,indent=2,sort_keys=True)+'\n');print('S016 native controls passed:',counts)
if __name__=='__main__':main()
