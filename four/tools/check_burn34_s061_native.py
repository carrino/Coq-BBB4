"""Finite S061 recursive-grammar controls; universal Coq proofs provide credit."""
import argparse,sys,json,itertools
from pathlib import Path
import burn10_marker_history_pilot as helper
ROOT=helper.ROOT
PREFIX=ROOT/'research/burn34-s061'
MACHINE='1LB2LB3RA1RA_3RB2LA1RA3LB'
sys.path.insert(0,'four/tools');from generate_pipeline_examples import codes
T=codes(MACHINE);assert T==[5,9,14,6,15,8,6,13]
def ew(e):
 t=e[0];c=e[1]if len(e)>1 else None
 return ['131','1113',lambda:'11113'+ow(c),lambda:'13331'+ne(c),lambda:'11131'+ne(c),lambda:'13313'+ow(c)][t]()if t>=2 else['131','1113'][t]
def ow(o):
 t=o[0];c=o[1]if len(o)>1 else None
 return ['1','1313',lambda:'11113'+ew(c),lambda:'13131'+ne(c),lambda:'11133'+ow(c),lambda:'13113'+ow(c)][t]()if t>=2 else['1','1313'][t]
def ne(e):
 t=e[0];c=e[1]if len(e)>1 else None
 return ['311','3331',lambda:'33331'+no(c),lambda:'31331'+ne(c),lambda:'33311'+ne(c),lambda:'31313'+ow(c)][t]()if t>=2 else['311','3331'][t]
def no(o):
 t=o[0];c=o[1]if len(o)>1 else None
 return ['331','3113',lambda:'33331'+ne(c),lambda:'31131'+ne(c),lambda:'33313'+ow(c),lambda:'31113'+ow(c)][t]()if t>=2 else['331','3113'][t]
def ec(e):return [3,7,lambda:10+oc(e[1]),3,7,3][e[0]]()if e[0]==2 else[3,7,0,3,7,3][e[0]]
def oc(o):return 10+ec(o[1])if o[0]==2 else[7,3,0,3,7,3][o[0]]
def dc(e):return 10+dc(e[1])if e[0]==4 else[7,13,11,5,0,5][e[0]]
def on(o):
 t=o[0];return [(0,),(1,),lambda:(3,o[1]),lambda:(4,o[1]),lambda:(5,o[1]),lambda:(2,o[1])][t]()if t>=2 else[(0,),(1,)][t]
def en(e):
 t=e[0];return [(1,),(4,(0,)),lambda:(2,on(e[1])),lambda:(3,e[1]),lambda:(4,en(e[1])),lambda:(5,e[1])][t]()if t>=2 else[(1,),(4,(0,))][t]
def run(c,n):
 q,l,h,r=c
 for _ in range(n):
  z=T[q*4+h];w,d,q=z//4,z//2%2,z%2
  if d:l=[w]+l;h,r=(r[0]if r else 0),r[1:]
  else:r=[w]+r;h,l=(l[0]if l else 0),l[1:]
 return q,l,h,r
def front(q,l,r):return q,l,r[0]if r else 0,r[1:]
def back(q,l,r):return q,l[1:],l[0]if l else 0,r
def conv(w):return list(map(int,w))
def trees(depth):
    es=[(0,),(1,)];os=[(0,),(1,)]
    for _ in range(depth):
        es,os=([(0,),(1,)]+[(t,c)for t in range(2,6)for c in(os if t in[2,5]else es)],
               [(0,),(1,)]+[(t,c)for t in range(2,6)for c in(es if t in[2,3]else os)])
    return es,os

def mainconf(kind,j,x):return 0,[3]*(2*j+(2 if kind=='e'else 1))+conv(ew(x)if kind=='e'else ow(x)),0,[]
def cost(kind,j,x):
    k=2*j+(2 if kind=='e'else 1)
    return 4*k+(ec(x)+dc(x)+3 if kind=='e'else oc(x)+4)
def cycle_cost(j,o):return cost('o',j,o)+cost('e',j,on(o))
def main():
    global T
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--check',action='store_true');args=parser.parse_args()
    checkpoint=ROOT/'research/state-holdouts-78.txt';assert checkpoint.read_text().splitlines()[60]==MACHINE
    assert T==[5,9,14,6,15,8,6,13] and sum(c*17**i for i,c in enumerate(T))==5491873516
    es,os=trees(3);assert len(es)==len(os)==170
    contexts=[[]]+[[s]for s in range(4)]+[list(s)for s in itertools.product(range(4),repeat=2)]
    counts={k:0 for k in ['even_normalizers','odd_normalizers','double_normalizers','even_returns','odd_returns','two_return_cycles','actual_entry','actual_orbit','negative_guards','identity_controls']}
    for kind,xs in[('e',es),('o',os)]:
        for x in xs:
            w,z,c=(ew(x),ne(x),ec(x))if kind=='e'else(ow(x),no(x),oc(x))
            assert z.startswith('3')
            if kind=='o':assert ew(on(x))=='1'+z[1:]
            for r in contexts:
                assert run(back(1,conv(w),r),c)==front(0,conv(z),r);counts['even_normalizers'if kind=='e'else'odd_normalizers']+=1
                if kind=='e':
                    assert run(back(1,conv(z),r),dc(x))==front(0,conv(ow(en(x))),r);counts['double_normalizers']+=1
            for j in range(4):
                target=mainconf('o',j+1,en(x))if kind=='e'else mainconf('e',j,on(x))
                assert run(mainconf(kind,j,x),cost(kind,j,x))==target;counts['even_returns'if kind=='e'else'odd_returns']+=1
                if kind=='o':
                    assert run(mainconf('o',j,x),cycle_cost(j,x))==mainconf('o',j+1,en(on(x)));counts['two_return_cycles']+=1
    assert run((0,[],0,[]),5)==mainconf('o',0,(0,));counts['actual_entry']+=1
    o=(0,);elapsed=5
    for j in range(64):elapsed+=cycle_cost(j,o);o=en(on(o))
    assert run((0,[],0,[]),elapsed)==mainconf('o',64,o);counts['actual_orbit']+=1
    # The grammar and prefix parity are semantic guards, not arbitrary binary words.
    assert run((0,[3,3,1,3,1,3],0,[]),15)!=(0,[3,3,3,1,1,1,3],0,[]);counts['negative_guards']+=1
    assert run(back(1,[3],[]),7)!=front(0,[3,3,1],[]);counts['negative_guards']+=1
    wrong_A1='1LB2LA3RA1RA_3RB2LA1RA3LB';wrong_B3='1LB2LB3RA1RA_3RB2LA1RA3RB'
    for machine in(wrong_A1,wrong_B3):
        wrong=codes(machine);assert wrong!=T
        # Use the same complete-table evaluator with only its table rebound locally.
        frozen=T;T=wrong
        result=run(mainconf('o',0,(0,)),36)
        T=frozen
        assert result!=mainconf('o',1,(1,));counts['identity_controls']+=1
    prior=PREFIX.with_name(PREFIX.name+'-prior-state-holdouts.txt');priorrows=prior.read_text().splitlines();assert len(priorrows)==8 and MACHINE in priorrows
    sources=[Path(__file__),Path(helper.__file__),ROOT/'tools/generate_pipeline_examples.py']
    stable=dict(metadata_revision=1,scope='Finite synthetic grammar controls only; no universal proof credit.',rows=[dict(machine=MACHINE,code=5491873516)],controls=counts,
        frozen_checkpoint_sha256=helper.sha(checkpoint),prior_remaining_count=8,prior_remaining_report=str(prior.relative_to(ROOT)),prior_remaining_sha256=helper.sha(prior),
        grammar_tree_depth=3,even_trees=len(es),odd_trees=len(os),context_max_length=2,entry_steps=5,
        odd_return_cost='4*(2*j+1)+oc(o)+4',even_return_cost='4*(2*j+2)+ec(e)+dc(e)+3',
        invariant='A0 right blank; left 3^(2*j+1) O(o) or 3^(2*j+2) E(e), mutually recursive finite grammar trees',
        actual_orbit=dict(two_return_cycles=64,total_steps=elapsed),
        boundary_guard='Only matching-parity grammar words are asserted; arbitrary binary words may escape in B3.',
        identity_negative_controls=[wrong_A1,wrong_B3],source_sha256={str(p.relative_to(ROOT)):helper.sha(p)for p in sources})
    report=PREFIX.with_name(PREFIX.name+'-native.json')
    if args.check:
        assert json.loads(report.read_text())==stable;print('S061 grammar normalizers, both parity returns and actual blank controls replayed; no proof credit.')
    else:
        if report.exists():raise ValueError('Frozen native report exists; use --check')
        report.write_text(json.dumps(stable,indent=2,sort_keys=True)+'\n');print('S061 native controls passed:',counts)
if __name__=='__main__':main()
