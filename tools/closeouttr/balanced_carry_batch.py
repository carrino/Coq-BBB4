#!/usr/bin/env python3
"""Emit/replay AST140: alternating-carry finite reachability plus FuelMix.

The certificate data lives in the batch; the small JSON records its hash,
parameters and state renaming. --find reruns the untrusted finder.
"""
import argparse
import hashlib
import itertools
import json
from pathlib import Path
import tempfile
import cbt
from period3_batch import row, table

HERE=Path(__file__).resolve().parent
DATA=HERE/'balanced_carry_ast.json'
BATCH=140

def emit(records):
    pre,entries=[],[]
    for i,r in enumerate(records):
        suffix=f'AST_{BATCH}_{i:04d}'
        p,flip=r['p'],r['flip']
        assert sorted(p)==list(range(4))
        assert r['failed']==[[p[1],1]] and r['mirrored'] and r['t']==0
        src,dst=table(r['source']),table(r['spec'])
        for q,s in itertools.product(range(4),range(2)):
            w,d,t=src[2*q+s]
            if flip:d='L' if d=='R' else 'R'
            assert dst[2*p[q]+s]==(w,d,p[t])
        target=f'(St{chr(65+p[1])},S1)'
        perm=' | '.join(f'St{chr(65+q)}=>St{chr(65+x)}' for q,x in enumerate(p))
        pre.append(f'''Definition cert_{suffix}:Instr->list fmxcomp*list positive :=
{r['cert']}.
Definition source_{suffix} := row_to_tm {row(r['source'])}.
Definition perm_{suffix}(q:St):St := match q with {perm} end.
Definition skip_{suffix}(t:Instr):bool := instr_eqb t {target}.''')
        proof=f'''assert(Hhit:finite_instr_hit(row_to_tm r_{suffix}){target}).
  {{ apply(finite_instr_conjugate source_{suffix} _ perm_{suffix} {str(flip).lower()} (StB,S1)).
    - intros[] [];reflexivity.
    - intros[];first[exists StA;reflexivity|exists StB;reflexivity|
                    exists StC;reflexivity|exists StD;reflexivity].
    - apply ac_finite;reflexivity. }}
  assert(Htotal:forall q s,exists tr,row_to_tm r_{suffix} q s=Some tr)
    by(intros[] [];eexists;reflexivity).
  pose proof(finite_instr_recurrent _ _ Htotal Hhit)as Hrec.
  apply coversTr_nqh,neverqhtr_mirror.
  apply(ngram_check_neverqh_fuelmixtr_except_sound _ {r['n']} 0 {r['fuel']} {r['rounds']}
    skip_{suffix} cert_{suffix}).
  - intros[[] []] H N;try discriminate.
    destruct(Hrec N)as(j&Hj&Hf). exists j;split;[exact Hj|apply mirror_fires;exact Hf].
  - vm_compute;reflexivity.'''
        entries.append((r['spec'],proof))
    return cbt.write_batch('AST',BATCH,
      ['From BBB4 Require Import CTape Mirror.',
       'From BBB4.Checkers Require Import NGram FuelMixTr FuelMixPartialTr.',
       'From BBB4.Counters Require Import CConjugateTr FiniteInstrTr AlternatingCarryFiniteTr.',
       'From BBB4.CensusTr Require Import TNF_QHTr.'],entries,
      'alternating carries on finite tapes and checked instruction recurrence',
      preamble='\n\n'.join(pre))

def main(data=DATA,batch=BATCH,emitter=emit):
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check',action='store_true')
    parser.add_argument('--find',action='store_true')
    args=parser.parse_args()
    assert not(args.check and args.find)
    records=json.loads(data.read_text())
    target=Path(cbt.batch_path('AST',batch))
    if args.find:
        import fuelcombinedtr_batch as combined
        ft=combined.ft
        for r in records:
            n=r['n'];spec=ft.gf.mirror_mtext(r['spec']) if r['mirrored'] else r['spec']
            tbl=ft.bp.parse(spec)
            _,ls,rs,a0,_=ft.bp.build_closure(tbl,n,0)
            nodes=ft.gf.build_fw_closure(tbl,ls,rs,(a0,0,0));adj=ft.gf.fw_adj(tbl,ls,rs,nodes)
            candidates=ft.pattern_candidates(n,r['max_pattern']);delta=ft.make_pattern_delta(tbl,n)
            cert={};failed=[]
            for q in itertools.product(range(4),range(2)):
                result=ft.instruction_procedure(tbl,n,adj,nodes,q,candidates,delta)
                if result is None:failed.append(list(q))
                else:
                    assert ft.instruction_check(tbl,n,adj,nodes,q,*result)
                    cert[q]=result
            assert failed==r['failed']
            r.update(cert=combined.fm.emit_cert(cert),fuel=8*len(nodes)+64,
                     rounds=len(ls)+len(rs)+4,contexts=len(nodes))
            r['certificate_sha256']=hashlib.sha256(r['cert'].encode()).hexdigest()
    else:
        source=target.read_text()
        for i,r in enumerate(records):
            start=f'Definition cert_AST_{batch}_{i:04d}:Instr->list fmxcomp*list positive :=\n'
            r['cert']=source.split(start,1)[1].split('\n  end.',1)[0]+'\n  end'
            assert hashlib.sha256(r['cert'].encode()).hexdigest()==r['certificate_sha256']
    with tempfile.TemporaryDirectory()as tmp:
        cbt.CT=tmp
        generated=Path(emitter(records)).read_text()
    if args.check:assert target.read_text()==generated
    else:target.write_text(generated)
    if args.find:
        data.write_text(json.dumps([{k:v for k,v in r.items()if k!='cert'}for r in records],indent=2)+'\n')
    print(('checked'if args.check else'wrote'),target)

if __name__=='__main__':main()
