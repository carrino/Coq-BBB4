"""Replay compact weighted/ordinary bundles and discharge their actual census cores.

Each generated module checks a small batch, including bootstrap membership.
Successful compilations have reusable hash receipts; a failed batch is bisected
to isolate failures. Only the final recursive kernel audit publishes a report.
Generated Coq and compilation products remain in the ignored build directory.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import subprocess
import time

from check_shadow_links import dependency_hashes
from generate_pipeline_examples import codes
from weighted_codec_v2 import unpack, bundle_decode
from weighted_render import HEADER, render

ROOT=Path(__file__).resolve().parents[1]


def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()


def write_json(path,value):
    temp=path.with_suffix(path.suffix+'.tmp')
    temp.write_text(json.dumps(value,indent=2,sort_keys=True)+'\n');temp.replace(path)


def ordinary(row):
    for key in ('n','t','fuel','rounds'):
        if type(row[key]) is not int or row[key]<0:raise ValueError('Invalid ordinary parameter')
    if row['mirror'] not in (0,1):raise ValueError('Invalid reflection')
    text='Definition family:TM:=machine_of_codes ['+';'.join(map(str,codes(row['machine'])))+'].\n'
    actual='(mirror_tm family)' if row['mirror'] else 'family'
    text+=f"Lemma checked:ng_check 4096%N 4096%N {actual} {row['n']} {row['t']} {row['fuel']} {row['rounds']}=true.\nProof. vm_compute. reflexivity. Qed.\n"
    text+='Theorem family_run:NonHalt family /\\ Bounds 4096%N 4096%N family.\nProof.\n'
    if row['mirror']:
        text+='destruct (ng_check_sound _ _ _ _ _ _ _ checked) as [Hrun Hb].\nsplit;[apply mirror_nonhalt;exact Hrun|eapply mirror_bounds;exact Hb].\n'
    else:text+='eapply ng_check_sound;exact checked.\n'
    return text+'Qed.\n'


def shard_source(rows):
    text=HEADER+'From BBB24 Require Import Pipeline NGramCensus Bootstrap Closeout CertifiedBoard.\n'
    for index,row in enumerate(rows):
        body=render(unpack(row))[len(HEADER):] if row['kind']=='weighted' else ordinary(row)
        text+=f'Module R{index:04d}.\n'+body+f'End R{index:04d}.\n'
    entries=';'.join(f'mkCertifiedFamily 4096%N 4096%N R{i:04d}.family R{i:04d}.family_run' for i in range(len(rows)))
    return text+f'''Definition families:list(CertifiedFamily 4096%N 4096%N):=[{entries}].
Definition board:=certified_board 4096%N 4096%N families.
Lemma board_small_sound:BoardSound 4096%N 4096%N board.
Proof. apply certified_board_sound. Qed.
Lemma board_nonhalt:forall tm,In tm board->NonHalt tm.
Proof. apply certified_board_nonhalt. Qed.
Lemma pending_checked:forallb (pending_check 9 empty bootstrap) board=true.
Proof. vm_compute. reflexivity. Qed.
Lemma board_was_pending:forall tm,In tm board->bootstrap_pending tm.
Proof.
 intros tm Hin. apply pending_check_sound. pose proof pending_checked as H.
 apply forallb_forall with (x:=tm) in H; assumption.
Qed.
'''


def all_forall(modules,lemma):
    return '\n'.join(f'apply Forall_cons;[exact {module}.{lemma}|].' for module in modules)+'\napply Forall_nil.'


def aggregate(namespace,modules):
    imports=f'From {namespace} Require Import '+ ' '.join(modules)+'.\n' if modules else ''
    boards=';'.join(module+'.board' for module in modules)
    return r'''From Coq Require Import List NArith.
From BBB24 Require Import Statement Spec Bounds Census Bootstrap Closeout CertifiedBoard CensusUnion.
Import ListNotations.
'''+imports+f'''Definition weighted_boards:list(list TM):=[{boards}].
Definition weighted_board:=concat weighted_boards.
Lemma weighted_board_small_sound:BoardSound 4096%N 4096%N weighted_board.
Proof. apply boards_sound. unfold weighted_boards.
{all_forall(modules,'board_small_sound')}
Qed.
Lemma weighted_board_was_pending:forall tm,In tm weighted_board->bootstrap_pending tm.
Proof. apply boards_pending. unfold weighted_boards.
{all_forall(modules,'board_was_pending')}
Qed.
Lemma weighted_board_nonhalt:forall tm,In tm weighted_board->NonHalt tm.
Proof.
 assert(H:Forall (fun board=>forall tm,In tm board->NonHalt tm) weighted_boards).
 {{ unfold weighted_boards.
{all_forall(modules,'board_nonhalt')}
 }}
 intros tm Hin. apply in_concat in Hin as (board&Hboard&Hin).
 apply Forall_forall with (x:=board) in H;[apply H;exact Hin|exact Hboard].
Qed.
'''+r'''Lemma weighted_board_sound:BoardSound scoreN scoreN weighted_board.
Proof.
 intros family Hin tm Hle. eapply (bounds_weaken 4096%N 4096%N scoreN scoreN tm).
 - vm_compute. discriminate.
 - vm_compute. discriminate.
 - exact (weighted_board_small_sound family Hin tm Hle).
Qed.
Definition weighted_pending:=remaining bootstrap_pending weighted_board.
Theorem weighted_coverage:forall tm,Bounds scoreN scoreN tm \/ weighted_pending tm.
Proof. exact (closeout_coverage _ _ _ _ bootstrap_coverage weighted_board_sound). Qed.
Theorem weighted_families_discharged:forall family,In family weighted_board->
 forall tm,TM_le family tm->bootstrap_pending tm /\ Bounds scoreN scoreN tm /\ ~weighted_pending tm.
Proof. exact (board_families_discharged _ _ _ _ _ weighted_board_was_pending weighted_board_sound). Qed.
Print Assumptions weighted_families_discharged.
'''


def run(command,log,timeout):
    start=time.monotonic()
    with log.open('w') as stream:
        try:code=subprocess.run(command,stdout=stream,stderr=subprocess.STDOUT,timeout=timeout).returncode
        except subprocess.TimeoutExpired:code=124
    return code,round(time.monotonic()-start,3)


def sources(flags):
    hashes=dependency_hashes([ROOT/'theories/WeightedCensus.v',ROOT/'theories/WeightedRegression.v',
                             ROOT/'theories/CertifiedBoard.v',ROOT/'theories/Bootstrap.v',
                             ROOT/'theories/CensusUnion.v',ROOT/'theories/Pipeline.v'],flags)
    for filename in ('check_weighted_v2.py','weighted_render.py','weighted_codec_v2.py',
                     'check_shadow_links.py','generate_pipeline_examples.py'):
        hashes['tools/'+filename]=sha(ROOT/'tools'/filename)
    return hashes


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--registry',type=Path,required=True)
    parser.add_argument('--output-dir',type=Path,required=True)
    parser.add_argument('--report',type=Path,required=True)
    parser.add_argument('--inventory',type=Path,required=True)
    parser.add_argument('--namespace',default='BBB24WeightedV2')
    parser.add_argument('--batch-size',type=int,default=16)
    parser.add_argument('--timeout',type=int,default=180)
    parser.add_argument('--check',action='store_true')
    args=parser.parse_args()
    if not re.fullmatch(r'[A-Z][A-Za-z0-9_]*(\.[A-Z][A-Za-z0-9_]*)*',args.namespace) or args.batch_size<1 or args.timeout<1:
        parser.error('Invalid budget or namespace')
    registry=json.loads(args.registry.read_text());rows=[]
    for bundle in registry['bundles']:
        path=ROOT/bundle['path']
        if sha(path)!=bundle['sha256'] or path.stat().st_size>4*1024*1024:raise ValueError('Bundle hash/size differs')
        part=bundle_decode(path.read_text())
        if len(part)!=bundle['rows']:raise ValueError('Bundle row count differs')
        rows+=part
    if not rows or len(rows)!=registry['rows'] or len({row['machine'] for row in rows})!=len(rows):
        raise ValueError('Empty, duplicate or mismatched bundle inventory')
    for row in rows:
        codes(row['machine'])
        if row['kind'] not in ('weighted','ordinary'):raise ValueError('Unknown certificate kind')
    args.output_dir.mkdir(parents=True,exist_ok=True)
    flags=['-Q',str(ROOT/'theories'),'BBB24','-Q',str(args.output_dir.resolve()),args.namespace]
    manifest={'registry_sha256':sha(args.registry),'sources_sha256':sources(flags),
              'coq_version':subprocess.run(['coqc','--version'],capture_output=True,text=True,check=True).stdout.splitlines()[0],
              'namespace':args.namespace,'batch_size':args.batch_size,'rows':len(rows),
              'state_bound':4096,'instruction_bound':4096}
    manifest_path=args.output_dir/'manifest.json'
    if manifest_path.exists() and json.loads(manifest_path.read_text())!=manifest:raise ValueError('Frozen manifest differs; use a fresh output directory')
    if args.check:
        report=json.loads(args.report.read_text())
        if manifest!=report['manifest']:raise ValueError('Saved report manifest differs')
        for filename,digest in report['artifacts_sha256'].items():
            if sha(args.output_dir/filename)!=digest:raise ValueError('Changed proof artifact '+filename)
        if sha(args.inventory)!=report['inventory_sha256']:raise ValueError('Changed inventory')
        print(f"Validated {report['census_linked']} census-linked weighted/ordinary families.");return
    write_json(manifest_path,manifest)
    modules=[];results=[];artifacts=[manifest_path]
    def compile_batch(name,batch):
        path=args.output_dir/(name+'.v');text=shard_source(batch);path.write_text(text)
        evidence={'source_sha256':sha(path),'manifest_sha256':sha(manifest_path)}
        receipt=path.with_suffix('.receipt.json');vo=path.with_suffix('.vo')
        old=json.loads(receipt.read_text()) if receipt.exists() else {}
        reuse=all(old.get(k)==v for k,v in evidence.items()) and old.get('code')==0 and vo.exists() and old.get('vo_sha256')==sha(vo)
        if reuse:code=0;seconds=0
        else:
            code,seconds=run(['coqc','-native-compiler','no',*flags,str(path)],path.with_suffix('.log'),args.timeout)
            write_json(receipt,{**evidence,'code':code,'seconds':seconds,**({'vo_sha256':sha(vo)} if code==0 else {})})
        print(f'{name}: {len(batch)} rows, code {code}, {seconds}s'+(' cached' if reuse else ''),flush=True)
        if code==0:
            modules.append(name);artifacts.extend([path,vo,receipt])
            results.extend({'machine':row['machine'],'kind':row['kind'],'module':name,'status':'coq_compiled'} for row in batch)
        elif len(batch)>1:
            middle=len(batch)//2;compile_batch(name+'A',batch[:middle]);compile_batch(name+'B',batch[middle:])
        else:results.append({'machine':batch[0]['machine'],'kind':batch[0]['kind'],'module':name,'status':'timeout' if code==124 else 'rejected'})
    for offset in range(0,len(rows),args.batch_size):compile_batch(f'Weighted{offset//args.batch_size:05d}',rows[offset:offset+args.batch_size])
    board=args.output_dir/'WeightedAll.v';board.write_text(aggregate(args.namespace,modules))
    code,_=run(['coqc','-native-compiler','no',*flags,str(board)],board.with_suffix('.log'),args.timeout)
    if code:raise RuntimeError('Aggregate failed; no report published')
    code,_=run(['coqchk','-silent','-bytecode-compiler','yes',*flags,args.namespace+'.WeightedAll','BBB24.WeightedRegression'],args.output_dir/'coqchk.log',args.timeout*max(1,len(modules)))
    if code:raise RuntimeError('Kernel audit failed; no report published')
    if manifest['registry_sha256']!=sha(args.registry) or manifest['sources_sha256']!=sources(flags):raise ValueError('Sources changed during replay')
    for bundle in registry['bundles']:
        if sha(ROOT/bundle['path'])!=bundle['sha256']:raise ValueError('Bundle changed during replay')
    checked=[row for row in results if row['status']=='coq_compiled']
    for row in checked:row['status']='coq_checked'
    args.inventory.parent.mkdir(parents=True,exist_ok=True)
    write_json(args.inventory,{'rows':[{'machine':row['machine']} for row in checked]})
    artifacts.extend([board,board.with_suffix('.vo')])
    descriptor={'module':args.namespace+'.WeightedAll','board':'weighted_board','nonhalt':'weighted_board_nonhalt',
                'small_sound':'weighted_board_small_sound','sound':'weighted_board_sound','was_pending':'weighted_board_was_pending',
                'discharged':'weighted_families_discharged','proof_source':str(board.resolve().relative_to(ROOT)),
                'machine_inputs':[{'path':str(args.inventory.resolve().relative_to(ROOT)),'format':'json_rows'}],
                'load_paths':[{'path':str(args.output_dir.resolve().relative_to(ROOT)),'namespace':args.namespace}]}
    report={'manifest':manifest,'validation':'coqc vm_compute for bounds and actual pending membership, plus recursive coqchk',
            'counts':dict(Counter(row['status'] for row in results)),'results':results,'census_linked':len(checked),
            'descriptor':descriptor,'inventory_sha256':sha(args.inventory),
            'artifacts_sha256':{path.name:sha(path) for path in artifacts}}
    args.report.parent.mkdir(parents=True,exist_ok=True);write_json(args.report,report)
    print(json.dumps(report['counts'],sort_keys=True),flush=True)


if __name__=='__main__':main()
