"""Replay the isolated contextual-marker theorem and its three exact families.

Proof input is compact: machine tables, marker masks, capacity weights and fixed
history-search parameters. Coq reconstructs and checks graph closure and every
contextual marker edge. Full recursive coqchk and an exact census wrapper are
required before any package report is written. Existing reports stay frozen.
"""
import argparse
import hashlib
import json
from pathlib import Path
import resource
import subprocess
import time

from check_campaign import dependency_hashes, inventory_source
from generate_pipeline_examples import codes
import kernel_audit_cache_v3 as kernel

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT/'research/burn9-context-marker'
OUTPUT = ROOT/'build/burn9-context-marker/proof'
DEPENDENCY = ROOT/'build/burn4-entry-marker/proof'
NS = 'BBB24Burn9ContextMarker'
TEMPLATES = ['ContextMarker.v','Regression.v']


def artifact(suffix):
    return BASE.with_name(BASE.name+'-'+suffix)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def exact(path, text):
    if path.exists() and path.read_text() != text:
        raise ValueError('Frozen artifact differs: '+str(path))
    if not path.exists(): path.write_text(text)


def example(index,row):
    table=';'.join(map(str,codes(row['machine'])))
    w1,w2,w3=row['weights'][1:]
    params=f"{row['marker_mask']}%N {w1} {w2} {w3} {row['history']} {row['width']} {row['anchor']} {row['fuel']} {row['rounds']}"
    return f'''From Coq Require Import List NArith.
From BBB24 Require Import Statement Spec Pipeline MarkerPotential MarkerState.
From BBB24Burn4EntryMarker Require Import EntryMarker.
From {NS} Require Import ContextMarker.
Import ListNotations.
Definition machine_{index} := machine_of_codes[{table}].
Lemma old_entry_condition_rejected :
 em_preserve machine_{index}(ms_mark {row['marker_mask']}%N)=false.
Proof. vm_compute;reflexivity. Qed.
Lemma context_marker_accepted : cm_check machine_{index} {params}=true.
Proof. vm_compute;reflexivity. Qed.
Theorem nonhalt_{index} : NonHalt machine_{index}.
Proof. exact(proj1(cm_check_sound _ _ _ _ _ _ _ _ _ _ context_marker_accepted)). Qed.
Theorem state_zero_{index} : QHBound 0 machine_{index}.
Proof. exact(proj2(cm_check_sound _ _ _ _ _ _ _ _ _ _ context_marker_accepted)). Qed.
Print Assumptions state_zero_{index}.
'''


def board(rows):
    imports=' '.join(f'Example{i:02d}' for i in range(len(rows)))
    machines=';'.join(f'machine_{i}' for i in range(len(rows)))
    packed=';'.join(str(row['code'])+'%N' for row in rows)
    cases='\n'.join(f' - eapply state_bound_extend;[exact nonhalt_{i}|exact state_zero_{i}|exact Hle].'
                    for i in range(len(rows)))
    destruct=''.join('[<-|' for _ in rows)+'Hbad'+']'*len(rows)
    return f'''From Coq Require Import List NArith.
From BBB24 Require Import Statement Spec Census Bootstrap Closeout StateOnlyCloseout BoardManifest.
From {NS} Require Import {imports}.
Import ListNotations.
Definition rows:list N := [{packed}].
Definition board:list TM := [{machines}].
Lemma inventory_checked : manifest_check rows board=true.
Proof. vm_compute;reflexivity. Qed.
Theorem inventory_exact : manifest_board rows=board.
Proof. apply manifest_check_sound;exact inventory_checked. Qed.
Theorem small_sound : StateBoardSound 0 board.
Proof.
 intros family Hin tm Hle;destruct Hin as{destruct}.
{cases}
 - contradiction.
Qed.
Theorem sound : StateBoardSound score board.
Proof. apply state_board_zero_weaken;exact small_sound. Qed.
Lemma pending_checked : forallb(pending_check 9 empty bootstrap)board=true.
Proof. vm_compute;reflexivity. Qed.
Theorem was_pending : forall family,In family board -> bootstrap_pending family.
Proof.
 intros family Hin;apply pending_check_sound;pose proof pending_checked as H.
 apply forallb_forall with(x:=family)in H;assumption.
Qed.
Print Assumptions small_sound.
'''


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--timeout',type=int,default=600)
    parser.add_argument('--audit-timeout',type=int,default=2400)
    args=parser.parse_args()
    if min(args.timeout,args.audit_timeout)<=0: parser.error('Positive budgets required')
    resource.setrlimit(resource.RLIMIT_AS,(3*1024**3,3*1024**3))
    OUTPUT.mkdir(parents=True,exist_ok=True)
    input_path=artifact('input.json'); report_path=artifact('checked.json'); inventory_path=artifact('machines.json')
    old=json.loads(report_path.read_text()) if report_path.exists() else None
    protected={p:sha(p) for p in (report_path,inventory_path) if p.exists()}
    data=json.loads(input_path.read_text());rows=data['rows']
    assert len(rows)==3 and len({r['machine'] for r in rows})==3 and data['state_bound']==0
    for row in rows:
        assert row['code']==sum(v*17**i for i,v in enumerate(codes(row['machine'])))
        assert row['weights'][0]==0 and len(row['weights'])==4
    templates=[ROOT/'proof-sources/burn9-context-marker'/name for name in TEMPLATES]
    template_pins={str(p.relative_to(ROOT)):sha(p) for p in templates}
    assert template_pins==data['template_sha256']
    dependency_input=ROOT/'research/burn4-entry-marker-input.json'
    dependency_pins=json.loads(dependency_input.read_text())['template_sha256']
    for name,digest in dependency_pins.items():
        p=ROOT/name; assert sha(p)==digest and sha(DEPENDENCY/p.name)==digest
    selection=ROOT/data['selection_report']; assert sha(selection)==data['selection_sha256']
    assert rows==json.loads(selection.read_text())['rows']
    inputs={str(p.relative_to(ROOT)):sha(p) for p in (input_path,dependency_input,selection)}
    load_paths=[(ROOT/'theories','BBB24'),(DEPENDENCY,'BBB24Burn4EntryMarker'),(OUTPUT,NS)]
    flags=[part for path,namespace in load_paths for part in ('-Q',str(path),namespace)]
    files=[]
    for template in templates:
        path=OUTPUT/template.name;exact(path,template.read_text());files.append(path)
    for i,row in enumerate(rows):
        path=OUTPUT/f'Example{i:02d}.v';exact(path,example(i,row));files.append(path)
    path=OUTPUT/'Board.v';exact(path,board(rows));files.append(path)
    descriptor=dict(id='burn9_context_marker',scope='state',rows=len(rows),state_bound=0,instruction_bound=None,
                    module=NS+'.Inventory',board='board',small_sound='small_sound',sound='sound',was_pending='was_pending',
                    proof_source=str((OUTPUT/'Inventory.v').relative_to(ROOT)),
                    exact_inventory_theorem=NS+'.Inventory.inventory_exact',
                    inventories=[dict(path=str(inventory_path.relative_to(ROOT)),format='rows')],
                    load_paths=[dict(path=str(p.relative_to(ROOT)),namespace=ns) for p,ns in load_paths[1:]])
    path=OUTPUT/'Inventory.v';exact(path,inventory_source(dict(descriptor,module=NS+'.Board',machines=[r['machine'] for r in rows])));files.append(path)
    sources=dependency_hashes(files,flags)
    for name in ('check_burn9_context_marker.py','check_campaign.py','check_shadow_links.py',
                 'generate_pipeline_examples.py','kernel_audit_cache_v3.py'):
        sources['tools/'+name]=sha(ROOT/'tools'/name)
    inventory=json.dumps(dict(rows=[dict(machine=r['machine']) for r in rows]),indent=2)+'\n'
    stable=dict(inputs_sha256=inputs,template_sha256={**template_pins,**dependency_pins},
                source_sha256=sources,descriptor=descriptor,inventory_sha256=hashlib.sha256(inventory.encode()).hexdigest(),
                checked_state_families=len(rows),checked_instruction_families=0)
    if old: assert all(old[k]==v for k,v in stable.items())
    timings={}
    for path in files:
        started=time.monotonic()
        with path.with_suffix('.log').open('w') as log:
            subprocess.run(['coqc','-w','-abstract-large-number','-native-compiler','no',*flags,str(path)],
                           stdout=log,stderr=subprocess.STDOUT,check=True,timeout=args.timeout)
        timings[path.stem]=round(time.monotonic()-started,3)
        print('Compiled '+path.stem+': '+str(timings[path.stem])+'s',flush=True)
    receipt,log=kernel.fresh_paths(OUTPUT,'kernel-audit')
    started=time.monotonic()
    audit=kernel.audit([NS+'.Inventory'],[files[-1]],load_paths,receipt,log,recursive=True,timeout=args.audit_timeout)
    assert all(sha(ROOT/p)==h for p,h in {**inputs,**sources,**template_pins,**dependency_pins}.items())
    assert all(sha(p)==h for p,h in protected.items())
    current=dict(stable,scope='Three exact state-zero census families, all completions. No instruction claim.',
                 compile_seconds=timings,kernel_receipt=str(receipt.relative_to(ROOT)),kernel_receipt_sha256=sha(receipt),
                 kernel_audit='Full recursive coqchk.',audit_seconds=round(time.monotonic()-started,3),
                 checked_modules=len(audit['checked_modules']),reused_modules=len(audit['reused_modules']),
                 object_sha256={str(p.with_suffix('.vo').relative_to(ROOT)):sha(p.with_suffix('.vo')) for p in files})
    if old is None:
        exact(inventory_path,inventory);exact(report_path,json.dumps(current,indent=2,sort_keys=True)+'\n')
    (OUTPUT/'current-proof-receipt.json').write_text(json.dumps(current,indent=2,sort_keys=True)+'\n')
    print('Three contextual-marker state families fully audited.',flush=True)


if __name__=='__main__': main()
