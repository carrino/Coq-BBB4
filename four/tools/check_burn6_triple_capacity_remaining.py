"""Replay two further capacity families using the frozen triple theorem.

The witnesses here use only symbol and right-pair counts. Their triple scores
ignore the third cell; no additional mathematical theorem is introduced.
"""
import argparse
import hashlib
import json
from pathlib import Path
import resource
import subprocess
import sys
import time

from check_campaign import dependency_hashes, inventory_source
from check_closure_wave import aggregate_source
import kernel_audit_cache_v3 as kernel
from weighted_codec_v2 import bundle_decode, unpack
from weighted_render import naturals
from weighted_render_v4 import render

ROOT = Path(__file__).resolve().parents[1]
PREFIX = ROOT/'research/burn6-triple-capacity-remaining'
BUILD = ROOT/'build/burn6-triple-capacity-remaining/proof'
NS = 'BBB24Burn6TripleCapacityRemaining'
MACHINES = ['1LB2LB3RA2RA_1RA3LB2LB1RB', '1LB2LB3LA2RB_3RA1RA0LA1RA']
TARGETS = [1, 5]


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def artifact(suffix):
    return PREFIX.with_name(PREFIX.name+'-'+suffix)


def exact(path, text):
    if path.exists() and path.read_text() != text:
        raise ValueError('Frozen artifact differs: '+str(path))
    if not path.exists():
        path.write_text(text)


def score(weights, pair, triple):
    branches = []
    for a in range(4):
        for b in range(4):
            for c in range(4):
                value = weights[pair+4*a+b]+weights[triple+16*a+4*b+c]
                if value:
                    branches.append(f'|S{a},S{b},S{c}=>{value}')
    return 'fun a b c=>match a,b,c with '+''.join(branches)+'|_,_,_=>0 end'


def render_row(packed, index):
    row = unpack(packed); graph = row['graph']; target = TARGETS[index]
    if (graph['machine'] != MACHINES[index] or graph['mirror'] != 0
            or graph['n'] != 2 or graph['t'] != 4096 or packed['missing_target'] != target):
        raise ValueError('Unexpected concrete recurrence graph')
    capacity = packed['triple_capacity']; weights = capacity['weights']; bias = capacity['bias']
    if (capacity['scale'] != 1 or len(weights) != 172 or len(bias) != len(graph['nodes'])
            or any(type(x) is not int or x < 0 for x in weights+bias)
            or any(weights[i] for i in (0,4,8,12,28,44,108)) or any(weights[44:])):
        raise ValueError('Unexpected pair-only capacity witness')
    terms = []
    for part, ctor in enumerate(['MAll','MLeft','MRight']):
        for symbol in (1,2,3):
            if weights[4*part+symbol]:
                terms.append(f'({weights[4*part+symbol]}%nat,{ctor} C{symbol})')
    targets = ';'.join(f'(St{chr(65+t//4)},S{t%4})' for t in range(8) if t != target)
    tg = f'(St{chr(65+target//4)},S{target%4})'
    source = render(row).split('Lemma checked:',1)[0]
    return source + f'''From BBB24 Require Import Bootstrap Closeout CertifiedBoard InstructionPortfolio.
From BBB24Burn6TripleCapacity Require Import TripleCapacity.
Definition left_score:Sym->Sym->Sym->nat:={score(weights,12,44)}.
Definition right_score:Sym->Sym->Sym->nat:={score(weights,28,108)}.
Definition capacity:TCapacity:=mkTCapacity 1 [{';'.join(terms)}] left_score right_score
 (wc_table 0%nat nodes {naturals(bias)}).
Definition targets:list Instr:=[{targets}].
Lemma seven_checked:wp_graph_check family 2 4096 nodes targets certificate=true.
Proof. vm_compute;reflexivity. Qed.
Lemma eighth_checked:tc_graph_check family 2 4096 nodes {tg} capacity(wc_components target_{target})=true.
Proof. vm_compute;reflexivity. Qed.
Theorem seven_sound:NonHalt family /\\
 forall tg,In tg targets -> forall N,exists k,N<=k /\\ FiresAt family tg k.
Proof. exact(wp_graph_check_sound _ _ _ _ _ _ seven_checked). Qed.
Theorem eighth_sound:NonHalt family /\\
 forall N,exists k,N<=k /\\ FiresAt family {tg} k.
Proof. exact(tc_graph_check_sound _ _ _ _ _ _ _ eighth_checked). Qed.
Example old_boundary_rejected:wp_graph_check family 2 4096 nodes [{tg}] certificate=false.
Proof. vm_compute;reflexivity. Qed.
Definition no_right_pairs:TCapacity:=mkTCapacity 1(tc_terms capacity)left_score(fun _ _ _=>0)(tc_bias capacity).
Example omitted_right_pairs_rejected:tc_graph_check family 2 4096 nodes {tg} no_right_pairs(wc_components target_{target})=false.
Proof. vm_compute;reflexivity. Qed.
Lemma all_instructions_recur:forall tg N,exists k,N<=k /\\ FiresAt family tg k.
Proof.
 intros [q h] N;destruct q,h.
 all:try(apply(proj2 seven_sound);unfold targets;simpl;tauto).
 exact(proj2 eighth_sound N).
Qed.
Theorem exact_bounds:NonHalt family /\\ Bounds 0%N 0%N family.
Proof. apply wp_all_recur_sound;exact all_instructions_recur. Qed.
Definition board:list TM:=[family].
Lemma nonhalt:forall f,In f board->NonHalt f.
Proof. intros f[<-|H];[exact(proj1 exact_bounds)|contradiction]. Qed.
Lemma small_sound:BoardSound 0%N 0%N board.
Proof.
 intros f[<-|Hfalse]tm Hle;[|contradiction].
 destruct exact_bounds as[Hnh Hb];eapply extend_bounds;eauto.
Qed.
Lemma sound:BoardSound scoreN scoreN board.
Proof.
 intros f Hin tm Hle;eapply(bounds_weaken 0%N 0%N scoreN scoreN tm).
 - vm_compute;discriminate.
 - vm_compute;discriminate.
 - exact(small_sound f Hin tm Hle).
Qed.
Lemma pending_checked:forallb(pending_check 9 empty bootstrap)board=true.
Proof. vm_compute;reflexivity. Qed.
Lemma was_pending:forall f,In f board -> bootstrap_pending f.
Proof.
 intros f Hin;apply pending_check_sound.
 pose proof pending_checked as H;apply forallb_forall with(x:=f)in H;assumption.
Qed.
Print Assumptions exact_bounds.
'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--timeout', type=int, default=300)
    parser.add_argument('--audit-timeout', type=int, default=1200)
    args = parser.parse_args()
    if args.timeout <= 0 or args.audit_timeout <= 0:
        raise ValueError('Positive replay budgets required')
    resource.setrlimit(resource.RLIMIT_AS, (3*1024**3, 3*1024**3))
    BUILD.mkdir(parents=True, exist_ok=True)
    input_path = artifact('input.json'); report_path = artifact('checked.json'); inventory_path = artifact('machines.json')
    data = json.loads(input_path.read_text()); previous = json.loads(report_path.read_text()) if report_path.exists() else None
    protected = {p:sha(p) for p in (report_path,inventory_path) if p.exists()}
    expected = {'machines':MACHINES, 'selected_rows':2, 'state_bound':0, 'instruction_bound':0,
                'indices':[44,52], 'targets':TARGETS}
    if any(data.get(k) != v for k,v in expected.items()):
        raise ValueError('Unexpected selection or declared bounds')
    bundle = ROOT/data['bundle']['path']; dependency = ROOT/data['theory_dependency']['report']
    if (bundle.resolve() != artifact('certificates.json').resolve() or data['bundle']['rows'] != 2
            or bundle.stat().st_size != data['bundle']['bytes'] or sha(bundle) != data['bundle']['sha256']
            or dependency.resolve() != (ROOT/'research/burn6-triple-capacity-checked.json').resolve()
            or sha(dependency) != data['theory_dependency']['sha256']):
        raise ValueError('Frozen certificate or theory dependency differs')
    dependency_report = json.loads(dependency.read_text())
    for name,digest in dependency_report['source_sha256'].items():
        if sha(ROOT/name) != digest:
            raise ValueError('Replay frozen triple-capacity dependency first: '+name)
    packed = bundle_decode(bundle.read_text())
    if len(packed) != 2:
        raise ValueError('Expected two compact certificates')
    inputs = {str(p.relative_to(ROOT)):sha(p) for p in (input_path,bundle,dependency)}
    loadpaths = [(ROOT/'theories','BBB24'),(ROOT/'build/burn3-frequent-invariants/proof','BBB24Burn3Pair'),
                 (ROOT/'build/burn6-triple-capacity/proof','BBB24Burn6TripleCapacity'),(BUILD,NS)]
    flags = [x for p,n in loadpaths for x in ('-Q',str(p),n)]
    paths, modules = [], []
    for index,row in enumerate(packed):
        name = f'Row{index:03d}'; path = BUILD/(name+'.v')
        exact(path,render_row(row,index));paths.append(path);modules.append(name)
    path = BUILD/'All.v';exact(path,aggregate_source(modules,NS,0,2));paths.append(path)
    descriptor = dict(id='burn6_triple_capacity_remaining',scope='both',rows=2,state_bound=0,instruction_bound=0,
        module=NS+'.Inventory',board='board',small_sound='small_sound',sound='sound',was_pending='was_pending',
        proof_source=str((BUILD/'Inventory.v').relative_to(ROOT)),exact_inventory_theorem=NS+'.Inventory.inventory_exact',
        inventories=[dict(path=str(inventory_path.relative_to(ROOT)),format='rows')],
        load_paths=[dict(path=str(p.relative_to(ROOT)),namespace=n) for p,n in loadpaths[1:]])
    path = BUILD/'Inventory.v';exact(path,inventory_source({**descriptor,'module':NS+'.All','machines':MACHINES}));paths.append(path)
    sources = dependency_hashes(paths,flags)
    for module in list(sys.modules.values()):
        name = getattr(module,'__file__',None)
        if name and Path(name).resolve().is_relative_to(ROOT/'tools'):
            p=Path(name).resolve();sources[str(p.relative_to(ROOT))]=sha(p)
    inventory = json.dumps({'rows':[{'machine':m} for m in MACHINES]},indent=2)+'\n'
    stable = dict(inputs_sha256=inputs,source_sha256=sources,descriptor=descriptor,
        inventory_sha256=hashlib.sha256(inventory.encode()).hexdigest(),checked_state_families=2,checked_instruction_families=2,
        all_recurrent_theorems=[NS+'.'+m+'.all_instructions_recur' for m in modules])
    if previous and any(previous[k] != v for k,v in stable.items()):
        raise ValueError('Frozen proof report differs')
    if previous and (not inventory_path.exists() or sha(inventory_path) != stable['inventory_sha256']):
        raise ValueError('Frozen inventory differs')
    timings={}
    for path in paths:
        started=time.monotonic()
        with path.with_suffix('.log').open('w') as log:
            subprocess.run(['coqc','-w','-abstract-large-number','-native-compiler','no',*flags,str(path)],
                           stdout=log,stderr=subprocess.STDOUT,timeout=args.timeout,check=True)
        timings[path.stem]=round(time.monotonic()-started,3)
        print('Compiled '+path.stem+': '+str(timings[path.stem])+'s',flush=True)
    receipt,log=kernel.fresh_paths(BUILD,'kernel-audit');started=time.monotonic()
    audited=kernel.audit([NS+'.Inventory'],[paths[-1]],loadpaths,receipt,log,recursive=True,timeout=args.audit_timeout)
    if any(sha(ROOT/name)!=digest for name,digest in {**inputs,**sources}.items()):
        raise ValueError('Frozen input or source changed during replay')
    if any(sha(path)!=digest for path,digest in protected.items()):
        raise ValueError('Published evidence changed during replay')
    current={**stable,'scope':'Two exact all-completion census families; every instruction recurs.',
        'compile_seconds':timings,'audit_seconds':round(time.monotonic()-started,3),
        'kernel_audit':'Full recursive coqchk.','kernel_receipt':str(receipt.relative_to(ROOT)),
        'kernel_receipt_sha256':sha(receipt),'checked_modules':len(audited['checked_modules']),
        'reused_modules':len(audited['reused_modules']),
        'object_sha256':{str(p.with_suffix('.vo').relative_to(ROOT)):sha(p.with_suffix('.vo')) for p in paths}}
    if previous is None:
        exact(inventory_path,inventory);exact(report_path,json.dumps(current,indent=2,sort_keys=True)+'\n')
    (BUILD/'current-proof-receipt.json').write_text(json.dumps(current,indent=2,sort_keys=True)+'\n')
    print('Two additional capacity families kernel-audited and inventory-exact.',flush=True)


if __name__=='__main__':
    main()
