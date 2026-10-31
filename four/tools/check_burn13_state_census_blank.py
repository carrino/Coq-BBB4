"""Replay conditional state census cut composition and the complete blank root.

The tracked recipe pins native sources, traces, units and dependencies. Missing
native artifacts are regenerated automatically and remain untrusted. Every
certificate and cut composition is checked by Coq, with strict v3 audit reuse.
The unresolved frontier remains an explicit score-bound hypothesis.
"""
import argparse
import csv
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time

from check_shadow_links import dependency_hashes
import kernel_audit_cache_v3 as kernel
from triage import scoped_source, replace_once

ROOT=Path(__file__).resolve().parents[1]
BUILD=ROOT/'build/burn13-state-census'
SOURCE=ROOT/'proof-sources/burn13-state-census-join/Join.v'
INPUT=ROOT/'research/burn13-state-census-blank-input.json'
NAMESPACE='BBB24Burn13StateCensus'
PROTOTYPE=ROOT/'build/burn10-state-closeout/prototype'
STATUS=BUILD/'continuation-status.json'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def dump(path,data):
    path.parent.mkdir(parents=True,exist_ok=True)
    path.write_text(json.dumps(data,indent=2,sort_keys=True)+'\n')


def status(stage,**fields):
    dump(STATUS,dict(stage=stage,pid=os.getpid(),updated_unix=time.time(),**fields))


def packed(machine):
    raw=machine.replace('_','');value=0
    for i in reversed(range(8)):
        cell=raw[3*i:3*i+3]
        code=16 if cell=='---' else 4*int(cell[0])+2*(cell[1]=='R')+(cell[2]=='B')
        value=17*value+code
    return value


def code_list(value):
    out=[]
    for _ in range(8):
        value,code=divmod(value,17);out.append(code)
    assert value==0
    return ';'.join(map(str,out))


def prepare():
    capture=json.loads((ROOT/'research/burn10-state-census-capture.json').read_text())
    plan=json.loads((ROOT/'build/burn12-state-census-shard-plan/blank-units.json').read_text())
    pins={str(p.relative_to(ROOT.parent)):sha(p) for p in
          [ROOT.parent/'tools/multisymbol/survey.cpp',ROOT/'tools/triage.py',SOURCE,
           *sorted((ROOT/'proof-sources/burn10-state-closeout').glob('*.v'))]}
    data=dict(scope='Conditional complete blank-root state census at scoreN; unresolved frontier remains a hypothesis.',
              root='blank',root_code=1,native_parameters=dict(symbols=4,fuel=256,window=64,states=2,max_nodes=10000000),
              capture=capture['roots']['blank'],plan=plan,source_sha256=pins,
              pilot_unit=5,minimum_nodes=4097,maximum_nodes=16385)
    dump(INPUT,data)


def ensure_trace(data):
    existing=ROOT/'build/burn10-state-closeout/census/blank.certificates.tsv'
    if existing.exists() and sha(existing)==data['capture']['certificates_sha256']:
        return existing
    native=BUILD/'native';native.mkdir(parents=True,exist_ok=True)
    prefix=native/'blank';trace=prefix.with_suffix('.certificates.tsv')
    if trace.exists() and sha(trace)==data['capture']['certificates_sha256']:
        return trace
    original=ROOT.parent/'tools/multisymbol/survey.cpp'
    generated=replace_once(scoped_source(original.read_text()),'certificates.open("/dev/null");',
                           'certificates.open(string(argv[1]) + ".certificates.tsv");')
    source=native/'survey.cpp';source.write_text(generated);executable=native/'survey'
    subprocess.run(['g++','-O3','-std=c++17',str(source),'-o',str(executable)],check=True,timeout=120)
    p=data['native_parameters']
    result=subprocess.run([str(executable),str(prefix),str(p['symbols']),str(p['fuel']),str(p['window']),
                           str(p['states']),str(data['root_code']),str(p['max_nodes'])],
                          capture_output=True,text=True,check=True,timeout=300)
    dump(native/'current-summary.json',json.loads(result.stdout))
    assert sha(trace)==data['capture']['certificates_sha256']
    assert sha(prefix.with_suffix('.unresolved.txt'))==data['capture']['residual_sha256']
    return trace


def reconstruct(data,trace):
    expected=data['plan']['units'];units=[];cursor=0;frontier=set();kinds={}
    def emit(fragment):
        nodes=[];ids={};unresolved=[];cuts=[]
        def intern(tree):
            if tree[0]==3:
                value=(3,tree[1],tuple(intern(c) for c in tree[2]))
            else:
                value=tree
                if tree[0]==1:unresolved.append(tree[1])
                elif tree[0]==2:cuts.append(tree[1])
            if value not in ids:
                ids[value]=len(nodes);nodes.append(value)
            return ids[value]
        root=intern(fragment['tree']);index=len(units)
        compact=dict(machine=packed(fragment['machine']),nodes=nodes,root=root,unresolved=unresolved,dependencies=cuts)
        encoded=json.dumps(compact,separators=(',',':')).encode()
        old=expected[index]
        assert old['machine']==fragment['machine'] and old['represented_nodes']==fragment['size']
        assert old['compact_sha256']==hashlib.sha256(encoded).hexdigest() and old['compact_bytes']==len(encoded)
        assert old['direct_dependencies']==cuts and old['local_unresolved']==len(unresolved)
        assert len(cuts)==len(set(cuts)) and len(unresolved)==len(set(unresolved))
        assert all(i<index for i in cuts)
        units.append(compact)
        path=BUILD/'units'/f'{index:03}.json';path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(encoded)
        return dict(machine=fragment['machine'],size=1,tree=(2,index,packed(fragment['machine'])))
    with trace.open() as stream:
        rows=iter(csv.DictReader(stream,delimiter='\t'))
        def read():
            nonlocal cursor
            row=next(rows);cursor+=1;kind=row['kind'];kinds[kind]=kinds.get(kind,0)+1
            machine=row['machine']
            if kind=='unresolved':
                code=packed(machine);assert code not in frontier;frontier.add(code)
                return dict(machine=machine,size=1,tree=(1,code))
            if kind in ('cycle','translated'):
                return dict(machine=machine,size=1,tree=(0,int(int(row['shift'])<0),int(row['anchor']),int(row['period']),int(row['reach'])))
            assert kind=='halt'
            children=[read() for _ in range(16)];size=1+sum(c['size'] for c in children)
            while size>data['maximum_nodes']:
                i=max(range(16),key=lambda i:(children[i]['size'],-i));assert children[i]['size']>1
                size-=children[i]['size']-1;children[i]=emit(children[i])
            fragment=dict(machine=machine,size=size,tree=(3,int(row['anchor']),tuple(c['tree'] for c in children)))
            return emit(fragment) if size>=data['minimum_nodes'] else fragment
        final=read();assert next(rows,None) is None
    if final['tree'][0]!=2:final=emit(final)
    assert final['tree'][1]==data['plan']['root_unit'] and len(units)==len(expected)
    assert cursor==data['capture']['nodes'] and kinds==data['capture']['leaves']
    assert len(frontier)==data['capture']['leaves']['unresolved']
    assert sum(len(u['unresolved']) for u in units)==len(frontier)
    assert sum(len(u['dependencies']) for u in units)==len(units)-1
    return units


def unit_module(data):
    return {u:i for i,m in enumerate(data['plan']['modules']) for u in m['units']}


def reference(unit,current,mapping):
    return f'U{unit:03}' if mapping[unit]==current else f'M{mapping[unit]:03}.U{unit:03}'


def module_source(index,data,units,mapping):
    selected=data['plan']['modules'][index]['units']
    imports=sorted({mapping[d] for u in selected for d in units[u]['dependencies'] if mapping[d]!=index})
    lines=['From Coq Require Import List NArith.',
           'From BBB24 Require Import Statement Spec Census Pipeline StateOnlyCloseout FamilyIndex Symmetry.',
           'From BBB24Burn10StateCensus Require Import StateCensus.',
           f'From {NAMESPACE} Require Import Join'+(' '+' '.join(f'M{i:03}' for i in imports) if imports else '')+'.',
           'Import ListNotations.']
    for uid in selected:
        unit=units[uid];deps=unit['dependencies'];names={d:reference(d,index,mapping) for d in deps}
        raw_ids={v:i for i,v in enumerate(unit['unresolved'])}
        lines += [f'Module U{uid:03}.']
        for i,value in enumerate(unit['unresolved']):
            lines.append(f'Definition raw_{i} := machine_of_codes [{code_list(value)}].')
        lines += ['Definition local_frontier : list TM := ['+';'.join(f'raw_{i}' for i in range(len(raw_ids)))+'].',
                  'Definition dependency_frontiers : list (list TM) := ['+';'.join(names[d]+'.frontier' for d in deps)+'].',
                  'Definition frontier := local_frontier ++ concat dependency_frontiers.',
                  'Definition dependency_roots : list TM := ['+';'.join(names[d]+'.family' for d in deps)+'].',
                  'Definition lookup_board := local_frontier ++ dependency_roots.',
                  'Definition index := family_index lookup_board.',
                  'Definition leaf_check := state_lookup_check index.']
        depths=[]
        for i,node in enumerate(unit['nodes']):
            if node[0]==0:
                _,mirrored,anchor,period,width=node
                body=f'StateCycle StateLookup {str(bool(mirrored)).lower()} {anchor} {period} {width}';depth=1
            elif node[0]==1:
                source=f'raw_{raw_ids[node[1]]}'
                body=f'StateLeaf StateLookup (state_lookup (family_key {source}) P123 false)';depth=1
            elif node[0]==2:
                _,dep,value=node;assert value==units[dep]['machine']
                body=f'StateLeaf StateLookup (state_lookup (family_key {names[dep]}.family) P123 false)';depth=1
            else:
                _,anchor,children=node
                assert len(children)==16 and all(0<=c<i for c in children)
                body=f'StateBranch StateLookup {anchor} ['+';'.join(f'node_{c}' for c in children)+']'
                depth=1+max(depths[c] for c in children)
            depths.append(depth);lines.append(f'Definition node_{i} : StateCert StateLookup := {body}.')
        depth=depths[unit['root']]
        lines += [f'Definition family := machine_of_codes [{code_list(unit["machine"])}].',
                  f'Definition certificate := node_{unit["root"]}.',
                  'Local Transparent scoreN.',
                  f'Lemma checked : state_verify scoreN StateLookup leaf_check {depth} family certificate = true.',
                  'Proof. vm_compute. reflexivity. Qed.',
                  'Local Opaque scoreN.',
                  'Lemma lookup_sound : StateBoardSound score frontier -> StateBoardSound score lookup_board.',
                  'Proof. intros H.',
                  '  destruct (frontier_parts score local_frontier dependency_frontiers H) as [HL HD].']
        for i,d in enumerate(deps):
            tail='HD' if i==0 else f'HT{i-1}'
            lines.append(f'  inversion {tail} as [| ? ? H{i} HT{i}]; subst; clear {tail}.')
        lines += ['  apply board_app; [exact HL|].','  unfold dependency_roots.']
        for i,d in enumerate(deps):
            lines += [f'  apply board_cons; [exact ({names[d]}.sound H{i})|].']
        lines += ['  apply board_nil.','Qed.',
                  'Theorem sound : StateBoardSound score frontier ->',
                  '  forall complete, TM_le family complete -> QHBound score complete.',
                  'Proof. intros H.',
                  '  exact (state_verify_sound scoreN StateLookup leaf_check',
                  '    (fun f w => state_lookup_sound score lookup_board f w (lookup_sound H))',
                  f'    {depth} family certificate checked).',
                  'Qed.',f'End U{uid:03}.']
    lines += [f'Print Assumptions U{selected[-1]:03}.sound.']
    return '\n'.join(lines)+'\n',imports


def ensure_dependencies():
    required=['StateBranchCloseout','FamilyIndex','OrbitCloseout','Census','StateOnlyCloseout']
    if any(not (ROOT/f'theories/{name}.vo').exists() for name in required):
        subprocess.run(['make','-C',str(ROOT),'Makefile.coq'],check=True)
        subprocess.run(['make','-C',str(ROOT),'-f','Makefile.coq',*[f'theories/{name}.vo' for name in required]],check=True)
    current=PROTOTYPE/'current-proof-receipt.json'
    if not current.exists() or not (PROTOTYPE/'RootBridge.vo').exists():
        subprocess.run(['python3',str(ROOT/'tools/check_burn10_state_census_prototype.py')],check=True)
    receipt=ROOT/json.loads(current.read_text())['kernel_receipt']
    kernel._load_receipt(receipt)
    return receipt


def checked_module(name,source,paths,cache,timeout):
    path=BUILD/f'{name}.v';done=BUILD/f'{name}-current.json'
    if done.exists() and path.exists() and path.read_text()==source:
        old=json.loads(done.read_text());receipt=ROOT/old['kernel_receipt']
        if old['input_sha256']==sha(INPUT) and sha(receipt)==old['kernel_receipt_sha256']:
            evidence=kernel._load_receipt(receipt)
            if kernel.snapshot([path],paths)==evidence['snapshot']:
                print('Resumed',name,flush=True);return old
    path.write_text(source)
    flags=[arg for p,ns in paths for arg in ('-Q',str(p),ns)]
    sources=dependency_hashes([path],flags)
    protected={p:sha(p.with_suffix('.vo')) for p in (ROOT/k for k in sources)
               if p.suffix=='.v' and p!=path}
    start=time.monotonic()
    with (BUILD/f'{name}-compile.log').open('w') as log:
        subprocess.run(['coqc','-w','-abstract-large-number','-native-compiler','no',*flags,str(path)],
                       stdout=log,stderr=subprocess.STDOUT,check=True,timeout=timeout)
    elapsed=round(time.monotonic()-start,3)
    receipt,log=kernel.fresh_paths(BUILD,name+'-audit')
    audit=kernel.audit([NAMESPACE+'.'+name],[path],paths,receipt,log,cache=cache,timeout=900)
    assert all(sha(ROOT/p)==h for p,h in sources.items())
    assert all(sha(p.with_suffix('.vo'))==h for p,h in protected.items())
    result=dict(input_sha256=sha(INPUT),source_sha256=sources,compile_seconds=elapsed,
                audit_seconds=audit['elapsed_seconds'],checked_modules=len(audit['checked_modules']),
                reused_modules=len(audit['reused_modules']),kernel_receipt=str(receipt.relative_to(ROOT)),
                kernel_receipt_sha256=sha(receipt),object_sha256=sha(path.with_suffix('.vo')))
    dump(done,result)
    print(name,'compile',elapsed,'audit',audit['elapsed_seconds'],'new',len(audit['checked_modules']),flush=True)
    return result


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--prepare',action='store_true')
    parser.add_argument('--scope',choices=('pilot','blank'),default='pilot')
    parser.add_argument('--timeout',type=int,default=180)
    args=parser.parse_args();BUILD.mkdir(parents=True,exist_ok=True)
    if args.prepare and not INPUT.exists():prepare()
    data=json.loads(INPUT.read_text());input_sha=sha(INPUT)
    assert all(sha(ROOT.parent/p)==h for p,h in data['source_sha256'].items())
    status('native_reconstruction',scope=args.scope)
    trace=ensure_trace(data);units=reconstruct(data,trace);mapping=unit_module(data)
    assert sha(trace)==data['capture']['certificates_sha256']
    base=ensure_dependencies()
    paths=[(ROOT/'theories','BBB24'),(PROTOTYPE,'BBB24Burn10StateCensus'),(BUILD,NAMESPACE)]
    results={}
    status('generic_join',scope=args.scope)
    results['Join']=checked_module('Join',SOURCE.read_text(),paths,[base],args.timeout)
    target=data['pilot_unit'] if args.scope=='pilot' else data['plan']['root_unit']
    wanted=set()
    def include(u):
        module=mapping[u]
        if module in wanted:return
        wanted.add(module)
        for v in data['plan']['modules'][module]['units']:
            for dep in units[v]['dependencies']:include(dep)
    include(target)
    for index in sorted(wanted):
        name=f'M{index:03}';source,deps=module_source(index,data,units,mapping)
        status('module_replay',scope=args.scope,module=name,finished_modules=len(results)-1,total_modules=len(wanted))
        cache=[base,ROOT/results['Join']['kernel_receipt']]
        cache += [ROOT/results[f'M{i:03}']['kernel_receipt'] for i in deps]
        results[name]=checked_module(name,source,paths,cache,args.timeout)
    module=f'M{mapping[target]:03}';unit=f'{module}.U{target:03}'
    visited=set()
    def collect(u):
        if u in visited:return
        visited.add(u)
        for d in units[u]['dependencies']:collect(d)
    collect(target);raw_count=sum(len(units[u]['unresolved']) for u in visited)
    final='ConditionalPilot' if args.scope=='pilot' else 'ConditionalBlank'
    source='\n'.join(['From Coq Require Import List NArith.',
        'From BBB24 Require Import Statement Spec Census StateOnlyCloseout.',
        f'From {NAMESPACE} Require Import {module}.',
        f'Definition frontier := {unit}.frontier.',f'Definition family := {unit}.family.',
        f'Lemma frontier_count : length frontier = {raw_count}.',
        'Proof. vm_compute. reflexivity. Qed.',
        'Local Opaque scoreN.',
        'Theorem sound : StateBoardSound score frontier -> forall complete,',
        '  TM_le family complete -> QHBound score complete.',
        f'Proof. exact {unit}.sound. Qed.',
        'Print Assumptions sound.'])+'\n'
    status('aggregate_audit',scope=args.scope,total_modules=len(wanted))
    results[final]=checked_module(final,source,paths,[ROOT/results[module]['kernel_receipt']],args.timeout)
    flags=[arg for p,ns in paths for arg in ('-Q',str(p),ns)]
    sources=dependency_hashes([BUILD/f'{final}.v'],flags)
    for path in [Path(__file__),ROOT/'tools/triage.py',ROOT/'tools/check_shadow_links.py',ROOT/'tools/kernel_audit_cache_v3.py',SOURCE]:
        sources[str(path.relative_to(ROOT))]=sha(path)
    stable=dict(scope='Conditional '+args.scope+' census at scoreN; explicit frontier hypothesis, no discharged root or global bound.',
                input_sha256=input_sha,source_sha256=sources,new_state_families=0,new_instruction_families=0,
                global_upper_bound_proved=False,bound='scoreN',scoreN=205770076433044242247860,
                root_family=data['plan']['units'][target]['machine'],frontier_families=raw_count,
                certificate_units=len(visited),proof_modules=len(wanted),theorem=NAMESPACE+'.'+final+'.sound',
                required_hypothesis='StateBoardSound score frontier',
                exact_native_unit_frontier_and_dependency_hashes=True)
    result=dict(stable,modules=results,total_compile_seconds=round(sum(r['compile_seconds'] for r in results.values()),3),
                total_audit_seconds=round(sum(r['audit_seconds'] for r in results.values()),3),
                aggregate_receipt=results[final]['kernel_receipt'],aggregate_receipt_sha256=results[final]['kernel_receipt_sha256'])
    report=ROOT/f'research/burn13-state-census-{args.scope}-checked.json'
    if report.exists():
        old=json.loads(report.read_text());assert all(old[k]==v for k,v in stable.items())
    else:dump(report,result)
    assert sha(INPUT)==input_sha and all(sha(ROOT/p)==h for p,h in sources.items())
    dump(BUILD/f'{args.scope}-current-proof-receipt.json',result)
    status('complete',scope=args.scope,frontier_families=raw_count,proof_modules=len(wanted),report=str(report.relative_to(ROOT)))
    print(json.dumps({k:v for k,v in result.items() if k not in ['source_sha256','modules']},indent=2),flush=True)


if __name__=='__main__':
    try:main()
    except BaseException as error:
        status('failed',error=repr(error));raise
