"""Replay five generic boundary-counter instruction families from frozen sources.

The B2-deleted machine is used only after each checked actual prefix. It halts
from blank, as a negative control verifies. Every replay covers all completions,
checks the exact inventory and original bootstrap membership, and performs full
recursive stock coqchk. Native diagnostics receive no proof credit.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import resource
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
NS = 'BBB24BoundaryNeighbors'
NAME = 'instruction-boundary-counter'


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def exact(path, text):
    if path.exists() and path.read_text() != text:
        raise ValueError('Frozen artifact differs: ' + str(path))
    if not path.exists():
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-root', type=Path, default=ROOT)
    parser.add_argument('--timeout', type=int, default=180)
    parser.add_argument('--audit-timeout', type=int, default=1800)
    args = parser.parse_args()
    if min(args.timeout, args.audit_timeout) < 1:
        parser.error('Positive replay budgets required')
    resource.setrlimit(resource.RLIMIT_AS, (3 * 1024**3, 3 * 1024**3))
    resource.setrlimit(resource.RLIMIT_STACK, (64 * 1024**2, 64 * 1024**2))
    shared = args.source_root.resolve()
    sys.path.insert(0, str(shared / 'tools'))
    import kernel_audit_cache_v3 as kernel
    from check_campaign import packed, inventory_source
    from instruction_residual import residual
    build = ROOT / 'build' / NAME
    proof = build / 'proof'
    artifact = lambda suffix: ROOT / 'research' / (NAME + '-' + suffix)
    inp, report, inventory = map(artifact, ('input.json', 'checked.json', 'machines.json'))
    data = json.loads(inp.read_text())
    machines = ['1LB2LB3RA3LB_2RB1LA' + b2 + '1RA' for b2 in ('0RB','1LA','1LB','3LA','3RA')]
    expected_rows = [dict(machine=m,code=packed(m),id='tr24-'+str(packed(m))) for m in machines]
    if (data['rows'] != expected_rows or (data['state_bound'],data['instruction_bound']) != (0,64) or
            data['entry_steps'] != [40,44,36,19,64] or data['entry_parameters'] != [1,1,1,0,1]):
        raise ValueError('Unexpected exact boundary-counter inventory or bounds')
    remaining, pins = residual(shared / data['baseline_report'], data['baseline_sha256'])
    if not set(machines) <= remaining:
        raise ValueError('Boundary-counter table outside frozen original remainder')
    inventory_text = json.dumps(dict(rows=[dict(machine=m) for m in machines]),indent=2)+'\n'
    if inventory.read_text() != inventory_text:
        raise ValueError('Frozen exact inventory differs')
    protected = {p:sha(p) for p in (inp,inventory,Path(__file__).resolve())}
    protected.update({shared/name:expected for name,expected in pins.items()})
    files = []
    for name in ('BoundaryKernel.v','Cases.v','Regression.v'):
        relative = 'proof-sources/' + NAME + '/' + name
        source = ROOT / relative
        if sha(source) != data['templates_sha256'][relative]:
            raise ValueError('Frozen proof source differs: ' + relative)
        protected[source] = sha(source)
        target = proof / name
        exact(target,source.read_text());files.append(target)
    descriptor = dict(id='instruction_boundary_counter',scope='both',rows=5,state_bound=0,instruction_bound=64,
        module=NS+'.Inventory',board='board',sound='sound',small_sound='small_sound',was_pending='was_pending',
        proof_source='build/'+NAME+'/proof/Inventory.v',exact_inventory_theorem=NS+'.Inventory.inventory_exact',
        inventories=[dict(path='research/'+NAME+'-machines.json',format='rows')],
        load_paths=[dict(path='build/'+NAME+'/proof',namespace=NS)])
    path = proof/'Inventory.v'
    exact(path,inventory_source({**descriptor,'module':NS+'.Cases','machines':machines})+
          '\nRequire Import '+NS+'.Regression.\n')
    files.append(path)
    assumptions = proof/'Assumptions.v'
    exact(assumptions,'From '+NS+' Require Import Inventory BoundaryKernel.\n'+
          'Print Assumptions main_next.\nPrint Assumptions Inventory.sound.\n')
    files.append(assumptions)
    loadpaths=[(shared/'theories','BBB24'),(proof,NS)]
    flags=[arg for directory,ns in loadpaths for arg in ('-Q',str(directory),ns)]
    timings={}
    for path in files:
        started=time.monotonic()
        with path.with_suffix('.log').open('w') as log:
            subprocess.run(['coqc','-q','-native-compiler','no',*flags,str(path)],stdout=log,
                           stderr=subprocess.STDOUT,timeout=args.timeout,check=True)
        timings[path.stem]=round(time.monotonic()-started,3)
        print('Compiled '+path.stem,flush=True)
    actual_assumptions=sorted(set(re.findall(r'(?m)^([A-Za-z_][A-Za-z_0-9.]*)\s*\n\s*:',
                                           assumptions.with_suffix('.log').read_text())))
    if actual_assumptions != ['FunctionalExtensionality.functional_extensionality_dep']:
        raise ValueError('Unexpected printed assumptions: '+str(actual_assumptions))
    snapshot=kernel.snapshot(files,loadpaths)
    sources={}
    for item in snapshot['graph'].values():
        path=Path(item['source'])
        if path.is_relative_to(ROOT):sources[str(path.relative_to(ROOT))]=item['source_sha256']
        elif path.is_relative_to(shared):sources[str(path.relative_to(shared))]=item['source_sha256']
    for name in ('check_campaign.py','instruction_residual.py','kernel_audit_cache_v3.py'):
        sources['tools/'+name]=sha(shared/'tools'/name)
    sources['tools/check_instruction_boundary_counter.py']=sha(__file__)
    stable=dict(inputs_sha256={**pins,'research/'+NAME+'-input.json':sha(inp),**data['templates_sha256']},
        source_sha256=sources,descriptor=descriptor,inventory_sha256=sha(inventory),
        checked_instruction_families=5,checked_state_families=5,new_instruction_families=5,new_state_families=0,
        actual_assumptions=actual_assumptions)
    previous=json.loads(report.read_text())if report.exists()else None
    if previous and any(previous[key]!=value for key,value in stable.items()):
        raise ValueError('Frozen report differs from replay inputs')
    if previous:protected[report]=sha(report)
    receipt,log=kernel.fresh_paths(build,'kernel-audit');started=time.monotonic()
    audit=kernel.audit([NS+'.Inventory',NS+'.Assumptions'],[files[-2],files[-1]],loadpaths,
                       receipt,log,recursive=True,timeout=args.audit_timeout)
    if NS+'.Regression'not in audit['checked_modules']:
        raise ValueError('Kernel audit omitted regression controls')
    if any(sha(p)!=expected for p,expected in protected.items()):
        raise ValueError('Frozen source/input changed during replay')
    result=dict(stable,scope='Five exact census families; every completion covered.',
        compile_seconds=timings,audit_seconds=round(time.monotonic()-started,3),
        kernel_audit='Full recursive stock coqchk, including regression controls.',
        kernel_receipt=str(receipt.relative_to(ROOT)),kernel_receipt_sha256=sha(receipt),kernel_log_sha256=sha(log),
        checked_modules=len(audit['checked_modules']),reused_modules=len(audit['reused_modules']),
        object_sha256={str(p.with_suffix('.vo').relative_to(ROOT)):sha(p.with_suffix('.vo'))for p in files})
    if previous is None:exact(report,json.dumps(result,indent=2,sort_keys=True)+'\n')
    (build/'current-proof-receipt.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print('Five boundary-counter instruction families: full recursive kernel audit passed.',flush=True)


if __name__=='__main__':
    main()
