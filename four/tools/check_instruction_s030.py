"""Replay S030's exact instruction score and all-completion census board.

Original state sources and the generic tail lemma are reconstructed unchanged
from frozen source pins. Native simulation and historical proof objects are
unnecessary. Every replay ends with full recursive stock coqchk, including both
old and new regressions. Generated sources and current receipts stay in build/.
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
NS = 'BBB24InstructionS030'
PREFIX = ROOT / 'research/instruction-s030'


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def artifact(suffix):
    return PREFIX.with_name(PREFIX.name + '-' + suffix)


def exact(path, text):
    if path.exists() and path.read_text() != text:
        raise ValueError('Frozen artifact differs: ' + str(path))
    if not path.exists():
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-root', type=Path, default=ROOT,
                        help='Shared four/ source root; defaults to this checkout')
    parser.add_argument('--timeout', type=int, default=180)
    parser.add_argument('--audit-timeout', type=int, default=1800)
    args = parser.parse_args()
    if min(args.timeout, args.audit_timeout) < 1:
        parser.error('Positive budgets required')
    resource.setrlimit(resource.RLIMIT_AS, (3 * 1024**3, 3 * 1024**3))
    resource.setrlimit(resource.RLIMIT_STACK, (64 * 1024**2, 64 * 1024**2))
    shared = args.source_root.resolve()
    sys.path.insert(0, str(shared / 'tools'))
    import kernel_audit_cache_v3 as kernel
    build = ROOT / 'build/instruction-s030'
    proof, state, helper = (build / name for name in ('proof', 'state-source', 'tail-helper'))
    inp, report, inventory = map(artifact, ('input.json', 'checked.json', 'machines.json'))
    data = json.loads(inp.read_text())
    if data['rows'] != [dict(machine='1LB2LA1LA2LB_2RB3RA0LB0LA',code=44979812,id='tr24-44979812')]:
        raise ValueError('Unexpected exact S030 inventory')
    if (data['instruction_score'], data['common_bound']) != (1367361263049, 2199023255552):
        raise ValueError('Unexpected S030 instruction or registration bound')
    inventory_text = json.dumps(dict(rows=[dict(machine=data['rows'][0]['machine'])]), indent=2) + '\n'
    if inventory.read_text() != inventory_text:
        raise ValueError('Frozen S030 machine inventory differs')
    protected = {p: sha(p) for p in (inp, inventory, Path(__file__).resolve())}
    original_input = shared / data['source_input']
    if sha(original_input) != data['source_input_sha256']:
        raise ValueError('Original state input differs')
    protected[original_input] = sha(original_input)
    original = json.loads(original_input.read_text())
    files = []
    for name in ('Counter.v', 'BinaryBridge.v', 'Trace.v', 'Final.v', 'Regression.v'):
        relative = 'proof-sources/burn25-s030-finite/' + name
        source = shared / relative
        expected = data['required_original_sources_sha256'][relative]
        if original['template_sha256'][relative] != expected or sha(source) != expected:
            raise ValueError('Original state source differs: ' + relative)
        protected[source] = expected
        target = state / name
        exact(target, source.read_text())
        files.append(target)
    relative = 'proof-sources/instruction-tails/SingleInstruction.v'
    source = shared / relative
    if sha(source) != data['required_original_sources_sha256'][relative]:
        raise ValueError('Generic instruction-tail helper differs')
    protected[source] = sha(source)
    target = helper / 'SingleInstruction.v'
    exact(target, source.read_text());files.append(target)
    for name in ('InstructionTail.v', 'Board.v', 'Regression.v', 'Inventory.v'):
        relative = 'proof-sources/instruction-s030/' + name
        source = ROOT / relative
        if sha(source) != data['templates_sha256'][relative]:
            raise ValueError('New instruction proof source differs: ' + relative)
        protected[source] = sha(source)
        target = proof / name
        exact(target, source.read_text());files.append(target)
    assumptions = proof / 'Assumptions.v'
    exact(assumptions, '''From BBB24InstructionS030 Require Import Inventory InstructionTail.
Require Import BBB24Burn25S030Finite.Regression.
Set Printing All.
Print Assumptions InstructionTail.s30_instruction_exact.
Print Assumptions Inventory.sound.
''')
    files.append(assumptions)
    loadpaths = [(shared / 'theories', 'BBB24'), (state, 'BBB24Burn25S030Finite'),
                 (helper, 'BBB24InstructionTails'), (proof, NS)]
    flags = [arg for directory, ns in loadpaths for arg in ('-Q', str(directory), ns)]
    timings = {}
    for path in files:
        started = time.monotonic()
        with path.with_suffix('.log').open('w') as log:
            subprocess.run(['coqc','-q','-w','-abstract-large-number','-native-compiler','no',
                            *flags,str(path)],stdout=log,stderr=subprocess.STDOUT,
                           timeout=args.timeout,check=True)
        timings[str(path.relative_to(build))] = round(time.monotonic()-started,3)
        print('Compiled ' + str(path.relative_to(build)),flush=True)
    actual_assumptions = sorted(set(re.findall(r'(?m)^([A-Za-z_][A-Za-z_0-9.]*)\s*\n\s*:',
                                                assumptions.with_suffix('.log').read_text())))
    if actual_assumptions != ['FunctionalExtensionality.functional_extensionality_dep']:
        raise ValueError('Unexpected printed assumptions: ' + str(actual_assumptions))
    descriptor = dict(id='instruction_s030',scope='both',rows=1,state_bound=data['common_bound'],
        instruction_bound=data['common_bound'],module=NS+'.Inventory',board='board',
        sound='sound',small_sound='small_sound',was_pending='was_pending',
        proof_source='build/instruction-s030/proof/Inventory.v',
        exact_inventory_theorem=NS+'.Inventory.inventory_exact',
        inventories=[dict(path='research/instruction-s030-machines.json',format='rows')],
        load_paths=[dict(path=str(p.relative_to(ROOT)),namespace=ns)for p,ns in loadpaths[1:]])
    snapshot = kernel.snapshot(files,loadpaths)
    sources = {}
    for item in snapshot['graph'].values():
        path = Path(item['source'])
        if path.is_relative_to(ROOT):
            sources[str(path.relative_to(ROOT))] = item['source_sha256']
        elif path.is_relative_to(shared):
            sources[str(path.relative_to(shared))] = item['source_sha256']
    sources['tools/check_instruction_s030.py'] = sha(__file__)
    inputs = {'research/instruction-s030-input.json':sha(inp),
              data['source_input']:sha(original_input),**data['templates_sha256'],
              **data['required_original_sources_sha256']}
    stable = dict(inputs_sha256=inputs,source_sha256=sources,descriptor=descriptor,
        inventory_sha256=sha(inventory),checked_instruction_families=1,checked_state_families=1,
        new_instruction_families=1,new_state_families=0,actual_assumptions=actual_assumptions,
        exact_instruction_score=data['instruction_score'],last_instruction_index=data['last_instruction_index'])
    previous = json.loads(report.read_text()) if report.exists() else None
    if previous and any(previous[key] != value for key,value in stable.items()):
        raise ValueError('Frozen S030 report differs from replay inputs')
    if previous:protected[report]=sha(report)
    receipt,log=kernel.fresh_paths(build,'kernel-audit');started=time.monotonic()
    audit=kernel.audit([NS+'.Inventory',NS+'.Assumptions'],[files[-2],files[-1]],loadpaths,
                       receipt,log,recursive=True,timeout=args.audit_timeout)
    required={NS+'.Regression','BBB24Burn25S030Finite.Regression'}
    if not required<=set(audit['checked_modules']):
        raise ValueError('Kernel audit omitted required regression controls')
    if any(sha(p)!=expected for p,expected in protected.items()):
        raise ValueError('Frozen proof source/input changed during replay')
    result=dict(stable,scope='One exact S030 instruction family; every completion covered.',
        compile_seconds=timings,audit_seconds=round(time.monotonic()-started,3),
        kernel_audit='Full recursive stock coqchk, including old and new regression modules.',
        kernel_receipt=str(receipt.relative_to(ROOT)),kernel_receipt_sha256=sha(receipt),
        kernel_log_sha256=sha(log),checked_modules=len(audit['checked_modules']),
        reused_modules=len(audit['reused_modules']),
        object_sha256={str(p.with_suffix('.vo').relative_to(ROOT)):sha(p.with_suffix('.vo'))for p in files})
    if previous is None:exact(report,json.dumps(result,indent=2,sort_keys=True)+'\n')
    (build/'current-proof-receipt.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print('S030 exact instruction score 1367361263049: full recursive kernel audit passed.',flush=True)


if __name__=='__main__':
    main()
