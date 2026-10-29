"""Replay exact S071 from a compact finite FAR certificate and audit its census wrapper.

The native witness is untrusted finite input. Pure Coq proves finite closure,
the forty concrete local block computations, and coverage of every run step.
The final inventory covers all completions of the exact complete table. A fresh
recursive kernel audit is required; prior reports and inventories stay frozen.
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
from generate_burn43_s071_far_data import render_data, WITNESS_SHA256, DATA_SHA256
import check_burn9_context_marker as wrappers
import kernel_audit_cache_v3 as kernel

ROOT = Path(__file__).resolve().parents[1]
BUILD = ROOT / 'build/burn43-s071-far/proof'
NS = 'BBB24Burn43S071FAR'
PREFIX = ROOT / 'research/burn43-s071-far'
MACHINE = '1LB2RA3LA2RB_0RB3LB0LA1RA'
MODULES = ['Programs', 'Progress', 'FARForward', 'Sparse', 'DataSchema',
           'Checker', 'CheckerSound', 'BlockMicro', 'LocalTable', 'SafeCover',
           'ZeroBridge', 'MacroBridge', 'Data', 'CheckActual', 'ActualClosed',
           'NoSpinout', 'ActualNoSpinout', 'Example00', 'Board', 'Inventory']
TEMPLATES = [name + '.v' for name in MODULES if name not in ('Data', 'Example00', 'Board', 'Inventory')]


def artifact(suffix):
    return PREFIX.with_name(PREFIX.name + '-' + suffix)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def exact(path, text):
    if path.exists() and path.read_text() != text:
        raise ValueError('Frozen artifact differs: ' + str(path))
    if not path.exists():
        path.write_text(text)


def example(row):
    assert row['machine'] == MACHINE
    table = ';'.join(map(str, codes(MACHINE)))
    return f'''From Coq Require Import List NArith.
From BBB24 Require Import Statement Spec Pipeline.
From {NS} Require Import Programs Progress ActualNoSpinout.
Import ListNotations.
Definition machine_0 := s71_tm.
Lemma exact_complete_table : forall q s,
 machine_0 q s = machine_of_codes [{table}] q s.
Proof. intros q s;destruct q,s;reflexivity. Qed.
Theorem nonhalt_0 : NonHalt machine_0.
Proof. exact s71_nonhalt. Qed.
Theorem state_zero_0 : QHBound 0 machine_0.
Proof. exact c54_s071_state_zero. Qed.
Print Assumptions exact_complete_table.
Print Assumptions state_zero_0.
'''


def board(rows):
    return wrappers.board(rows).replace('From ' + wrappers.NS + ' Require Import Example',
                                        'From ' + NS + ' Require Import Example')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--timeout', type=int, default=600)
    parser.add_argument('--audit-timeout', type=int, default=3600)
    args = parser.parse_args()
    if min(args.timeout, args.audit_timeout) <= 0:
        parser.error('Positive budgets required')
    resource.setrlimit(resource.RLIMIT_AS, (3 * 1024**3, 3 * 1024**3))
    BUILD.mkdir(parents=True, exist_ok=True)
    inp = artifact('proof-input.json')
    report = artifact('checked.json')
    invpath = artifact('machines.json')
    old = json.loads(report.read_text()) if report.exists() else None
    protected = {p: sha(p) for p in (report, invpath) if p.exists()}
    data = json.loads(inp.read_text())
    rows = data['rows']
    assert data['metadata_revision'] == 1 and data['state_bound'] == 0
    assert rows == [dict(machine=MACHINE, code=2480798428)]
    assert codes(MACHINE) == [5, 10, 12, 11, 3, 13, 0, 6]
    assert rows[0]['code'] == sum(v * 17**i for i, v in enumerate(codes(MACHINE)))
    # A replay may only reuse the exact frozen inventory represented by Coq.
    # Validate metadata before writing or compiling any generated source.
    inventory = json.dumps(dict(rows=[dict(machine=MACHINE)]), indent=2) + '\n'
    inventory_digest = hashlib.sha256(inventory.encode()).hexdigest()
    if invpath.exists() and invpath.read_bytes() != inventory.encode():
        raise ValueError('Frozen inventory differs: ' + str(invpath))
    if old is not None:
        if not invpath.is_file():
            raise ValueError('Frozen checked report is missing its inventory')
        if old.get('inventory_sha256') != inventory_digest:
            raise ValueError('Frozen checked report inventory digest differs')
    checkpoint = ROOT / data['frozen_checkpoint']
    assert sha(checkpoint) == data['frozen_checkpoint_sha256']
    assert data['frozen_checkpoint_sha256'] == 'a99ef3991f68ae537039424b5c8a6e7bf762a32e9cba22fa120c93daeef2c709'
    assert len(checkpoint.read_text().splitlines()) == 78
    assert data['frozen_checkpoint_index'] == 70
    assert checkpoint.read_text().splitlines()[70] == MACHINE
    prior = ROOT / data['prior_remaining_file']
    assert sha(prior) == data['prior_remaining_sha256']
    assert prior.read_text() == MACHINE + '\n'
    witness_path = ROOT / data['witness_file']
    traces_path = ROOT / data['microtraces_file']
    assert sha(witness_path) == data['witness_sha256'] == WITNESS_SHA256
    assert sha(traces_path) == data['microtraces_sha256'] == '2eefdae4985c181edeb9de47192e65107bdf0b50802b890ed5a9d34e5d2bc542'
    witness = json.loads(witness_path.read_text())
    traces = json.loads(traces_path.read_text())
    assert witness['dfa_states'] == 3986 and len(witness['h3']) == 4155
    assert len(witness['h2']) == 4055 and len(witness['push']) == 4178
    assert witness['zero_context'] == [False, True] + [False] * 3984
    assert traces['machine'] == MACHINE and traces['source_witness_sha256'] == WITNESS_SHA256
    assert traces['words'] == witness['words'] and traces['block_length'] == 2
    assert len(traces['cases']) == 40 and traces['max_steps'] == 5
    assert traces['all_cases_exit'] is True and traces['local_loop_cases'] == traces['target_cases'] == 0
    assert traces['total_distinct_case_microsteps'] == 83
    template_dir = ROOT / 'proof-sources/burn43-s071-far'
    templates = [template_dir / name for name in TEMPLATES]
    template_pins = {str(p.relative_to(ROOT)): sha(p) for p in templates}
    assert template_pins == data['template_sha256']
    rendered = render_data(witness)
    assert hashlib.sha256(rendered.encode()).hexdigest() == data['generated_data_sha256'] == DATA_SHA256
    load_paths = [(ROOT / 'theories', 'BBB24'), (BUILD, NS)]
    flags = [x for path, ns in load_paths for x in ('-Q', str(path), ns)]
    for path in templates:
        exact(BUILD / path.name, path.read_text())
    exact(BUILD / 'Data.v', rendered)
    exact(BUILD / 'Example00.v', example(rows[0]))
    exact(BUILD / 'Board.v', board(rows))
    descriptor = dict(id='burn43_s071_far', scope='state', rows=1, state_bound=0,
                      instruction_bound=None, module=NS + '.Inventory', board='board',
                      small_sound='small_sound', sound='sound', was_pending='was_pending',
                      proof_source=str((BUILD / 'Inventory.v').relative_to(ROOT)),
                      exact_inventory_theorem=NS + '.Inventory.inventory_exact',
                      inventories=[dict(path=str(invpath.relative_to(ROOT)), format='rows')],
                      load_paths=[dict(path=str(BUILD.relative_to(ROOT)), namespace=NS)])
    exact(BUILD / 'Inventory.v', inventory_source(dict(descriptor, module=NS + '.Board', machines=[MACHINE])))
    files = [BUILD / (name + '.v') for name in MODULES]
    sources = dependency_hashes(files, flags)
    for name in ('check_burn43_s071_far.py', 'generate_burn43_s071_far_data.py',
                 'check_burn9_context_marker.py', 'check_campaign.py', 'check_shadow_links.py',
                 'generate_pipeline_examples.py', 'kernel_audit_cache_v3.py'):
        sources['tools/' + name] = sha(ROOT / 'tools' / name)
    inputs = {str(p.relative_to(ROOT)): sha(p) for p in (inp, checkpoint, prior, witness_path, traces_path)}
    stable = dict(inputs_sha256=inputs, template_sha256=template_pins, source_sha256=sources,
                  descriptor=descriptor, inventory_sha256=inventory_digest,
                  checked_state_families=1, checked_instruction_families=0,
                  prior_remaining_count=1, prior_remaining_sha256=sha(prior),
                  frozen_checkpoint_index=70, generated_data_sha256=DATA_SHA256,
                  block_cells=2, local_trace_cases=40, maximum_local_trace_steps=5,
                  generic_forward_closure_checked=True, concrete_run_coverage_checked=True)
    if old:
        assert all(old[k] == v for k, v in stable.items())
    timings = {}
    for path in files:
        begin = time.monotonic()
        with path.with_suffix('.log').open('w') as log:
            subprocess.run(['coqc', '-w', '-abstract-large-number', '-native-compiler', 'no',
                            *flags, str(path)], stdout=log, stderr=subprocess.STDOUT,
                           check=True, timeout=args.timeout)
        timings[path.stem] = round(time.monotonic() - begin, 3)
        print('Compiled ' + path.stem + ': ' + str(timings[path.stem]) + 's', flush=True)
    receipt, log = kernel.fresh_paths(BUILD, 'kernel-audit')
    begin = time.monotonic()
    audit = kernel.audit([NS + '.Inventory'], [files[-1]], load_paths, receipt, log,
                         recursive=True, timeout=args.audit_timeout)
    assert audit['kind'] == 'recursive' and audit['reused_modules'] == [] and audit['parents'] == []
    assert {NS + '.' + name for name in MODULES} <= set(audit['checked_modules'])
    assert all(sha(ROOT / p) == h for p, h in {**inputs, **sources, **template_pins}.items())
    assert all(sha(p) == h for p, h in protected.items())
    current = dict(stable, scope='Exact complete S071 FAR state-zero family, every completion; no instruction claim.',
                   compile_seconds=timings, kernel_receipt=str(receipt.relative_to(ROOT)),
                   kernel_receipt_sha256=sha(receipt), kernel_audit='Full fresh recursive coqchk; no reused modules.',
                   audit_seconds=round(time.monotonic() - begin, 3),
                   checked_modules=len(audit['checked_modules']), reused_modules=0,
                   object_sha256={str(p.with_suffix('.vo').relative_to(ROOT)): sha(p.with_suffix('.vo')) for p in files})
    if old is None:
        exact(invpath, inventory)
        exact(report, json.dumps(current, indent=2, sort_keys=True) + '\n')
    (BUILD / 'current-proof-receipt.json').write_text(json.dumps(current, indent=2, sort_keys=True) + '\n')
    print('Complete S071 FAR state family fully audited.', flush=True)


if __name__ == '__main__':
    main()
