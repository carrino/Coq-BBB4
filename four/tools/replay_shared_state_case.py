"""Rebuild three frozen shared-library cases without historical object-byte pins.

Frozen source/input/report/inventory bytes remain authoritative. Current dependency
objects must belong to a validated current full-recursive receipt. Every replay
compiles the exact original Coq sources and performs a new full recursive audit;
no dependency is skipped and no original report or driver is modified.
"""
import argparse
import hashlib
import importlib
import json
import resource
import subprocess
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CASES = {
    'burn12-history-marker-next1a': ('bda158c25f8ddcc6977adbd9f568976399f06890c224f39462d67ad151d3e87a', 'burn12-history-marker'),
    'burn12-history-marker-next1b': ('28e9fe480dc612814108fa712cf8b9130e564a50eca2ef4298ad57b847999d78', 'burn12-history-marker'),
    'burn17-double-zero-rank': ('9f4e35cf2f4c7a0da64726f393180c22e7abd454217a2e1f4802506ec0536838', 'burn17-binary-rank'),
}


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def require(test, message):
    if not test:
        raise ValueError(message)


def pins(group):
    for name, expected in group.items():
        path = ROOT / name
        require(path.is_file() and sha(path) == expected, 'Frozen file missing or changed: ' + name)


def exact(path, content):
    data = content.encode()
    if path.exists():
        require(path.read_bytes() == data, 'Generated source differs: ' + str(path))
    else:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)


def source_groups(report, generated=False):
    for name in ('inputs_sha256', 'template_sha256', 'source_sha256'):
        group = report.get(name, {})
        pins({p: h for p, h in group.items() if generated or not p.startswith('build/')})
    inventory = ROOT / report['descriptor']['inventories'][0]['path']
    require(sha(inventory) == report['inventory_sha256'], 'Frozen inventory changed')


def dependency_current(name, frozen, kernel):
    build = ROOT / 'build' / name / 'proof'
    current_path = build / 'current-proof-receipt.json'
    require(current_path.is_file(), 'Replay the shared prerequisite first: ' + name)
    current = json.loads(current_path.read_text())
    for key in ('inputs_sha256', 'template_sha256', 'source_sha256', 'descriptor',
                'inventory_sha256', 'checked_state_families', 'checked_instruction_families'):
        require(current.get(key) == frozen.get(key), 'Current dependency source/descriptor differs: ' + key)
    require(set(current['object_sha256']) == set(frozen['object_sha256']), 'Current dependency object inventory differs')
    pins(current['object_sha256'])
    source_groups(frozen, generated=True)
    receipt_path = ROOT / current['kernel_receipt']
    require(sha(receipt_path) == current['kernel_receipt_sha256'], 'Current dependency receipt changed')
    validation = kernel.ReceiptValidation()
    receipt = validation.load(receipt_path)
    require(receipt['kind'] == 'recursive' and receipt['parents'] == [] and receipt['reused_modules'] == [],
            'Dependency needs a current full recursive receipt without reuse')
    paths = [(ROOT / 'theories', 'BBB24')] + [(ROOT / p['path'], p['namespace']) for p in frozen['descriptor']['load_paths']]
    roots = [ROOT / frozen['descriptor']['proof_source']]
    if name == 'burn12-history-marker':
        roots.append(build / 'Regression.v')
    require(kernel.snapshot(roots, paths) == receipt['snapshot'], 'Stale dependency source/object/runtime closure')
    validation.recheck()
    return dict(path=current_path, sha256=sha(current_path), receipt=receipt_path,
                receipt_sha256=sha(receipt_path), validation=validation, roots=roots,
                paths=paths, snapshot=receipt['snapshot'])


def prepare(package):
    require(package in CASES, 'Unsupported shared case: ' + package)
    expected, dependency_name = CASES[package]
    report_path = ROOT / 'research' / (package + '-checked.json')
    require(sha(report_path) == expected, 'Frozen case report changed: ' + package)
    frozen = json.loads(report_path.read_text())
    source_groups(frozen)
    input_path = ROOT / 'research' / (package + '-proof-input.json')
    data = json.loads(input_path.read_text())
    rows = data['rows']
    require(data['state_bound'] == 0 and len(rows) == 1, 'Unexpected case scope')
    selection = ROOT / data['selection_report']
    require(sha(selection) == data['selection_sha256'], 'Selection changed')
    require(rows == json.loads(selection.read_text())['rows'], 'Selection rows differ')
    dependency_report = ROOT / 'research' / (dependency_name + '-checked.json')
    dep_key = 'generic_report_sha256' if dependency_name == 'burn12-history-marker' else 'dependency_report_sha256'
    require(sha(dependency_report) == data[dep_key], 'Frozen shared report changed')
    shared = json.loads(dependency_report.read_text())
    source_groups(shared)
    # Project Python is imported only after its frozen producer/source pins pass.
    campaign = importlib.import_module('check_campaign')
    codes = importlib.import_module('generate_pipeline_examples').codes
    kernel = importlib.import_module('kernel_audit_cache_v3')
    require(all(row['code'] == sum(v * 17**i for i, v in enumerate(codes(row['machine']))) for row in rows), 'Machine code mismatch')
    dependency = dependency_current(dependency_name, shared, kernel)
    build = ROOT / 'build' / package / 'proof'
    descriptor = frozen['descriptor']
    namespace = descriptor['module'].removesuffix('.Inventory')
    require(descriptor['proof_source'] == str((build / 'Inventory.v').relative_to(ROOT)), 'Unexpected descriptor source path')
    require(descriptor['rows'] == 1 and descriptor['state_bound'] == 0 and descriptor['scope'] == 'state', 'Descriptor scope differs')
    files = []
    if dependency_name == 'burn12-history-marker':
        pilot = importlib.import_module('check_burn12_history_marker')
        require(all(len(row['weights']) == 4 and row['weights'][0] == 0 and row['invariant'] == 'conditional'
                    and 0 < row['history_marker_mask'] < 256 for row in rows), 'Invalid history parameters')
        render_example = pilot.example
        board = pilot.board(rows).replace('From ' + pilot.NS + ' Require Import Example',
                                         'From ' + namespace + ' Require Import Example')
    else:
        producer = importlib.import_module('check_burn17_double_zero_rank')
        require(rows[0]['machine'] == producer.MACHINE and namespace == producer.NS, 'Unexpected binary-rank machine')
        for name in ('DoubleZeroRank.v', 'Regression.v'):
            template = ROOT / 'proof-sources' / package / name
            require(sha(template) == data['template_sha256'][str(template.relative_to(ROOT))], 'Template changed')
            target = build / name
            exact(target, template.read_text())
            files.append(target)
        require(data['template_sha256'] == frozen['template_sha256'], 'Template pin group differs')
        render_example, board = producer.example, producer.board(rows)
    for i, row in enumerate(rows):
        path = build / f'Example{i:02d}.v'
        exact(path, render_example(i, row))
        files.append(path)
    path = build / 'Board.v'
    exact(path, board)
    files.append(path)
    path = build / 'Inventory.v'
    exact(path, campaign.inventory_source(dict(descriptor, module=namespace + '.Board', machines=[r['machine'] for r in rows])))
    files.append(path)
    inventory = json.dumps(dict(rows=[dict(machine=r['machine']) for r in rows]), indent=2) + '\n'
    inventory_path = ROOT / descriptor['inventories'][0]['path']
    require(inventory_path.read_text() == inventory, 'Regenerated inventory differs')
    paths = [(ROOT / 'theories', 'BBB24')] + [(ROOT / p['path'], p['namespace']) for p in descriptor['load_paths']]
    flags = [part for p, ns in paths for part in ('-Q', str(p), ns)]
    sources = campaign.dependency_hashes(files, flags)
    sources.update({p: sha(ROOT / p) for p in frozen['source_sha256'] if p.startswith('tools/')})
    require(sources == frozen['source_sha256'], 'Regenerated source dependency closure differs')
    source_groups(frozen, generated=True)
    protected = {report_path: sha(report_path), dependency_report: sha(dependency_report),
                 inventory_path: sha(inventory_path), dependency['path']: dependency['sha256']}
    return dict(package=package, frozen=frozen, files=files, paths=paths, flags=flags,
                namespace=namespace, dependency=dependency, kernel=kernel, protected=protected)


def replay(context, timeout, audit_timeout):
    package, files, kernel = context['package'], context['files'], context['kernel']
    output = ROOT / 'build/shared-state-case-replay' / package
    output.mkdir(parents=True, exist_ok=True)
    timings = {}
    for path in files:
        started = time.monotonic()
        with (output / (path.stem + '.log')).open('w') as log:
            subprocess.run(['coqc', '-w', '-abstract-large-number', '-native-compiler', 'no',
                            *context['flags'], str(path)], stdout=log, stderr=subprocess.STDOUT,
                           check=True, timeout=timeout)
        timings[path.stem] = round(time.monotonic() - started, 3)
        print('Compiled ' + path.stem + ': ' + str(timings[path.stem]) + 's', flush=True)
    receipt, log = kernel.fresh_paths(output, 'kernel-audit')
    started = time.monotonic()
    namespace = context['namespace']
    audit = kernel.audit([namespace + '.Inventory'], [files[-1]], context['paths'], receipt, log,
                         recursive=True, timeout=audit_timeout)
    require(audit['kind'] == 'recursive' and audit['parents'] == [] and audit['reused_modules'] == [], 'Audit skipped dependencies')
    if package == 'burn17-double-zero-rank':
        require(namespace + '.Regression' in audit['checked_modules'], 'Regression omitted')
    dependency = context['dependency']
    dependency['validation'].recheck()
    require(kernel.snapshot(dependency['roots'], dependency['paths']) == dependency['snapshot'], 'Dependency changed during replay')
    source_groups(context['frozen'], generated=True)
    for path, expected in context['protected'].items():
        require(sha(path) == expected, 'Frozen/current prerequisite metadata changed: ' + str(path))
    record = dict(schema=1, package=package, scope=context['frozen']['scope'],
                  descriptor=context['frozen']['descriptor'], frozen_report_sha256=CASES[package][0],
                  inputs_sha256=context['frozen']['inputs_sha256'],
                  template_sha256=context['frozen'].get('template_sha256', {}),
                  source_sha256=context['frozen']['source_sha256'],
                  inventory_sha256=context['frozen']['inventory_sha256'],
                  replay_checker_sha256=sha(Path(__file__)), compile_seconds=timings,
                  audit_seconds=round(time.monotonic() - started, 3),
                  checked_modules=len(audit['checked_modules']), reused_modules=0,
                  dependency_current_receipt=str(dependency['path'].relative_to(ROOT)),
                  dependency_current_receipt_sha256=dependency['sha256'],
                  dependency_kernel_receipt_sha256=dependency['receipt_sha256'],
                  kernel_receipt=str(receipt.relative_to(ROOT)), kernel_receipt_sha256=sha(receipt),
                  current_runtime=audit['snapshot']['runtime'],
                  object_sha256={str(p.with_suffix('.vo').relative_to(ROOT)): sha(p.with_suffix('.vo')) for p in files})
    target = output / 'current-proof-receipt.json'
    target.write_text(json.dumps(record, indent=2, sort_keys=True) + '\n')
    print(package + ' compiled and fully recursively audited; no historical object-byte requirement.', flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--package', choices=sorted(CASES), required=True)
    parser.add_argument('--timeout', type=int, default=600)
    parser.add_argument('--audit-timeout', type=int, default=3600)
    args = parser.parse_args()
    if min(args.timeout, args.audit_timeout) < 1:
        parser.error('Positive budgets required')
    resource.setrlimit(resource.RLIMIT_AS, (3 * 1024**3, 3 * 1024**3))
    resource.setrlimit(resource.RLIMIT_STACK, (resource.RLIM_INFINITY, resource.RLIM_INFINITY))
    replay(prepare(args.package), args.timeout, args.audit_timeout)


if __name__ == '__main__':
    main()
