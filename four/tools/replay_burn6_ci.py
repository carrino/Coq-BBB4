"""Replay the frozen burn6 campaign with bounded, exact-artifact audit phases.

The original replay plan, generators, theorem sources, and frozen reports are
unchanged. Only receipts created by this invocation's prerequisite commands
are considered. V3 validates their complete receipt DAGs and exact current
artifact closure before any dependency is reused. Missing prerequisite modules
are freshly checked in dependency order, at most sixteen per phase. Every
inventory wrapper is then freshly checked; the original final checker validates
the unchanged campaign with those receipts and freshly checks Campaign itself.
"""
import argparse
import hashlib
import importlib
import json
import os
from pathlib import Path
import resource
import subprocess
import sys
import time


def digest(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()


def json_paths(build):
    return {path.resolve() for path in build.rglob('*.json')}


def pinned_inputs(repo, report_path, plan_path):
    report = json.loads(report_path.read_text())
    paths = {report_path, plan_path}
    paths.update(repo / 'four' / name for name in report['inputs'])
    # These new orchestration tools are deliberately outside historical reports.
    # Pin them locally as well before any current-run receipts are produced.
    paths.update(repo / 'four/tools' / name for name in
                 ('replay_burn6_ci.py', 'check_campaign_next_audit.py',
                  'campaign_snapshot_dependencies.py'))
    # Generated build sources are reproduced by the unchanged final checker.
    paths.update(repo / 'four' / name for name in report['source_sha256']
                 if not (repo / 'four' / name).resolve().is_relative_to(repo / 'four/build'))
    return {str(path.resolve()): digest(path) for path in sorted(paths)}


def recheck_pins(pins):
    if any(digest(path) != expected for path, expected in pins.items()):
        raise ValueError('A frozen campaign input, helper, theorem source, or report changed')


def validate_current_receipts(kernel, build, baseline, current, roots, forbidden,
                              *, require_complete=True):
    """Select newly created local receipts and validate their complete ancestry.

    Raw JSON shape is only a discovery hint. V3 supplies the validation, and
    its exact source/object/runtime/dependency comparison supplies coverage.
    The new campaign modules must never arrive through a prerequisite cache.
    """
    validation = kernel.ReceiptValidation()
    choices = []
    build = build.resolve()
    for path in sorted(json_paths(build) - baseline):
        data = json.loads(path.read_text())
        if not isinstance(data, dict) or not (
                data.get('schema') == 1 and data.get('result') == 'passed'
                and isinstance(data.get('snapshot'), dict)
                and 'checked_modules' in data and 'log_sha256' in data):
            continue
        data = validation.load(path)
        if set(data['snapshot']['graph']) & forbidden:
            raise ValueError('A prerequisite receipt includes a new campaign module')
        gain = kernel._covered(current, [data])
        if gain:
            choices.append((path, gain))
    validation.recheck()
    for path in validation.artifacts:
        if not path.is_relative_to(build):
            raise ValueError('Audit receipt/log ancestry escapes the local build directory')
    covered = set().union(*(gain for _, gain in choices))
    required = set(current['graph']) - forbidden
    if require_complete and not required <= covered:
        raise ValueError('Current-run receipts do not cover all campaign prerequisites: '
                         + ', '.join(sorted(required - covered)))
    if not set(roots) <= set(current['graph']):
        raise ValueError('Campaign root/source mismatch')
    # Retain only a covering set; audit() revalidates every selected DAG afresh.
    selected, union = [], set()
    while covered - union:
        path, gain = max(choices, key=lambda item: len(item[1] - union))
        selected.append(path)
        union.update(gain)
        choices.remove((path, gain))
    validation.release()
    return selected


def covered_modules(kernel, current, caches):
    validation = kernel.ReceiptValidation()
    data = [validation.load(path) for path in caches]
    covered = kernel._covered(current, data)
    validation.recheck()
    return covered


def next_prerequisite_batch(graph, required, covered, size):
    """Choose at most size uncovered modules, after all their dependencies.

    No campaign wrapper can enter this phase. Every dependency must either be
    already V3-covered or occur earlier in this same explicit fresh batch.
    """
    if size <= 0 or not set(required) <= graph.keys() or not set(covered) <= graph.keys():
        raise ValueError('Invalid prerequisite audit scope or batch size')
    batch = []
    pending = set(required) - set(covered)
    while pending and len(batch) < size:
        available = set(covered) | set(batch)
        ready = sorted(name for name in pending
                       if set(graph[name]['dependencies']) <= available)
        if not ready:
            raise ValueError('Uncovered prerequisite dependency cycle or out-of-scope dependency')
        name = ready[0]
        batch.append(name)
        pending.remove(name)
    return batch


def require_fresh_modules(phase, modules):
    if (len(phase['checked_modules']) != len(modules)
            or set(phase['checked_modules']) != set(modules)):
        raise ValueError('A bounded phase did not freshly check exactly its declared modules')
    if set(modules) & set(phase['reused_modules']):
        raise ValueError('A new campaign module was reused instead of freshly checked')


def require_fresh_phase(phase, module):
    if phase['checked_modules'] != [module]:
        raise ValueError('A bounded phase did not freshly check exactly ' + module)
    if module in phase['reused_modules']:
        raise ValueError('A new campaign module was reused instead of freshly checked')


def fresh_directory(parent):
    parent.mkdir(parents=True, exist_ok=True)
    for index in range(1000000):
        path = parent / f'run-{index:06}'
        try:
            path.mkdir()
            return path
        except FileExistsError:
            pass
    raise ValueError('No unused CI replay directory')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, default=Path(__file__).resolve().parents[2])
    parser.add_argument('--jobs', type=int, default=2, choices=range(1, 9))
    parser.add_argument('--timeout', type=int, default=14400)
    parser.add_argument('--memory-mib', type=int, default=2816)
    args = parser.parse_args()
    if args.timeout <= 0 or args.memory_mib <= 0:
        parser.error('Resource limits must be positive')
    repo = args.repo.resolve()
    sys.path.insert(0, str(repo / 'four/tools'))
    rebuild = importlib.import_module('rebuild_campaign')
    campaign = importlib.import_module('campaign_next_boards')
    helpers = importlib.import_module('check_campaign_v2')
    kernel = importlib.import_module('kernel_audit_cache_v3')
    if rebuild.REPO != repo or campaign.ROOT != repo / 'four':
        raise ValueError('Imported campaign helpers belong to another repository')
    plan_path = repo / 'four/research/burn6-campaign-build.json'
    report_path = repo / 'four/research/burn6-campaign-summary.json'
    manifest_path = repo / 'four/research/burn6-campaign-input.json'
    build = repo / 'four/build'
    output = build / 'burn6-campaign'
    namespace = 'BBB24Burn6Campaign'
    pins = pinned_inputs(repo, report_path, plan_path)
    steps = rebuild.read_plan(plan_path, 'burn6-campaign')
    final = steps.pop('burn6-campaign')
    expected = ['python3', 'four/tools/check_campaign_next.py', '--manifest',
                'four/research/burn6-campaign-input.json', '--report',
                'four/research/burn6-campaign-summary.json', '--output-dir',
                'four/build/burn6-campaign', '--namespace', namespace, '--resume']
    if final['command'] != expected or len(steps) != 39:
        raise ValueError('Frozen burn6 replay plan layout changed')
    run_dir = fresh_directory(build / 'burn6-ci-replay')
    baseline = json_paths(build)
    start = time.monotonic()
    rebuild.execute(steps, run_dir / 'prerequisites', args.jobs)
    recheck_pins(pins)
    # This diagnostic path publishes no report or ledger. The exact original
    # audit-only path below rechecks every compilation receipt and frozen input.
    subprocess.run([*expected, '--compile-only', '--timeout', str(args.timeout)],
                   cwd=repo, check=True)
    _, boards, paths, _ = campaign.load_manifest(manifest_path)
    paths[str(output.relative_to(repo / 'four'))] = namespace
    loadpaths = [(repo / 'four' / path, prefix) for path, prefix in paths.items()]
    aggregate = output / 'Campaign.v'
    compiled = kernel.snapshot([aggregate], loadpaths)
    modules = [namespace + '.' + board['id'] for board in boards]
    if len(modules) != 41 or len(set(modules)) != 41:
        raise ValueError('Frozen burn6 inventory wrapper count changed')
    forbidden = set(modules) | {namespace + '.Campaign'}
    caches = validate_current_receipts(kernel, build, baseline, compiled,
                                       forbidden, forbidden, require_complete=False)
    resource.setrlimit(resource.RLIMIT_AS,
                       (args.memory_mib * 1024 * 1024,) * 2)
    os.environ.setdefault('OCAMLRUNPARAM', 'o=5,O=10')
    prerequisite_phases = []
    required = set(compiled['graph']) - forbidden
    covered = covered_modules(kernel, compiled, caches)
    while required - covered:
        batch = next_prerequisite_batch(compiled['graph'], required, covered, 16)
        receipt, log = kernel.fresh_paths(run_dir, 'prerequisite-audit')
        print('Auditing uncovered prerequisites: ' + ', '.join(batch), flush=True)
        phase = kernel.audit(batch, [Path(compiled['graph'][name]['source']) for name in batch],
                             loadpaths, receipt, log,
                             cache=helpers.relevant_caches(compiled, batch, caches),
                             timeout=args.timeout)
        require_fresh_modules(phase, batch)
        caches.append(receipt)
        prerequisite_phases.append({'modules': batch, 'receipt': str(receipt),
                                    'sha256': digest(receipt),
                                    'fresh': phase['checked_modules']})
        covered = covered_modules(kernel, compiled, caches)
    if not required <= covered or forbidden & covered:
        raise ValueError('Prerequisite phases do not cover exactly the allowed dependency scope')
    phases = []
    for board, module in zip(boards, modules):
        receipt, log = kernel.fresh_paths(run_dir, 'inventory-' + board['id'])
        phase = kernel.audit([module], [output / (board['id'] + '.v')], loadpaths,
                             receipt, log,
                             cache=helpers.relevant_caches(compiled, [module], caches),
                             timeout=args.timeout)
        require_fresh_phase(phase, module)
        phases.append({'module': module, 'receipt': str(receipt),
                       'sha256': digest(receipt), 'fresh': phase['checked_modules']})
        caches.append(receipt)
    recheck_pins(pins)
    # Preserve the frozen checker; normalize its local receipt projection
    # through an explicit-loadpath adapter when Coq lives inside the checkout.
    command = [expected[0], 'four/tools/check_campaign_next_audit.py', *expected[2:],
               '--audit-only', '--timeout', str(args.timeout),
               '--memory-mib', str(args.memory_mib)]
    command.extend(arg for path in caches for arg in ('--audit-cache', str(path)))
    subprocess.run(command, cwd=repo, check=True)
    history = json.loads((output / 'latest-audit.json').read_text())
    receipt = repo / 'four' / history['receipt']
    validation = kernel.ReceiptValidation()
    final_audit = validation.load(receipt)
    validation.recheck()
    require_fresh_phase(final_audit, namespace + '.Campaign')
    after = kernel.snapshot([aggregate], loadpaths)
    if after != compiled or not set(after['graph']) <= kernel._covered(after, [final_audit]):
        raise ValueError('The final receipt does not cover the exact unchanged campaign closure')
    recheck_pins(pins)
    result = {'schema': 1, 'result': 'passed', 'frozen_input_pins': pins,
              'prerequisite_phases': prerequisite_phases,
              'fresh_prerequisite_modules': sum(len(p['fresh']) for p in prerequisite_phases),
              'inventory_phases': phases, 'final_receipt': str(receipt),
              'final_receipt_sha256': digest(receipt),
              'closure_modules': len(after['graph']), 'fresh_inventory_modules': 41,
              'fresh_campaign_modules': 1,
              'seconds': round(time.monotonic() - start, 3)}
    (run_dir / 'checked.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({key: value for key, value in result.items()
                      if key not in {'frozen_input_pins', 'prerequisite_phases', 'inventory_phases'}}, indent=2))


if __name__ == '__main__':
    main()
