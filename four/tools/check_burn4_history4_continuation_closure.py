"""Kernel replay and exact census inventory for the bounded history4 closure refinement.

Only the immutable StatePipeline renderer/checker supplies mathematical proof
content. Native search is untrusted. Published evidence is never overwritten;
replays preserve source bytes and accepted inventories and audit current objects.
"""
import argparse
import csv
import math
import hashlib
import json
from pathlib import Path
import resource
import shutil
import subprocess
import time
from types import SimpleNamespace

from check_campaign import dependency_hashes, inventory_source
import check_state_pipeline_batch as engine
import kernel_audit_cache

ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / 'build/burn4-history4-continuation-closure/proof'
PREFIX = ROOT / 'research/burn4-history4-continuation-closure'
NAMESPACE = 'BBB24Burn4History4Closure'
MAX_SHARD_ROWS = 4
TARGET_NATIVE_SECONDS = 1.0


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def path(suffix):
    return PREFIX.with_name(PREFIX.name + '-' + suffix)


def exact(file, text):
    if file.exists() and file.read_text() != text:
        raise ValueError('Frozen proof source or inventory differs: ' + str(file))
    if not file.exists():
        file.write_text(text)


def make_shards(rows, costs):
    """Preserve exact input order, placing expensive rows in their own shard."""
    shards, pending, seconds = [], [], 0.0
    for row in rows:
        cost = costs[row]
        if not math.isfinite(cost) or cost < 0:
            raise ValueError('Invalid observed native cost')
        if pending and (len(pending) >= MAX_SHARD_ROWS or
                        seconds + cost > TARGET_NATIVE_SECONDS):
            shards.append({'rows': pending, 'native_seconds': round(seconds, 6)})
            pending, seconds = [], 0.0
        pending.append(row)
        seconds += cost
    if pending:
        shards.append({'rows': pending, 'native_seconds': round(seconds, 6)})
    return shards


def validate_shard_rows(rows, shards):
    if not shards or any(not shard['rows'] or len(shard['rows']) > MAX_SHARD_ROWS
                         for shard in shards):
        raise ValueError('Invalid proof shard size')
    if [row for shard in shards for row in shard['rows']] != rows:
        raise ValueError('Proof shards omit, repeat, reorder or replace selected families')
    if any(type(row) is not int for shard in shards for row in shard['rows']):
        raise ValueError('Packed families must be integers')


def select_shard_plan(data, groups, destination):
    report = json.loads((ROOT / data['source_report']).read_text())
    ledger = OUTPUT.parent / 'stage-01.tsv'
    if sha(ledger) != report['results'][1]['results_sha256']:
        raise ValueError('Native cost ledger differs from its search report')
    entries = list(csv.reader(ledger.open(), delimiter='\t'))
    if len(entries) != 16 or len({entry[0] for entry in entries}) != 16:
        raise ValueError('Expected the exact 16-row native cost ledger')
    costs = {engine.pack(machine): float(seconds)
             for machine, status, seconds in entries if status == 'candidate'}
    rows = groups[0]['rows']
    if set(costs) != set(rows):
        raise ValueError('Native costs do not match the selected proof inventory')
    shards = make_shards(rows, costs)
    validate_shard_rows(rows, shards)
    plan = {'scope': 'Proof scheduling only; every selected family is independently checked.',
            'source_report_sha256': sha(ROOT / data['source_report']),
            'native_cost_ledger_sha256': sha(ledger),
            'maximum_rows_per_shard': MAX_SHARD_ROWS,
            'target_native_seconds_per_shard': TARGET_NATIVE_SECONDS,
            'slow_rows_get_separate_shards': True,
            'selected_rows': len(rows), 'shards': shards,
            'producer_sha256': sha(Path(__file__))}
    exact(destination, json.dumps(plan, indent=2, sort_keys=True) + '\n')


def validate_shard_plan(data, groups, plan):
    if (plan['source_report_sha256'] != sha(ROOT / data['source_report']) or
        plan['maximum_rows_per_shard'] != MAX_SHARD_ROWS or
        plan['target_native_seconds_per_shard'] != TARGET_NATIVE_SECONDS or
        plan['selected_rows'] != data['selected_rows'] or
        plan['producer_sha256'] != sha(Path(__file__))):
        raise ValueError('Frozen proof scheduling parameters changed')
    validate_shard_rows(groups[0]['rows'], plan['shards'])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--select', action='store_true',
                        help='Create missing compact input from completed search')
    parser.add_argument('--resume', action='store_true')
    parser.add_argument('--timeout', type=int, default=600)
    parser.add_argument('--audit-timeout', type=int, default=2400)
    args = parser.parse_args()
    if args.timeout <= 0 or args.audit_timeout <= 0:
        raise ValueError('Timeouts must be positive')
    resource.setrlimit(resource.RLIMIT_AS, (3221225472, 3221225472))
    OUTPUT.mkdir(parents=True, exist_ok=True)
    input_path = path('proof-input.json')
    shard_plan_path = path('shard-plan.json')
    report_path, inventory_path = path('checked.json'), path('machines.json')
    frozen = {file: sha(file) if file.exists() else None
              for file in (report_path, inventory_path)}
    previous = json.loads(report_path.read_text()) if report_path.exists() else None
    if args.select:
        if input_path.exists() or shard_plan_path.exists() or previous is not None or inventory_path.exists():
            raise ValueError('Selection already exists; replay without --select')
        engine.select(SimpleNamespace(input=input_path,
                      search_report=path('search.json'), search_dir=OUTPUT.parent))
    data, groups = engine.load(SimpleNamespace(input=input_path))
    if data['source_rows'] != 16 or not 0 < data['selected_rows'] <= 16:
        raise ValueError('Unexpected history4 closure refinement cohort')
    if data['state_bound'] != 4096:
        raise ValueError('Unexpected state bound')
    expected_certificate = dict(mode='hist', size=4, history=4, anchor=4096,
                                fuel=131072, extra=128)
    if (data['source_report'] != 'research/burn4-history4-continuation-closure-search.json' or
        len(groups) != 1 or type(groups[0]['stage']) is not int or groups[0]['stage'] != 1 or
        groups[0]['certificate'] != expected_certificate or
        any(type(groups[0]['certificate'][key]) is not int
            for key in ('size', 'history', 'anchor', 'fuel', 'extra'))):
        raise ValueError('Unexpected continuation certificate or source report')
    if args.select:
        select_shard_plan(data, groups, shard_plan_path)
    shard_plan = json.loads(shard_plan_path.read_text())
    validate_shard_plan(data, groups, shard_plan)
    inputs = {str(input_path.relative_to(ROOT)): sha(input_path),
              data['source_report']: sha(ROOT / data['source_report']),
              str(shard_plan_path.relative_to(ROOT)): sha(shard_plan_path)}
    load_paths = [(ROOT / 'theories', 'BBB24'), (OUTPUT, NAMESPACE)]
    flags = [value for directory, namespace in load_paths
             for value in ('-Q', str(directory), namespace)]
    paths, modules, machines = [], [], []
    for shard in shard_plan['shards']:
        packed = shard['rows']
        name = f'History{len(modules):03d}'
        source = OUTPUT / (name + '.v')
        exact(source, engine.shard_text(packed, groups[0]['certificate'], 4096))
        modules.append(name)
        paths.append(source)
        machines.extend(engine.unpack(value) for value in packed)
    source = OUTPUT / 'HistoryAll.v'
    exact(source, engine.aggregate(modules, len(machines), 4096, NAMESPACE))
    paths.append(source)
    descriptor = {'id': 'burn4_history4_continuation_closure', 'scope': 'state', 'rows': len(machines),
        'state_bound': 4096, 'instruction_bound': None,
        'module': NAMESPACE + '.HistoryInventory',
        'board': 'board', 'small_sound': 'small_sound', 'sound': 'sound',
        'was_pending': 'was_pending',
        'proof_source': str((OUTPUT / 'HistoryInventory.v').relative_to(ROOT)),
        'exact_inventory_theorem': NAMESPACE + '.HistoryInventory.inventory_exact',
        'inventories': [{'path': str(inventory_path.relative_to(ROOT)), 'format': 'rows'}],
        'load_paths': [{'path': str(OUTPUT.relative_to(ROOT)), 'namespace': NAMESPACE}]}
    original = {**descriptor, 'module': NAMESPACE + '.HistoryAll', 'board': 'state_board',
                'small_sound': 'state_board_small', 'sound': 'state_board_bound',
                'was_pending': 'state_board_pending', 'machines': machines}
    source = OUTPUT / 'HistoryInventory.v'
    exact(source, inventory_source(original))
    paths.append(source)
    sources = dependency_hashes(paths, flags)
    for filename in ('check_burn4_history4_continuation_closure.py', 'check_state_pipeline_batch.py',
                     'check_campaign.py', 'kernel_audit_cache.py',
                     'generate_pipeline_examples.py', 'check_shadow_links.py'):
        sources['tools/' + filename] = sha(ROOT / 'tools' / filename)
    inventory = json.dumps({'rows': [{'machine': machine} for machine in machines]}, indent=2) + '\n'
    stable = {'inputs_sha256': inputs, 'source_sha256': sources, 'descriptor': descriptor,
              'inventory_sha256': hashlib.sha256(inventory.encode()).hexdigest(),
              'checked_state_families': len(machines), 'checked_instruction_families': 0}
    if previous and any(previous[key] != value for key, value in stable.items()):
        raise ValueError('Frozen history proof evidence differs')
    if previous and sha(inventory_path) != stable['inventory_sha256']:
        raise ValueError('Frozen history inventory differs')
    dependencies = {name: sha((ROOT / name).with_suffix('.vo'))
                    for name in sources if name.startswith('theories/') and name.endswith('.v')}
    compiler = {'version': subprocess.check_output(['coqc', '--version'], text=True),
                'executable_sha256': sha(Path(shutil.which('coqc')).resolve())}
    timings = {}
    for source in paths:
        dependency_sources = dependency_hashes([source], flags)
        imported_objects = {name: sha((ROOT / name).with_suffix('.vo'))
                            for name in dependency_sources
                            if name.endswith('.v') and ROOT / name != source}
        signature = {'source_sha256': sha(source), 'dependencies_vo_sha256': imported_objects,
                     'compiler': compiler,
                     'renderer_sources_sha256': sources}
        checked = source.with_suffix('.checked.json')
        vo = source.with_suffix('.vo')
        reuse = (args.resume and checked.exists() and vo.exists() and
                 json.loads(checked.read_text()) == {**signature, 'object_sha256': sha(vo)})
        start = time.monotonic()
        if not reuse:
            with source.with_suffix('.log').open('w') as log:
                subprocess.run(['coqc', '-noglob', '-native-compiler', 'no', *flags, str(source)],
                               stdout=log, stderr=subprocess.STDOUT,
                               timeout=args.timeout, check=True)
            checked.write_text(json.dumps({**signature, 'object_sha256': sha(vo)},
                                           indent=2, sort_keys=True) + '\n')
        timings[source.stem] = round(time.monotonic() - start, 3)
        print(('Reused ' if reuse else 'Compiled ') + source.stem + ': ' +
              str(timings[source.stem]) + 's', flush=True)
    receipt, log = kernel_audit_cache.fresh_paths(OUTPUT, 'kernel-audit')
    kernel_audit_cache.audit([NAMESPACE + '.HistoryInventory'], [paths[-1]], load_paths,
                             receipt, log, recursive=True, timeout=args.audit_timeout)
    if any(sha(ROOT / name) != digest for name, digest in {**inputs, **sources}.items()):
        raise ValueError('Inputs changed during history proof replay')
    if dependencies != {name: sha((ROOT / name).with_suffix('.vo')) for name in dependencies}:
        raise ValueError('Core proof objects changed during history replay')
    if frozen != {file: sha(file) if file.exists() else None for file in frozen}:
        raise ValueError('Published report or inventory changed during history replay')
    current = {**stable, 'scope': 'Exact state-only census bound; no instruction claim.',
               'compile_seconds': timings, 'kernel_receipt': str(receipt.relative_to(ROOT)),
               'kernel_receipt_sha256': sha(receipt), 'kernel_audit': 'Full recursive coqchk.',
               'object_sha256': {str(source.with_suffix('.vo').relative_to(ROOT)):
                                sha(source.with_suffix('.vo')) for source in paths}}
    if previous is None:
        exact(inventory_path, inventory)
        exact(report_path, json.dumps(current, indent=2, sort_keys=True) + '\n')
    (OUTPUT / 'current-proof-receipt.json').write_text(json.dumps(current, indent=2, sort_keys=True) + '\n')
    print(f'{len(machines)} history families kernel-audited and inventory-exact.', flush=True)


if __name__ == '__main__':
    main()
