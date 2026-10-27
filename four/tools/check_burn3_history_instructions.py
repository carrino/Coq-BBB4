"""Kernel replay of instruction upgrades from the third-round state-history sweep.

Only the immutable AdvancedPipeline renderer/checker supplies mathematical proof
content. Both state and instruction bounds are checked. Native search is untrusted.
Published evidence is never overwritten; replays preserve source bytes and accepted
inventories and audit current objects.
"""
import argparse
import hashlib
import json
from pathlib import Path
import resource
import shutil
import subprocess
import time

from check_campaign import dependency_hashes, inventory_source
import check_closure_wave as engine
import kernel_audit_cache

ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / 'build/burn3-history-instruction/proof'
PREFIX = ROOT / 'research/burn3-history-instruction'
NAMESPACE = 'BBB24Burn3HistoryInstruction'
SHARD_SIZE = 4


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def path(suffix):
    return PREFIX.with_name(PREFIX.name + '-' + suffix)


def exact(file, text):
    if file.exists() and file.read_text() != text:
        raise ValueError('Frozen proof source or inventory differs: ' + str(file))
    if not file.exists():
        file.write_text(text)


def select_input(input_path):
    search_path = path('search.json')
    search = json.loads(search_path.read_text())
    rows = sorted(search['candidates'], key=engine.machine_hash)
    if not rows or search['candidate_rows'] != len(rows):
        raise ValueError('Empty or inconsistent instruction candidate inventory')
    for row in rows:
        engine.validate_row(row)
    value = {'selection': 'All native instruction upgrades of the frozen state-history candidates.',
             'source_report': str(search_path.relative_to(ROOT)),
             'search_sources': [], 'excluded_ledgers_sha256': {},
             'columns': engine.FIELDS, 'selected_rows': len(rows),
             'rows': [[row[field] for field in engine.FIELDS] for row in rows]}
    exact(input_path, json.dumps(value, indent=2, sort_keys=True) + '\n')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--select', action='store_true',
                        help='Create missing compact input from completed search')
    parser.add_argument('--resume', action='store_true')
    parser.add_argument('--timeout', type=int, default=300)
    parser.add_argument('--audit-timeout', type=int, default=2400)
    args = parser.parse_args()
    if args.timeout <= 0 or args.audit_timeout <= 0:
        raise ValueError('Timeouts must be positive')
    resource.setrlimit(resource.RLIMIT_AS, (3221225472, 3221225472))
    OUTPUT.mkdir(parents=True, exist_ok=True)
    input_path = path('proof-input.json')
    report_path, inventory_path = path('checked.json'), path('machines.json')
    frozen = {file: sha(file) if file.exists() else None
              for file in (report_path, inventory_path)}
    previous = json.loads(report_path.read_text()) if report_path.exists() else None
    if args.select:
        if input_path.exists() or previous is not None or inventory_path.exists():
            raise ValueError('Selection already exists; replay without --select')
        select_input(input_path)
    data, rows = engine.load_input(input_path)
    search = json.loads((ROOT / data['source_report']).read_text())
    if (not 0 < len(rows) <= 378 or search['selected_rows'] != 378 or
        rows != sorted(search['candidates'], key=engine.machine_hash) or
        any(row['mode'] != 'hist' or row['bound'] != 4096 for row in rows)):
        raise ValueError('Unexpected instruction-upgrade selection or bound')
    inputs = {str(input_path.relative_to(ROOT)): sha(input_path),
              data['source_report']: sha(ROOT / data['source_report'])}
    load_paths = [(ROOT / 'theories', 'BBB24'), (OUTPUT, NAMESPACE)]
    flags = [value for directory, namespace in load_paths
             for value in ('-Q', str(directory), namespace)]
    paths, modules, machines = [], [], []
    for start in range(0, len(rows), SHARD_SIZE):
        shard = rows[start:start + SHARD_SIZE]
        name = f'History{len(modules):03d}'
        source = OUTPUT / (name + '.v')
        exact(source, engine.shard_source(shard))
        modules.append(name)
        paths.append(source)
        machines.extend(row['machine'] for row in shard)
    source = OUTPUT / 'HistoryAll.v'
    exact(source, engine.aggregate_source(modules, NAMESPACE, 4096, len(machines)))
    paths.append(source)
    descriptor = {'id': 'burn3_history_instruction', 'scope': 'both', 'rows': len(machines),
        'state_bound': 4096, 'instruction_bound': 4096,
        'module': NAMESPACE + '.HistoryInventory',
        'board': 'board', 'small_sound': 'small_sound', 'sound': 'sound',
        'was_pending': 'was_pending',
        'proof_source': str((OUTPUT / 'HistoryInventory.v').relative_to(ROOT)),
        'exact_inventory_theorem': NAMESPACE + '.HistoryInventory.inventory_exact',
        'inventories': [{'path': str(inventory_path.relative_to(ROOT)), 'format': 'rows'}],
        'load_paths': [{'path': str(OUTPUT.relative_to(ROOT)), 'namespace': NAMESPACE}]}
    original = {**descriptor, 'module': NAMESPACE + '.HistoryAll', 'machines': machines}
    source = OUTPUT / 'HistoryInventory.v'
    exact(source, inventory_source(original))
    paths.append(source)
    sources = dependency_hashes(paths, flags)
    for filename in ('check_burn3_history_instructions.py', 'check_closure_wave.py',
                     'check_campaign.py', 'kernel_audit_cache.py',
                     'generate_pipeline_examples.py', 'check_shadow_links.py'):
        sources['tools/' + filename] = sha(ROOT / 'tools' / filename)
    inventory = json.dumps({'rows': [{'machine': machine} for machine in machines]}, indent=2) + '\n'
    stable = {'inputs_sha256': inputs, 'source_sha256': sources, 'descriptor': descriptor,
              'inventory_sha256': hashlib.sha256(inventory.encode()).hexdigest(),
              'checked_state_families': len(machines), 'checked_instruction_families': len(machines)}
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
                subprocess.run(['coqc', '-w', '-abstract-large-number', '-native-compiler', 'no', *flags, str(source)],
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
    current = {**stable, 'scope': 'Exact state and instruction census bounds; all completions covered.',
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
