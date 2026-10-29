"""Kernel replay and exact census inventory for the fourth-round refinement pilot.

Only the immutable StatePipeline renderer/checker supplies mathematical proof
content. Native search is untrusted. Published evidence is never overwritten;
replays preserve source bytes and accepted inventories and audit current objects.
"""
import argparse
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
OUTPUT = ROOT / 'build/burn4-history-refinement-pilot/proof'
PREFIX = ROOT / 'research/burn4-history-refinement-pilot'
NAMESPACE = 'BBB24Burn4HistoryRefinement'
SHARD_SIZE = 1


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def path(suffix):
    return PREFIX.with_name(PREFIX.name + '-' + suffix)


def exact(file, text):
    if file.exists() and file.read_text() != text:
        raise ValueError('Frozen proof source or inventory differs: ' + str(file))
    if not file.exists():
        file.write_text(text)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--select', action='store_true',
                        help='Create missing compact input from completed search')
    parser.add_argument('--resume', action='store_true')
    parser.add_argument('--timeout', type=int, default=120)
    parser.add_argument('--audit-timeout', type=int, default=600)
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
        engine.select(SimpleNamespace(input=input_path,
                      search_report=path('search.json'), search_dir=OUTPUT.parent))
    data, groups = engine.load(SimpleNamespace(input=input_path))
    if data['source_rows'] != 16 or data['selected_rows'] != 1:
        raise ValueError('Unexpected fourth-round refinement cohort')
    if data['state_bound'] != 4096:
        raise ValueError('Unexpected state bound')
    if data['source_report'] != 'research/burn4-history-refinement-pilot-search.json':
        raise ValueError('Unexpected refinement search report')
    if [engine.unpack(value) for group in groups for value in group['rows']] != [
            '1LB2RB3RB2RA_3RB3LA0LB1LB']:
        raise ValueError('Unexpected refinement family')
    for group in groups:
        cert = group['certificate']
        if (set(cert) != {'mode', 'size', 'anchor', 'fuel', 'extra', 'history'} or
            cert['mode'] != 'hist' or any(type(cert[key]) is not int
                for key in ('size', 'anchor', 'fuel', 'extra', 'history'))):
            raise ValueError('Malformed history parameters')
    inputs = {str(input_path.relative_to(ROOT)): sha(input_path),
              data['source_report']: sha(ROOT / data['source_report'])}
    load_paths = [(ROOT / 'theories', 'BBB24'), (OUTPUT, NAMESPACE)]
    flags = [value for directory, namespace in load_paths
             for value in ('-Q', str(directory), namespace)]
    paths, modules, machines = [], [], []
    for group in groups:
        rows = group['rows']
        for start in range(0, len(rows), SHARD_SIZE):
            packed = rows[start:start + SHARD_SIZE]
            name = f'History{len(modules):03d}'
            source = OUTPUT / (name + '.v')
            exact(source, engine.shard_text(packed, group['certificate'], 4096))
            modules.append(name)
            paths.append(source)
            machines.extend(engine.unpack(value) for value in packed)
    source = OUTPUT / 'HistoryAll.v'
    exact(source, engine.aggregate(modules, len(machines), 4096, NAMESPACE))
    paths.append(source)
    descriptor = {'id': 'burn4_history_refinement', 'scope': 'state', 'rows': len(machines),
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
    for filename in ('check_burn4_history_refinement.py', 'check_state_pipeline_batch.py',
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
