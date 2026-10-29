"""Bounded sequential kernel replay of the fresh weighted STATE-only queue.

Uses the unchanged historical renderer. Adds an exact board inventory proof,
resource bounds, per-shard receipts and an audit of the complete dependency
closure. A report is emitted only after full recursive coqchk succeeds.
"""
import argparse
import hashlib
import json
import re
import resource
import subprocess
import time
from pathlib import Path

from check_campaign import dependency_hashes, inventory_source
from check_state_pipeline_batch import aggregate
from check_weighted_state import ROOT, load_input, render_shard, sha


def limits():
    resource.setrlimit(resource.RLIMIT_AS, (3 * 1024**3, 3 * 1024**3))


def run(command, path, timeout):
    start = time.monotonic()
    with path.open('w') as log:
        subprocess.run(command, stdout=log, stderr=subprocess.STDOUT,
                       timeout=timeout, check=True, preexec_fn=limits)
    return round(time.monotonic() - start, 3)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path, required=True)
    parser.add_argument('--report', type=Path, required=True)
    parser.add_argument('--inventory', type=Path, required=True)
    parser.add_argument('--output-dir', type=Path, required=True)
    parser.add_argument('--namespace', required=True)
    parser.add_argument('--limit', type=int, default=240)
    parser.add_argument('--shard-size', type=int, default=8)
    parser.add_argument('--timeout', type=int, default=300)
    parser.add_argument('--audit-timeout', type=int, default=1800)
    parser.add_argument('--resume', action='store_true')
    args = parser.parse_args()
    if not re.fullmatch(r'[A-Z][A-Za-z0-9_]*', args.namespace):
        raise ValueError('Invalid namespace')
    rows, inputs = load_input(args.input)
    if len(rows) != 240 or not 1 <= args.limit <= 240 or args.shard_size < 1:
        raise ValueError('Expected the fresh 240-row manifest and a valid subset')
    rows = rows[:args.limit]
    output = args.output_dir.resolve()
    output.mkdir(parents=True, exist_ok=True)
    flags = ['-Q', str(ROOT/'theories'), 'BBB24', '-Q', str(output), args.namespace]
    paths, modules = [], []
    for offset in range(0, len(rows), args.shard_size):
        name = f'WeightedState{len(modules):04}'
        path = output / (name + '.v')
        path.write_text(render_shard(rows[offset:offset+args.shard_size]))
        paths.append(path)
        modules.append(name)
    combined = output / 'WeightedStateAll.v'
    combined.write_text(aggregate(modules, len(rows), 4096, args.namespace))
    paths.append(combined)
    descriptor = {'id': 'next_weighted_state', 'scope': 'state',
                  'rows': len(rows), 'state_bound': 4096, 'instruction_bound': None,
                  'module': args.namespace+'.WeightedStateAll',
                  'board': 'state_board', 'small_sound': 'state_board_small',
                  'sound': 'state_board_bound', 'was_pending': 'state_board_pending',
                  'load_paths': [{'path': str(output.relative_to(ROOT)),
                                  'namespace': args.namespace}],
                  'inventories': [{'path': str(args.inventory.resolve().relative_to(ROOT)),
                                   'format': 'rows'}]}
    exact = output / 'WeightedStateInventory.v'
    exact.write_text(inventory_source({**descriptor, 'machines':
                                      [row['machine'] for row in rows]}))
    paths.append(exact)
    sources = dependency_hashes(paths, flags)
    for name in ('check_next_weighted_state.py', 'check_weighted_state.py',
                 'check_campaign.py', 'generate_pipeline_examples.py',
                 'check_state_pipeline_batch.py', 'weighted_codec_v2.py',
                 'weighted_render.py', 'weighted_render_v3.py', 'weighted_render_v4.py'):
        sources['tools/'+name] = sha(ROOT/'tools'/name)
    version = subprocess.check_output(['coqc', '--version'], text=True)
    timings = {}
    for path in paths:
        current = {'source': sha(path), 'dependencies': dependency_hashes([path], flags),
                   'coq_version': version}
        receipt, vo = path.with_suffix('.checked.json'), path.with_suffix('.vo')
        if args.resume and receipt.exists() and vo.exists():
            previous = json.loads(receipt.read_text())
            if previous == {**current, 'vo_sha256': sha(vo)}:
                print('Reused '+path.stem, flush=True)
                continue
        elapsed = run(['coqc', '-noglob', '-native-compiler', 'no', *flags, str(path)],
                      path.with_suffix('.log'), args.timeout)
        receipt.write_text(json.dumps({**current, 'vo_sha256': sha(vo)}, indent=2)+'\n')
        timings[path.stem] = elapsed
        print(f'Checked {path.stem}: {elapsed:.2f}s', flush=True)
    audit_command = ['coqchk', '-silent', '-bytecode-compiler', 'yes', *flags,
                     args.namespace+'.WeightedStateInventory']
    objects = {str(Path(name).with_suffix('.vo')): sha((ROOT/name).with_suffix('.vo'))
               for name in sources if name.endswith('.v')}
    elapsed = run(audit_command, output/'coqchk.log', args.audit_timeout)
    print(f'Full recursive coqchk: {elapsed:.2f}s', flush=True)
    if (inputs != load_input(args.input)[1]
        or any(sha(ROOT/name) != digest for name, digest in sources.items())
        or any(sha(ROOT/name) != digest for name, digest in objects.items())):
        raise ValueError('Pinned inputs or sources changed during replay')
    inventory = json.dumps({'rows': [{'machine': row['machine']} for row in rows]},
                           indent=2)+'\n'
    report = {'scope': 'State-only bounds and census discharge; no instruction claim.',
              'inputs': inputs, 'source_sha256': sources, 'coq_version': version,
              'candidate_rows': 240, 'selected_rows': len(rows),
              'state_checked_families': len(rows), 'state_census_linked_families': len(rows),
              'exact_inventory_checked_families': len(rows), 'instruction_checked_families': 0,
              'state_bound': 4096, 'inventory_sha256': hashlib.sha256(inventory.encode()).hexdigest(),
              'descriptor': descriptor,
              'exact_inventory_theorem': args.namespace+'.WeightedStateInventory.inventory_exact',
              'audit_root': args.namespace+'.WeightedStateInventory',
              'audit_command': audit_command,
              'object_sha256': objects,
              'audit_exit_code': 0, 'audit_log_sha256': sha(output/'coqchk.log'),
              'validation': 'VM recurrence, pending membership, exact inventory, full recursive coqchk.',
              'resource_limits': {'workers': 1, 'address_space_bytes': 3*1024**3,
                                  'compile_timeout_seconds': args.timeout,
                                  'audit_timeout_seconds': args.audit_timeout},
              'compile_seconds': timings, 'audit_seconds': elapsed,
              'failed_rows': 0, 'timed_out_rows': 0}
    args.inventory.parent.mkdir(parents=True, exist_ok=True)
    args.inventory.write_text(inventory)
    args.report.parent.mkdir(parents=True, exist_ok=True)
    args.report.write_text(json.dumps(report, indent=2, sort_keys=True)+'\n')
    print(f'{len(rows)} weighted STATE-only families kernel-audited and inventory-exact.', flush=True)


if __name__ == '__main__':
    main()
