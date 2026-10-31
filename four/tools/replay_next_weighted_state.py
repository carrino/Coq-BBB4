"""Replay a frozen weighted-state board without rewriting published evidence.

The compact manifest and accepted IDs reproduce the exact frozen Coq sources.
Fresh compilation and recursive coqchk produce runtime evidence only in build/.
Historical object bytes, compiler versions and timings are not portability
requirements; mathematical statements, source bytes and inventories are.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
INPUT = 'research/next-weighted-state-input.json'
BUNDLE = 'research/next-weighted-state-certificates.json'
INVARIANTS = (
    'scope', 'inputs', 'source_sha256', 'candidate_rows', 'selected_rows',
    'state_checked_families', 'state_census_linked_families',
    'exact_inventory_checked_families', 'instruction_checked_families',
    'state_bound', 'inventory_sha256', 'exact_inventory_theorem', 'audit_root',
    'validation', 'failed_rows', 'timed_out_rows',
)
FROZEN_TOOLS = {
    'tools/' + name for name in (
        'check_next_weighted_state.py', 'check_weighted_state.py',
        'check_campaign.py', 'generate_pipeline_examples.py',
        'check_state_pipeline_batch.py', 'weighted_codec_v2.py',
        'weighted_render.py', 'weighted_render_v3.py', 'weighted_render_v4.py')
}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def text_digest(text):
    return hashlib.sha256(text.encode()).hexdigest()


def repo_path(name):
    path = (ROOT / name).resolve()
    path.relative_to(ROOT.parent)
    return path


def checked_pins(pins):
    for name, expected in pins.items():
        path = repo_path(name)
        if not path.is_file() or digest(path) != expected:
            raise ValueError('Frozen input/source pin differs: ' + name)


def prepare(reference_path):
    """Validate immutable evidence and render expected bytes without writing."""
    reference_path = reference_path.resolve()
    frozen = json.loads(reference_path.read_text())
    count = frozen['selected_rows']
    if type(count) is not int or count not in (8, 240):
        raise ValueError('Only the frozen pilot8 and full240 boards are supported')
    pilot = count == 8
    namespace = 'BBB24NextWeightedState' + ('Pilot' if pilot else '')
    output_name = 'build/next-weighted-state/' + ('pilot' if pilot else 'full')
    inventory_name = 'research/next-weighted-state-' + ('pilot-' if pilot else '') + 'machines.json'
    descriptor = {
        'id': 'next_weighted_state', 'scope': 'state', 'rows': count,
        'state_bound': 4096, 'instruction_bound': None,
        'module': namespace + '.WeightedStateAll', 'board': 'state_board',
        'small_sound': 'state_board_small', 'sound': 'state_board_bound',
        'was_pending': 'state_board_pending',
        'load_paths': [{'path': output_name, 'namespace': namespace}],
        'inventories': [{'path': inventory_name, 'format': 'rows'}],
    }
    if frozen['descriptor'] != descriptor:
        raise ValueError('Unsupported frozen descriptor or output load paths')
    if (frozen['audit_root'] != namespace + '.WeightedStateInventory'
        or frozen['exact_inventory_theorem'] != namespace + '.WeightedStateInventory.inventory_exact'):
        raise ValueError('Frozen inventory theorem or recursive audit root differs')
    if (frozen['candidate_rows'] != 240 or frozen['state_bound'] != 4096
        or frozen['instruction_checked_families'] != 0
        or frozen['failed_rows'] != 0 or frozen['timed_out_rows'] != 0
        or frozen['audit_exit_code'] != 0
        or any(frozen[key] != count for key in (
            'state_checked_families', 'state_census_linked_families',
            'exact_inventory_checked_families'))):
        raise ValueError('Frozen mathematical scope or accepted count differs')
    if set(frozen['inputs']) != {INPUT, BUNDLE}:
        raise ValueError('Expected the frozen compact 240-row input and bundle')
    checked_pins(frozen['inputs'])
    output = ROOT / output_name
    names = [f'WeightedState{i:04}' for i in range((count + 7) // 8)]
    generated_names = {output_name + '/' + name + '.v'
                       for name in [*names, 'WeightedStateAll', 'WeightedStateInventory']}
    generated_pins = {name: value for name, value in frozen['source_sha256'].items()
                      if name.startswith(output_name + '/')}
    if set(generated_pins) != generated_names:
        raise ValueError('Frozen generated-source inventory differs')
    static_pins = {name: value for name, value in frozen['source_sha256'].items()
                   if name not in generated_names}
    if not FROZEN_TOOLS <= static_pins.keys():
        raise ValueError('Frozen source pins omit a replay implementation dependency')
    checked_pins(static_pins)
    # Import the frozen implementation only after its source pins have passed.
    from check_campaign import inventory_source
    from check_state_pipeline_batch import aggregate
    from check_weighted_state import load_input, render_shard

    rows, inputs = load_input(ROOT / INPUT)
    if len(rows) != 240 or inputs != frozen['inputs']:
        raise ValueError('Compact manifest inventory differs from frozen evidence')
    rows = rows[:count]
    inventory = json.dumps({'rows': [{'machine': row['machine']} for row in rows]},
                           indent=2) + '\n'
    inventory_path = ROOT / inventory_name
    if (text_digest(inventory) != frozen['inventory_sha256']
        or inventory_path.read_text() != inventory):
        raise ValueError('Frozen accepted IDs differ from selected compact certificates')
    generated = {output_name + '/' + name + '.v': render_shard(rows[i*8:(i+1)*8])
                 for i, name in enumerate(names)}
    generated[output_name + '/WeightedStateAll.v'] = aggregate(names, count, 4096, namespace)
    generated[output_name + '/WeightedStateInventory.v'] = inventory_source({
        **descriptor, 'machines': [row['machine'] for row in rows]})
    for name, source in generated.items():
        if text_digest(source) != generated_pins[name]:
            raise ValueError('Regenerated frozen source pin differs: ' + name)
        path = ROOT / name
        if path.exists() and digest(path) != generated_pins[name]:
            raise ValueError('Existing generated source differs: ' + name)
    protected = {**frozen['inputs'], **static_pins, inventory_name: frozen['inventory_sha256']}
    return {'frozen': frozen, 'reference': reference_path,
            'reference_sha256': digest(reference_path), 'output': output,
            'namespace': namespace, 'protected': protected, 'inventory': inventory}


def compare_runtime(plan, runtime, local_inventory):
    frozen = plan['frozen']
    for field in INVARIANTS:
        if runtime[field] != frozen[field]:
            raise ValueError('Fresh replay changed invariant field: ' + field)
    expected_descriptor = {**frozen['descriptor'], 'inventories': [{
        'path': str(local_inventory.relative_to(ROOT)), 'format': 'rows'}]}
    if runtime['descriptor'] != expected_descriptor:
        raise ValueError('Fresh replay changed the frozen descriptor')
    if (local_inventory.read_text() != plan['inventory']
        or digest(local_inventory) != frozen['inventory_sha256']):
        raise ValueError('Fresh replay changed the exact accepted inventory')
    objects = runtime['object_sha256']
    expected_objects = {str(Path(name).with_suffix('.vo'))
                        for name in frozen['source_sha256'] if name.endswith('.v')}
    if set(objects) != expected_objects:
        raise ValueError('Fresh object receipt omits a local proof dependency')
    checked_pins(objects)
    audit_command = ['coqchk', '-silent', '-bytecode-compiler', 'yes',
                     '-Q', str(ROOT/'theories'), 'BBB24',
                     '-Q', str(plan['output']), plan['namespace'], frozen['audit_root']]
    if (runtime['audit_exit_code'] != 0 or runtime['audit_command'] != audit_command
        or runtime['audit_log_sha256'] != digest(plan['output']/'coqchk.log')):
        raise ValueError('Fresh recursive audit evidence is incomplete')
    if (runtime['resource_limits']['workers'] != 1
        or runtime['resource_limits']['address_space_bytes'] != 3*1024**3):
        raise ValueError('Fresh replay resource bounds differ')
    # Deliberately never compare runtime objects/compiler/timings to historical values.
    checked_pins(frozen['source_sha256'])
    checked_pins(plan['protected'])
    if digest(plan['reference']) != plan['reference_sha256']:
        raise ValueError('Published report changed during portable replay')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--report', type=Path,
                        default=ROOT/'research/next-weighted-state-checked.json')
    parser.add_argument('--timeout', type=int)
    parser.add_argument('--audit-timeout', type=int)
    parser.add_argument('--resume', action='store_true')
    parser.add_argument('--check-only', action='store_true',
                        help='Validate frozen inputs and regenerated source bytes without auditing')
    args = parser.parse_args()
    plan = prepare(args.report)
    frozen, output = plan['frozen'], plan['output']
    count = frozen['selected_rows']
    if args.check_only:
        print(f'Validated frozen inputs, exact {count}-ID inventory and generated sources; no audit run.')
        return
    timeout = (args.timeout if args.timeout is not None
               else frozen['resource_limits']['compile_timeout_seconds'])
    audit_timeout = (args.audit_timeout if args.audit_timeout is not None
                     else frozen['resource_limits']['audit_timeout_seconds'])
    if timeout <= 0 or audit_timeout <= 0:
        raise ValueError('Replay timeouts must be positive')
    output.mkdir(parents=True, exist_ok=True)
    runtime_path = output/'portable-runtime.json'
    local_inventory = output/'portable-machines.json'
    receipt_path = output/'portable-replay.json'
    receipt_path.unlink(missing_ok=True)
    command = [sys.executable, str(ROOT/'tools/check_next_weighted_state.py'),
               '--input', str(ROOT/INPUT), '--report', str(runtime_path),
               '--inventory', str(local_inventory), '--output-dir', str(output),
               '--namespace', plan['namespace'], '--limit', str(count), '--shard-size', '8',
               '--timeout', str(timeout), '--audit-timeout', str(audit_timeout)]
    if args.resume:
        command.append('--resume')
    subprocess.run(command, check=True, cwd=ROOT.parent)
    runtime = json.loads(runtime_path.read_text())
    compare_runtime(plan, runtime, local_inventory)
    receipt = {
        'frozen_report': str(plan['reference'].relative_to(ROOT)),
        'frozen_report_sha256': plan['reference_sha256'],
        'runtime_report': str(runtime_path.relative_to(ROOT)),
        'runtime_report_sha256': digest(runtime_path),
        'adapter_sha256': digest(Path(__file__)), 'replay_command': command,
        'state_checked_families': count, 'instruction_checked_families': 0,
        'mathematical_source_input_inventory_fields_match': True,
        'published_evidence_unchanged': True, 'fresh_recursive_audit_exit_code': 0,
        'historical_object_bytes_compared': False,
    }
    receipt_path.write_text(json.dumps(receipt, indent=2, sort_keys=True)+'\n')
    print(f'{count} STATE-only families freshly audited; published evidence unchanged.')
    print('Current-runtime receipt: ' + str(receipt_path))


if __name__ == '__main__':
    main()
