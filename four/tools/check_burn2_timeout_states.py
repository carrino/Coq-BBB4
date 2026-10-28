"""Replay the remaining timeout RW cases with pending state obligations.

Select once from the audited supplementary queue, then run bounded, disjoint
slices. A report is published only after a recursive kernel audit. Ordinary
replay uses tracked compact inputs and preserves the frozen report; current
objects and receipts stay under build/. One compilation worker, 3 GiB limit.
"""
import argparse
from collections import Counter
import csv
import hashlib
import json
from pathlib import Path
import resource
import subprocess
import time

import check_closure_wave as closure
import check_next_timeout as timeout_queue
from check_next_rw import compact, load
from check_shadow_links import dependency_hashes
from check_state_repwl_batch import pack
from kernel_audit_cache import audit, fresh_paths

ROOT = Path(__file__).resolve().parents[1]
INPUT = ROOT / 'research/burn2-timeout-state-input.json'
MEMORY = 3 * 1024**3
TOOLS = ['check_burn2_timeout_states.py', 'check_next_timeout.py', 'check_campaign.py',
         'check_next_rw.py', 'check_closure_wave.py',
         'generate_pipeline_examples.py', 'check_shadow_links.py',
         'check_state_repwl_batch.py', 'kernel_audit_cache.py']


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def pins(mapping):
    for name, expected in mapping.items():
        p = ROOT / name
        if Path(name).is_absolute() or '..' in Path(name).parts or sha(p) != expected:
            raise ValueError('Frozen pin differs: ' + name)


def write_once(path, text):
    if path.exists() and path.read_text() != text:
        raise ValueError('Refusing to change existing artifact: ' + str(path))
    if not path.exists():
        path.write_text(text)


EXCLUDED = ('next-timeout-burn2-rw128-v1',
            'next-timeout-burn2-rw256-offset256-v1')


def expected_selection():
    data, original = timeout_queue.load_input()
    excluded = set()
    inputs = [timeout_queue.INPUT, ROOT/'research/next-burndown-summary.json']
    for name in EXCLUDED:
        input_path = ROOT/'research'/(name+'-input.json')
        report_path = ROOT/'research'/(name+'-summary.json')
        successful = load(input_path)
        report = load(report_path)
        if (successful['columns'] != closure.FIELDS or
            successful['selected_rows'] != len(successful['rows']) or
            report['input_sha256'] != sha(input_path) or
            report['checked_families'] != len(successful['rows']) or
            report['queue_input_sha256'] != sha(timeout_queue.INPUT)):
            raise ValueError('Prior timeout inventory/report mismatch')
        for row in successful['rows']:
            machine = row[closure.FIELDS.index('machine')]
            if machine in excluded:
                raise ValueError('Prior accepted batches overlap')
            excluded.add(machine)
        inputs.extend([input_path, report_path])
    if len(excluded) != 384:
        raise ValueError('Expected 384 previous timeout RW discharges')
    state = set(data['state_pending'])
    rows = [{**r, 'state_already_checked': 'no'} for r in original
            if r['mode'] == 'rw' and r['machine'] in state and r['machine'] not in excluded]
    if len(rows) != 207 or len({r['machine'] for r in rows}) != 207:
        raise ValueError('Expected exactly 207 remaining state obligations')
    for row in rows:
        closure.validate_row({k: row[k] for k in closure.FIELDS})
        if row['bound'] != 4096:
            raise ValueError('Unexpected proof bound')
    return dict(selected_rows=207, state_pending_rows=207,
                selection='Timeout RW state obligations, excluding accepted first128 and offsets256-511; inherited machine SHA256 order',
                source_sha256={str(p.relative_to(ROOT)): sha(p) for p in inputs},
                rows=rows)


def select():
    data = expected_selection()
    if INPUT.exists():
        if load(INPUT) != data:
            raise ValueError('Refusing to change frozen priority selection')
    else:
        compact(INPUT, data)
    return data


def read_input():
    data = load(INPUT)
    pins(data['source_sha256'])
    if data != expected_selection():
        raise ValueError('Priority selection differs from exact source-minus-accepted state queue')
    return data


def aggregate_source(rows, modules, namespace):
    source = closure.aggregate_source(modules, namespace, 4096, len(rows))
    packed = '[' + ';'.join(str(pack(r['machine'])) + '%N' for r in rows) + ']'
    return source + ('\nFrom BBB24 Require Import BoardManifest.\nDefinition inventory : list N := '
                     + packed + '.\nLemma inventory_checked : manifest_check inventory board = true.\n'
                     'Proof. vm_compute. reflexivity. Qed.\nTheorem inventory_exact : '
                     'manifest_board inventory = board.\nProof. apply manifest_check_sound. '
                     'exact inventory_checked. Qed.\nPrint Assumptions sound.\nPrint Assumptions inventory_exact.\n')


def limit_child():
    resource.setrlimit(resource.RLIMIT_AS, (MEMORY, MEMORY))


def compile_source(path, flags, timeout):
    start = time.monotonic()
    try:
        with path.with_suffix('.log').open('w') as stream:
            subprocess.run(['coqc', '-w', '-abstract-large-number', '-native-compiler', 'no',
                            *flags, str(path)], stdout=stream, stderr=subprocess.STDOUT,
                           check=True, timeout=timeout, preexec_fn=limit_child)
        status = 'compiled'
    except subprocess.TimeoutExpired:
        status = 'coq_timeout'
    except subprocess.CalledProcessError:
        status = 'coq_failure'
    return dict(status=status, seconds=round(time.monotonic()-start, 3))


def execute(args):
    data = read_input()
    initial_pins = {'tools/'+name: sha(ROOT/'tools'/name) for name in TOOLS}
    roots = [ROOT/'theories'/(name+'.v') for name in
             ('AdvancedPipeline', 'CertifiedBoard', 'CensusUnion', 'Bootstrap', 'Spec', 'BoardManifest')]
    initial_pins.update(dependency_hashes(roots, ['-Q', str(ROOT/'theories'), 'BBB24']))
    report_path = ROOT / ('research/burn2-timeout-state-' + args.batch.lower() + '-report.json')
    frozen = json.loads(report_path.read_text()) if report_path.exists() else None
    report_hash = sha(report_path) if frozen is not None else None
    if (args.replay or args.check_only) and frozen is None:
        raise ValueError('Replay needs an existing audited report')
    if frozen and not (args.replay or args.check_only):
        raise ValueError('Existing report is frozen; use --replay')
    if args.output_dir and not args.replay:
        raise ValueError('Alternate output directories are only for frozen replay')
    namespace = 'BBB24Burn2TimeoutState' + args.batch
    logical_build = 'build/burn2-timeout-state/' + args.batch.lower()
    build = (args.output_dir or ROOT / logical_build).resolve()
    build.relative_to((ROOT / 'build').resolve())
    flags = ['-Q', str(ROOT/'theories'), 'BBB24', '-Q', str(build), namespace]
    input_hash = sha(INPUT)
    selected = data['rows'][args.start:args.start+args.limit]
    if frozen:
        if frozen['input_sha256'] != input_hash:
            raise ValueError('Frozen input differs')
        static = {k:v for k,v in frozen['source_sha256'].items() if not k.startswith('build/')}
        if not {'tools/'+name for name in TOOLS} <= static.keys():
            raise ValueError('Frozen implementation pins are incomplete')
        pins(static)
        args.start, args.limit = frozen['selection_start'], frozen['attempted_rows']
        selected = data['rows'][args.start:args.start+args.limit]
        accepted_ids = [r['machine'] for r in frozen['attempts'] if r['status'] == 'compiled']
        selected = [r for r in selected if r['machine'] in set(accepted_ids)]
        if [r['machine'] for r in selected] != accepted_ids:
            raise ValueError('Frozen accepted inventory differs')
        descriptor = frozen['board_descriptor']
        inventory_name = 'research/burn2-timeout-state-'+args.batch.lower()+'-board-input.json'
        expected_descriptor = dict(id='Burn2TimeoutState'+args.batch, module=namespace+'.All', board='board',
            sound='sound', small_sound='small_sound', was_pending='was_pending', state_bound=4096,
            instruction_bound=4096, scope='both', rows=len(selected),
            inventories=[dict(path=inventory_name, format='columns', order='input')],
            load_paths=[dict(path=logical_build, namespace=namespace)])
        if (descriptor != expected_descriptor or len(selected) != frozen['checked_families']
            or frozen['inventory_theorem'] != namespace+'.All.inventory_exact'
            or frozen['discharge_theorem'] != namespace+'.All.discharged'
            or dict(Counter(r['status'] for r in frozen['attempts'])) != frozen['attempt_counts']
            or any(r['status'] not in {'compiled','coq_failure','coq_timeout'} for r in frozen['attempts'])
            or len(frozen['attempts']) != frozen['attempted_rows']
            or [r['machine'] for r in frozen['attempts']]
               != [r['machine'] for r in data['rows'][args.start:args.start+args.limit]]
            or sum(r['state_already_checked']=='no' for r in selected) != frozen['new_state_families']):
            raise ValueError('Frozen descriptor or attempt ledger differs')
        pins({inventory_name: frozen['board_input_sha256']})
        inventory = load(ROOT/inventory_name)
        if inventory != dict(columns=closure.FIELDS, rows=[[r[k] for k in closure.FIELDS] for r in selected]):
            raise ValueError('Frozen compact inventory differs')
        static[inventory_name] = frozen['board_input_sha256']
        names = ['Row'+hashlib.sha256(r['machine'].encode()).hexdigest()[:16] for r in selected]
        regenerated = {logical_build+'/'+m+'.v': hashlib.sha256(closure.shard_source([r]).encode()).hexdigest()
                       for m,r in zip(names, selected)}
        regenerated[logical_build+'/All.v'] = hashlib.sha256(aggregate_source(selected,names,namespace).encode()).hexdigest()
        if regenerated != frozen['generated_sha256']:
            raise ValueError('Frozen generated-source inventory differs')
        if any(frozen['source_sha256'].get(k) != v for k,v in regenerated.items()):
            raise ValueError('Frozen source/generated pins disagree')
        if args.check_only:
            print(json.dumps(dict(status='preflight passed',accepted_rows=len(selected),new_state=frozen['new_state_families'])))
            return
    if not selected:
        raise ValueError('Empty selected slice')
    build.mkdir(parents=True, exist_ok=True)
    results, accepted, modules, sources = [], [], [], []
    for index, row in enumerate(selected):
        module = 'Row' + hashlib.sha256(row['machine'].encode()).hexdigest()[:16]
        path = build / (module + '.v')
        write_once(path, closure.shard_source([row]))
        result = dict(machine=row['machine'], **compile_source(path, flags, args.timeout))
        results.append(result)
        if result['status'] == 'compiled':
            accepted.append(row); modules.append(module); sources.append(path)
        elif frozen:
            raise ValueError('Frozen proof failed replay: ' + row['machine'])
        (build/'progress.json').write_text(json.dumps(results, indent=2)+'\n')
        print(json.dumps(dict(replayed=index+1, total=len(selected), **result)), flush=True)
    if not accepted:
        raise ValueError('No successful proofs')
    aggregate = build/'All.v'
    write_once(aggregate, aggregate_source(accepted, modules, namespace))
    if compile_source(aggregate, flags, max(300, args.timeout))['status'] != 'compiled':
        raise ValueError('Aggregate failed compilation')
    sources.append(aggregate)
    generated = {logical_build+'/'+p.name: sha(p) for p in sources}
    if frozen and generated != frozen['generated_sha256']:
        raise ValueError('Frozen generated-source hashes differ')
    receipt, log = fresh_paths(build/'audits', 'recursive')
    previous = resource.getrlimit(resource.RLIMIT_AS)
    resource.setrlimit(resource.RLIMIT_AS, (MEMORY, previous[1]))
    try:
        audit([namespace+'.All'], [aggregate], [(ROOT/'theories','BBB24'), (build,namespace)],
              receipt, log, recursive=True, timeout=args.audit_timeout)
    finally:
        resource.setrlimit(resource.RLIMIT_AS, previous)
    pins(data['source_sha256'])
    pins(initial_pins)
    if sha(INPUT) != input_hash:
        raise ValueError('Input changed during proof replay')
    runtime = dict(status='passed', accepted_rows=len(accepted), audit_receipt=str(receipt.relative_to(ROOT)),
                   audit_receipt_sha256=sha(receipt), audit_log_sha256=sha(log), attempts=results,
                   executed_runner_sha256=initial_pins['tools/check_burn2_timeout_states.py'],
                   input_sha256=input_hash, frozen_report_sha256=report_hash)
    if frozen:
        pins(static)
        if sha(report_path) != report_hash:
            raise ValueError('Published report changed during replay')
        runtime['published_evidence_unchanged'] = True
        runtime_path = receipt.with_name(receipt.stem+'-runtime.json')
        runtime_path.write_text(json.dumps(runtime, indent=2)+'\n')
        print(json.dumps(runtime | {'attempts': len(results)}), flush=True)
        return
    inventory_path = ROOT/('research/burn2-timeout-state-'+args.batch.lower()+'-board-input.json')
    if inventory_path.exists():
        raise ValueError('Inventory already exists without report')
    compact(inventory_path, dict(columns=closure.FIELDS, rows=[[r[k] for k in closure.FIELDS] for r in accepted]))
    descriptor = dict(id='Burn2TimeoutState'+args.batch, module=namespace+'.All', board='board', sound='sound',
                      small_sound='small_sound', was_pending='was_pending', state_bound=4096,
                      instruction_bound=4096, scope='both', rows=len(accepted),
                      inventories=[dict(path=str(inventory_path.relative_to(ROOT)), format='columns', order='input')],
                      load_paths=[dict(path=logical_build, namespace=namespace)])
    source_hashes = dependency_hashes([aggregate], flags)
    source_hashes.update({'tools/'+name: sha(ROOT/'tools'/name) for name in TOOLS})
    report = dict(status='Recursive kernel audit passed; exact inventory and pending membership checked',
                  scope='Both bounds for every completion; original census leaf weights unchanged',
                  method='direct rw_check', checked_families=len(accepted),
                  new_state_families=sum(r['state_already_checked']=='no' for r in accepted),
                  selection_start=args.start, attempted_rows=len(selected), attempts=results,
                  attempt_counts=dict(Counter(r['status'] for r in results)),
                  input_sha256=input_hash, board_input_sha256=sha(inventory_path),
                  board_descriptor=descriptor, inventory_theorem=namespace+'.All.inventory_exact',
                  discharge_theorem=namespace+'.All.discharged', generated_sha256=generated,
                  source_sha256=source_hashes, object_sha256={str(p.with_suffix('.vo').relative_to(ROOT)):sha(p.with_suffix('.vo')) for p in sources},
                  audit_receipt=runtime['audit_receipt'], audit_receipt_sha256=sha(receipt), audit_log_sha256=sha(log),
                  budgets=dict(coq_seconds_per_row=args.timeout,audit_seconds=args.audit_timeout,memory_limit_bytes=MEMORY,workers=1))
    write_once(report_path, json.dumps(report, indent=2, sort_keys=True)+'\n')
    print(json.dumps(dict(audited=len(accepted),new_state=report['new_state_families'],descriptor=descriptor)), flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--select', action='store_true')
    parser.add_argument('--batch', default='Priority207')
    parser.add_argument('--start', type=int, default=0)
    parser.add_argument('--limit', type=int, default=207)
    parser.add_argument('--timeout', type=int, default=120)
    parser.add_argument('--audit-timeout', type=int, default=2400)
    parser.add_argument('--replay', action='store_true')
    parser.add_argument('--check-only', action='store_true')
    parser.add_argument('--output-dir', type=Path)
    args = parser.parse_args()
    if not args.batch.isascii() or not args.batch.isidentifier() or args.start < 0 or args.limit <= 0:
        raise ValueError('Invalid batch or slice')
    if args.select:
        data = select()
        print(json.dumps({k:v for k,v in data.items() if k != 'rows'}))
    else:
        execute(args)


if __name__ == '__main__':
    main()
