"""Bounded, serial replay of the frozen timeout recovery queue.

All original campaign files are read-only. `prepare` records the exact remaining
queue. `run` compiles selected rows separately, retains failures, then recursively
audits an aggregate and its exact inventory before publishing any proof count.
Receipts are local caches only; every published batch receives fresh coqchk.
"""
import argparse
import base64
from collections import Counter
import csv
import hashlib
import json
import os
from pathlib import Path
import resource
import subprocess
import time
import zlib

import check_closure_wave as closure
from check_campaign import packed, read_inventory
from check_shadow_links import dependency_hashes

ROOT = Path(__file__).resolve().parents[1]
INPUT = ROOT/'research/next-timeout-input-v1.json'
BUILD = ROOT/'build/next-timeout'
SOURCE = ROOT/'research/wave3-timeout-proof-input.json'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write_json(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix+'.tmp')
    temporary.write_text(json.dumps(value, indent=2, sort_keys=True)+'\n')
    temporary.replace(path)


def prepare():
    _, rows = closure.load_input(SOURCE)
    queue = ROOT/'build/campaign-next/queued.tsv'
    next_report = ROOT/'research/campaign-next-summary.json'
    report = json.loads(next_report.read_text())
    if sha(queue) != report['outputs']['queued.tsv']['sha256']:
        raise ValueError('Frozen next-work queue changed')
    with queue.open() as stream:
        queued = {r['machine']: r for r in csv.DictReader(stream, delimiter='\t')
                  if 'timeout.recovery' in r['both_sources'].split(',')}
    rows = [r for r in rows if r['machine'] in queued]
    if len(rows) != 1519 or len(queued) != 1519:
        raise ValueError('Expected exactly 1,519 timeout instruction obligations')
    state_pending = sorted(r['machine'] for r in rows
                           if queued[r['machine']]['state_already_checked'] == 'no')
    if len(state_pending) != 296:
        raise ValueError('Expected exactly 296 timeout state obligations')
    sources = [SOURCE, next_report, ROOT/'research/campaign-final-input.json',
               ROOT/'research/campaign-final-summary.json']
    data = {'version': 1, 'scope': 'Both state and instruction bounds, all completions',
            'source_sha256': {str(p.relative_to(ROOT)): sha(p) for p in sources},
            'queue_sha256': sha(queue), 'columns': closure.FIELDS,
            'rows': [[r[k] for k in closure.FIELDS] for r in rows],
            'state_pending': state_pending, 'selected_rows': len(rows),
            'mode_counts': dict(Counter(r['mode'] for r in rows)),
            'ordering': 'Ascending SHA256(machine UTF-8), inherited from source'}
    raw = json.dumps(data, separators=(',', ':'), sort_keys=True).encode()
    value = {'encoding': 'zlib-base64', 'uncompressed_sha256': hashlib.sha256(raw).hexdigest(),
             'data': base64.b64encode(zlib.compress(raw, 9)).decode()}
    if INPUT.exists() and json.loads(INPUT.read_text()) != value:
        raise ValueError('Refusing to replace a different frozen queue')
    write_json(INPUT, value)
    print(json.dumps({'rows': len(rows), 'modes': data['mode_counts'],
                      'state_pending': len(state_pending)}), flush=True)


def load_input():
    outer = json.loads(INPUT.read_text())
    raw = zlib.decompress(base64.b64decode(outer['data'], validate=True))
    if hashlib.sha256(raw).hexdigest() != outer['uncompressed_sha256']:
        raise ValueError('Corrupt frozen input')
    data = json.loads(raw)
    for name, expected in data['source_sha256'].items():
        if sha(ROOT/name) != expected:
            raise ValueError('Source changed: '+name)
    if data['columns'] != closure.FIELDS:
        raise ValueError('Invalid columns')
    rows = [dict(zip(closure.FIELDS, row)) for row in data['rows']]
    if len(rows) != 1519 or len({r['machine'] for r in rows}) != len(rows):
        raise ValueError('Incomplete/duplicate queue')
    for row in rows:
        closure.validate_row(row)
    if rows != sorted(rows, key=closure.machine_hash):
        raise ValueError('Changed queue ordering')
    # Compare against the original certified inventories, not search statuses.
    manifest = json.loads((ROOT/'research/campaign-final-input.json').read_text())
    final = json.loads((ROOT/'research/campaign-final-summary.json').read_text())
    for name, expected in final['inputs'].items():
        if sha(ROOT/name) != expected:
            raise ValueError('Audited final inventory input changed: '+name)
    both, state = set(), set()
    for board in manifest['boards']:
        ids = {machine for spec in board['inventories'] for machine in read_inventory(spec)}
        state.update(ids)
        if board['scope'] == 'both':
            both.update(ids)
    ids = {r['machine'] for r in rows}
    if ids & both or ids-state != set(data['state_pending']):
        raise ValueError('Frozen queue disagrees with final audited inventories')
    _, original_rows = closure.load_input(SOURCE)
    if rows != [r for r in original_rows if r['machine'] not in both]:
        raise ValueError('Queue is not the exact source-minus-final-both inventory')
    if not ids <= set(read_inventory(manifest['cohort'])):
        raise ValueError('Queue contains a machine outside the original comparison cohort')
    return data, rows


def execute(command, log, timeout, memory_mib):
    """Address-space cap is stricter than an RSS cap; poll one serial child."""
    start = time.monotonic()
    def limits():
        cap = memory_mib*1024*1024
        resource.setrlimit(resource.RLIMIT_AS, (cap, cap))
    env = dict(os.environ)
    env.setdefault('OCAMLRUNPARAM', 's=4M,o=30,O=50')
    with log.open('w') as stream:
        try:
            result = subprocess.run(command, cwd=ROOT.parent, env=env,
                                    stdout=stream, stderr=subprocess.STDOUT,
                                    timeout=timeout, preexec_fn=limits)
            status = 'compiled' if result.returncode == 0 else 'failed'
            code = result.returncode
        except subprocess.TimeoutExpired:
            status, code = 'timeout', None
    return {'status': status, 'returncode': code,
            'seconds': round(time.monotonic()-start, 3), 'log_sha256': sha(log)}


def compile_row(path, flags, evidence, args):
    receipt = path.with_suffix('.receipt.json')
    vo = path.with_suffix('.vo')
    # A compiled object depends on the generated source and Coq dependencies;
    # Python driver changes are separately pinned by the final audit report.
    expected = {'sources_sha256': {k: v for k, v in evidence['sources_sha256'].items()
                                   if k.endswith('.v')},
                'coq_version': evidence['coq_version'], 'source_sha256': sha(path)}
    if args.resume and receipt.exists() and vo.exists():
        old = json.loads(receipt.read_text())
        old_evidence = {k: v for k, v in old['evidence'].items() if k != 'input_sha256'}
        old_evidence['sources_sha256'] = {k: v for k, v in old_evidence['sources_sha256'].items()
                                          if k.endswith('.v')}
        if old_evidence == expected and old['vo_sha256'] == sha(vo):
            return {**old['result'], 'reused': True}
    result = execute(['coqc', '-w', '-abstract-large-number', '-native-compiler', 'no',
                      *flags, str(path)], path.with_suffix('.log'), args.timeout, args.memory_mib)
    if result['status'] == 'compiled':
        write_json(receipt, {'evidence': expected, 'vo_sha256': sha(vo), 'result': result})
    else:
        vo.unlink(missing_ok=True)
        receipt.unlink(missing_ok=True)
    return result


def run(args):
    data, all_rows = load_input()
    rows = [r for r in all_rows if r['mode'] in args.modes.split(',')]
    rows = rows[args.offset:args.offset+args.limit] if args.limit else rows[args.offset:]
    if not rows or not args.batch.replace('-', '').isalnum():
        raise ValueError('Empty selection or invalid batch name')
    directory = BUILD/args.batch
    directory.mkdir(parents=True, exist_ok=True)
    namespace = 'BBB24NextTimeout'+''.join(x.title() for x in args.batch.split('-'))
    flags = ['-Q', str(ROOT/'theories'), 'BBB24', '-Q', str(directory), namespace]
    roots = [ROOT/'theories'/f'{name}.v' for name in
             ('AdvancedPipeline', 'CertifiedBoard', 'CensusUnion', 'Bootstrap', 'Spec', 'BoardManifest')]
    sources = dependency_hashes(roots, flags)
    sources.update({str(p.relative_to(ROOT)): sha(p) for p in
                    (Path(__file__), Path(closure.__file__), ROOT/'tools/check_shadow_links.py',
                     ROOT/'tools/check_campaign.py', ROOT/'tools/generate_pipeline_examples.py')})
    evidence = {'sources_sha256': sources, 'coq_version': subprocess.check_output(
        ['coqc', '--version'], text=True), 'input_sha256': sha(INPUT)}
    prefix = ROOT/'research'/('next-timeout-'+args.batch)
    report_path = Path(str(prefix)+'-summary.json')
    previous = json.loads(report_path.read_text()) if report_path.exists() else None
    if previous and (previous['source_sha256'] != sources or
                     previous['queue_input_sha256'] != sha(INPUT)):
        raise ValueError('Frozen batch input/source changed; select a new versioned batch')
    results, accepted, modules, paths = [], [], [], []
    for i, row in enumerate(rows):
        name = 'Row'+hashlib.sha256(row['machine'].encode()).hexdigest()[:16]
        path = directory/(name+'.v')
        path.write_text(closure.shard_source([row]))
        result = {**row, **compile_row(path, flags, evidence, args)}
        results.append(result)
        if result['status'] == 'compiled':
            accepted.append(row); modules.append(name); paths.append(path)
        write_json(directory/'progress.json', {'attempted': len(results), 'selected': len(rows),
                                              'compiled': len(accepted), 'results': results})
        print(json.dumps({'row': i+1, 'selected': len(rows), 'mode': row['mode'],
                          'status': result['status'], 'seconds': result['seconds']}), flush=True)
    if not accepted:
        raise ValueError('No accepted rows; progress preserves all failures')
    aggregate = directory/'All.v'
    inventory = '['+';'.join(str(packed(r['machine']))+'%N' for r in accepted)+']'
    aggregate.write_text(closure.aggregate_source(modules, namespace, 4096, len(accepted))+f'''
From BBB24 Require Import BoardManifest.
Definition inventory : list N := {inventory}.
Lemma inventory_checked : manifest_check inventory board = true.
Proof. vm_compute. reflexivity. Qed.
Theorem inventory_exact : manifest_board inventory = board.
Proof. apply manifest_check_sound. exact inventory_checked. Qed.
Print Assumptions inventory_exact.
''')
    aggregate_result = compile_row(aggregate, flags, evidence, args)
    if aggregate_result['status'] != 'compiled':
        raise ValueError('Aggregate failed; no proof report published')
    paths.append(aggregate)
    module = namespace+'.All'
    def object_snapshot():
        return {'generated_sha256': {p.name: sha(p) for p in paths},
                'object_sha256': {p.with_suffix('.vo').name: sha(p.with_suffix('.vo')) for p in paths},
                'dependency_objects_sha256': {str(Path(k).with_suffix('.vo')): sha((ROOT/k).with_suffix('.vo'))
                    for k in sources if k.endswith('.v')}}
    before_audit = object_snapshot()
    audit = execute(['coqchk', '-silent', '-bytecode-compiler', 'yes', *flags, module],
                    directory/'coqchk.log', args.audit_timeout, args.memory_mib)
    write_json(directory/'audit.json', audit)
    if audit['status'] != 'compiled':
        raise ValueError('Recursive audit failed; no proof report published')
    if object_snapshot() != before_audit:
        raise ValueError('Generated source or Coq objects changed during audit')
    if sha(INPUT) != evidence['input_sha256'] or any(sha(ROOT/k) != v for k,v in sources.items()):
        raise ValueError('Proof sources changed during audit')
    for name, expected in data['source_sha256'].items():
        if sha(ROOT/name) != expected:
            raise ValueError('Campaign source changed during audit')
    success_path = Path(str(prefix)+'-input.json')
    success = {'columns': closure.FIELDS, 'selected_rows': len(accepted),
               'rows': [[r[k] for k in closure.FIELDS] for r in accepted],
               'queue_input_sha256': sha(INPUT)}
    if success_path.exists() and json.loads(success_path.read_text()) != success:
        raise ValueError('Frozen successful inventory changed; select a new batch version')
    write_json(success_path, success)
    state_delta = len({r['machine'] for r in accepted} & set(data['state_pending']))
    descriptor = {'id': 'NextTimeout'+''.join(x.title() for x in args.batch.split('-')),
                  'module': module, 'board': 'board', 'sound': 'sound', 'small_sound': 'small_sound',
                  'was_pending': 'was_pending', 'state_bound': 4096, 'instruction_bound': 4096,
                  'scope': 'both', 'rows': len(accepted),
                  'inventories': [{'path': str(success_path.relative_to(ROOT)),
                                   'format': 'columns', 'order': 'input'}],
                  'load_paths': [{'path': str(directory.relative_to(ROOT)), 'namespace': namespace}]}
    report = {'status': 'recursively kernel-audited', 'scope': 'All completions of each partial family',
              'queue_input_sha256': sha(INPUT), 'input_sha256': sha(success_path),
              'source_sha256': sources, 'baseline_source_sha256': data['source_sha256'],
              'selection': {'modes': args.modes, 'offset': args.offset, 'limit': args.limit},
              'resources': {'workers': 1, 'address_space_mib': args.memory_mib,
                            'row_timeout_seconds': args.timeout, 'audit_timeout_seconds': args.audit_timeout},
              'attempted': len(rows), 'checked_families': len(accepted),
              'mode_counts': dict(Counter(r['mode'] for r in accepted)),
              'failure_counts': dict(Counter(r['status'] for r in results if r['status'] != 'compiled')),
              'new_both_vs_campaign_final': len(accepted), 'new_state_vs_campaign_final': state_delta,
              'baseline_cohort_remaining_after_this_batch': {'both': 33492-len(accepted), 'state': 2758-state_delta},
              'coverage_theorem': module+'.coverage', 'discharge_theorem': module+'.discharged',
              'nonhalt': module+'.nonhalt', 'inventory_exact': module+'.inventory_exact',
              'board_descriptor': descriptor, 'results': results, 'aggregate': aggregate_result,
              'audit': audit, 'generated_sha256': {p.name: sha(p) for p in paths},
              'validation': 'VM checker and original pending membership per family; exact inventory equality; recursive coqchk of aggregate and transitive dependencies.'}
    final = json.loads((ROOT/'research/campaign-final-summary.json').read_text())
    if any(sha(ROOT/k) != v for k,v in final['inputs'].items()):
        raise ValueError('Baseline inventory changed during audit')
    current_receipt = {'input_sha256': sha(success_path), 'source_sha256': sources,
                       'coq_version': evidence['coq_version'], 'audit': audit,
                       'snapshot_unchanged_during_audit': True, **before_audit}
    write_json(directory/'audited-receipt.json', current_receipt)
    if previous:
        stable = ('checked_families', 'mode_counts', 'new_both_vs_campaign_final',
                  'new_state_vs_campaign_final', 'board_descriptor', 'generated_sha256')
        if any(previous[k] != report[k] for k in stable):
            raise ValueError('Audited proof scope differs from frozen batch')
    else:
        write_json(report_path, report)
        write_json(Path(str(prefix)+'-board.json'), descriptor)
    print(json.dumps({k: report[k] for k in ('checked_families', 'failure_counts',
                                           'new_both_vs_campaign_final', 'new_state_vs_campaign_final')}), flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('action', choices=('prepare', 'run'))
    parser.add_argument('--batch', default='pilot-v1')
    parser.add_argument('--modes', default='ng,finite,hist,rw')
    parser.add_argument('--offset', type=int, default=0)
    parser.add_argument('--limit', type=int, default=0)
    parser.add_argument('--timeout', type=int, default=30)
    parser.add_argument('--audit-timeout', type=int, default=900)
    parser.add_argument('--memory-mib', type=int, default=3072)
    parser.add_argument('--resume', action='store_true')
    args = parser.parse_args()
    if args.offset < 0 or args.limit < 0 or min(args.timeout, args.audit_timeout, args.memory_mib) <= 0:
        parser.error('Invalid limit')
    if not set(args.modes.split(',')) <= {'ng', 'finite', 'hist', 'rw'}:
        parser.error('Invalid method')
    prepare() if args.action == 'prepare' else run(args)


if __name__ == '__main__':
    main()
