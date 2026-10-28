"""Audit a supplemental campaign, with an explicit exact-champion board.

Derived from frozen check_campaign_v2.py. Existing checkers and reports are
unchanged. New manifest validation and binary-bound wrappers are in
campaign_next_boards.py. Reports preserve recorded runtime audit metadata on
normal replay; latest local execution evidence is written only under build/.
"""
import argparse
import json
import os
from pathlib import Path
import resource
import subprocess
import time

from check_campaign import ROOT, IDENT, dependency_hashes, ledger, read_inventory, sha
from check_campaign_v2 import aggregate_source, snapshot_dependencies, relevant_caches
from campaign_next_boards import inventory_source, load_manifest
from kernel_audit_cache_v3 import audit, fresh_paths, snapshot


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--manifest', type=Path, default=ROOT/'research/next-campaign-input.json')
    parser.add_argument('--report', type=Path, default=ROOT/'research/next-campaign-summary.json')
    parser.add_argument('--output-dir', type=Path, default=ROOT/'build/next-campaign')
    parser.add_argument('--namespace', default='BBB24NextCampaign')
    parser.add_argument('--refresh', action='store_true')
    parser.add_argument('--resume', action='store_true')
    parser.add_argument('--compile-only', action='store_true', help='Diagnostic only: no audit, report or ledger publication')
    parser.add_argument('--audit-only', action='store_true', help='Require exact compiled inventory receipts and audit without recompiling')
    parser.add_argument('--timeout', type=int, default=14400)
    parser.add_argument('--audit-cache', type=Path, action='append', default=[],
                        help='Locally created exact-artifact audit receipt; not a portable proof input')
    parser.add_argument('--recursive', action='store_true', help='Freshly audit the complete closure across bounded phases')
    parser.add_argument('--memory-mib', type=int, default=2816, help='Hard address-space limit for this one-worker replay')
    args = parser.parse_args()
    if args.memory_mib <= 0 or args.timeout <= 0:
        parser.error('Resource limits must be positive')
    memory_bytes = args.memory_mib * 1024 * 1024
    resource.setrlimit(resource.RLIMIT_AS, (memory_bytes, memory_bytes))
    # Large certificate environments otherwise retain excessive major-heap
    # slack. This changes only collection policy, for coqc and coqchk alike.
    os.environ.setdefault('OCAMLRUNPARAM', 'o=5,O=10')
    if args.audit_only and args.compile_only:
        parser.error('--audit-only and --compile-only are mutually exclusive')
    for field in ('manifest', 'report', 'output_dir'):
        setattr(args, field, getattr(args, field).resolve())
    if not IDENT.fullmatch(args.namespace):
        raise ValueError('Invalid campaign namespace')
    manifest, boards, paths, inputs = load_manifest(args.manifest)
    for path in args.audit_cache:
        path.resolve().relative_to((ROOT/'build').resolve())
    args.output_dir.mkdir(parents=True, exist_ok=True)
    paths[str(args.output_dir.resolve().relative_to(ROOT))] = args.namespace
    flags = [part for path, namespace in paths.items() for part in ('-Q', str(ROOT/path), namespace)]
    generated = []
    for board in boards:
        path = args.output_dir/(board['id']+'.v')
        path.write_text(inventory_source(board)); generated.append(path)
    aggregate = args.output_dir/'Campaign.v'
    aggregate.write_text(aggregate_source(args.namespace, boards)); generated.append(aggregate)
    dependencies = dependency_hashes(generated, flags)
    compiler = subprocess.check_output(['coqc', '--version'], text=True)
    evidence = {'inputs': inputs, 'source_sha256': dependencies, 'coq_version': compiler}
    if not args.refresh and not args.compile_only:
        old = json.loads(args.report.read_text())
        if any(old[key] != value for key, value in evidence.items()):
            raise ValueError('Campaign proof inputs changed; a fresh audit is required')
    loadpaths = [(ROOT/path, namespace) for path, namespace in paths.items()]
    compiled = snapshot([aggregate], loadpaths) if args.audit_only else None
    for path in generated:
        receipt = path.with_suffix('.checked.json'); vo = path.with_suffix('.vo')
        source_dependencies = (snapshot_dependencies(compiled, args.namespace+'.'+path.stem)
                               if args.audit_only else dependency_hashes([path], flags))
        current = {'source': sha(path), 'dependencies': source_dependencies, 'coq_version': compiler}
        if (args.resume or args.audit_only) and receipt.exists() and vo.exists():
            prior = json.loads(receipt.read_text())
            if all(prior.get(key) == value for key, value in current.items()) and prior.get('vo_sha256') == sha(vo):
                print(f'Reused {path.stem}', flush=True); continue
        if args.audit_only:
            raise ValueError(f'Exact compilation receipt unavailable for {path.stem}; run --resume first')
        start = time.monotonic()
        with path.with_suffix('.log').open('w') as stream:
            subprocess.run(['coqc', '-native-compiler', 'no', *flags, str(path)], cwd=ROOT.parent,
                           stdout=stream, stderr=subprocess.STDOUT, check=True, timeout=args.timeout)
        receipt.write_text(json.dumps({**current, 'vo_sha256': sha(vo)}, indent=2)+'\n')
        print(f'Checked inventory {path.stem}: {time.monotonic()-start:.2f}s', flush=True)
    if args.compile_only:
        print('Compilation only; no audited report or ledger published.', flush=True)
        return
    # Large census VM evaluations must run before the complete certificate
    # environment is imported. A fresh replay still checks every dependency;
    # only receipts created during these phases are reused with --recursive.
    if compiled is None:
        compiled = snapshot([aggregate], loadpaths)
    core_modules = sorted(name for name in compiled['graph']
                          if name == 'BBB24.Bootstrap' or name.startswith('SmallBB.'))
    caches = [] if args.recursive else list(args.audit_cache)
    phases = []
    if core_modules:
        core_receipt, core_log = fresh_paths(args.output_dir, 'campaign-core-audit')
        print('Auditing bootstrap and SmallBB in a separate environment', flush=True)
        core = audit(core_modules, [Path(compiled['graph'][name]['source']) for name in core_modules],
                     loadpaths, core_receipt, core_log,
                     cache=relevant_caches(compiled, core_modules, caches),
                     recursive=args.recursive, timeout=args.timeout)
        phases.append({'role': 'bootstrap-smallbb', 'kind': core['kind'], 'receipt': str(core_receipt.relative_to(ROOT)),
                       'receipt_sha256': sha(core_receipt),
                       'checked_modules': len(core['checked_modules']),
                       'reused_modules': len(core['reused_modules'])})
        caches.append(core_receipt)
    for module, role in (('BBB24ClosureWave3.ClosureWaveAll', 'closure-prefix'),
                         ('BBB24Wave3Closure.ClosureWaveAll', 'closure-frontier')):
        if module not in compiled['graph']:
            continue
        phase_receipt, phase_log = fresh_paths(args.output_dir, 'campaign-'+role+'-audit')
        print('Auditing '+role+' in a separate environment', flush=True)
        phase = audit([module], [Path(compiled['graph'][module]['source'])], loadpaths,
                      phase_receipt, phase_log,
                      cache=relevant_caches(compiled, [module], caches), timeout=args.timeout)
        phases.append({'role': role, 'kind': phase['kind'],
                       'receipt': str(phase_receipt.relative_to(ROOT)),
                       'receipt_sha256': sha(phase_receipt),
                       'checked_modules': len(phase['checked_modules']),
                       'reused_modules': len(phase['reused_modules'])})
        caches.append(phase_receipt)
    for board in boards:
        if board['rows'] < 25000:
            continue
        module = args.namespace+'.'+board['id']
        phase_receipt, phase_log = fresh_paths(args.output_dir, 'campaign-inventory-'+board['id']+'-audit')
        print('Auditing oversized inventory '+board['id']+' separately', flush=True)
        phase = audit([module], [args.output_dir/(board['id']+'.v')], loadpaths,
                      phase_receipt, phase_log,
                      cache=relevant_caches(compiled, [module], caches), timeout=args.timeout)
        phases.append({'role': 'inventory-'+board['id'], 'kind': phase['kind'],
                       'receipt': str(phase_receipt.relative_to(ROOT)),
                       'receipt_sha256': sha(phase_receipt),
                       'checked_modules': len(phase['checked_modules']),
                       'reused_modules': len(phase['reused_modules'])})
        caches.append(phase_receipt)
    receipt, audit_log = fresh_paths(args.output_dir, 'campaign-audit')
    print('Auditing the complete campaign dependency closure', flush=True)
    checked = audit([args.namespace+'.Campaign'], [aggregate],
                    loadpaths, receipt, audit_log,
                    cache=relevant_caches(compiled, [args.namespace+'.Campaign'], caches),
                    recursive=args.recursive and not phases,
                    timeout=args.timeout)
    if dependencies != dependency_hashes(generated, flags):
        raise ValueError('Proof dependencies changed during the recursive audit')
    current_inputs = load_manifest(args.manifest)[3]
    if inputs != current_inputs:
        raise ValueError('Campaign inventory changed during the recursive audit')
    counts = {}
    ledgers = {}
    cohort_counts = {}
    cohort = set(read_inventory(manifest['cohort'])) if 'cohort' in manifest else None
    for scope in ('both', 'state'):
        families, contents = ledger(boards, scope)
        counts[scope] = len(families)
        path = args.output_dir/(scope+'-families.tsv')
        path.write_text(contents)
        ledgers[scope] = {'path': str(path.relative_to(ROOT)), 'sha256': sha(path)}
        if cohort is not None:
            unresolved = sorted(cohort-families.keys())
            path = args.output_dir/(scope+'-unproved-initial-cohort.txt')
            path.write_text(''.join(machine+'\n' for machine in unresolved))
            cohort_counts[scope] = {'cohort_rows': len(cohort), 'proved': len(cohort & families.keys()),
                                    'unproved': len(unresolved), 'unproved_path': str(path.relative_to(ROOT)),
                                    'unproved_sha256': sha(path)}
    report = {**evidence, 'scope': 'Distinct family IDs, with all completions covered; no raw-table weight subtraction.',
              'both_census_linked_families': counts['both'], 'state_census_linked_families': counts['state'],
              'initial_search_cohort': cohort_counts,
              'source_rows': {board['id']: len(board['machines']) for board in boards}, 'ledgers': ledgers,
              'module': args.namespace+'.Campaign', 'validation': 'Exact inventory VM proofs, typed bounds, pending membership, and coqchk validation of the complete transitive object dependency closure.',
              'original_structural_weights_unchanged': True, 'global_upper_bound_proved': False}
    # This audit's local receipt is historical execution evidence. A clean
    # replay may use a recursive pass where the recorded run reused receipts;
    # every portable proof input, inventory, count and theorem still must match.
    history = {'kind': checked['kind'], 'receipt': str(receipt.relative_to(ROOT)),
               'receipt_sha256': sha(receipt), 'checked_modules': len(checked['checked_modules']),
               'reused_modules': len(checked['reused_modules'])}
    history['phases'] = phases
    history['fresh_complete_closure'] = args.recursive or not args.audit_cache
    if args.refresh:
        report['recorded_audit'] = history
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(json.dumps(report, indent=2, sort_keys=True)+'\n')
    else:
        previous = json.loads(args.report.read_text())
        previous.pop('recorded_audit', None)
        if previous != report:
            raise ValueError('Campaign report differs from checked evidence')
    (args.output_dir/'latest-audit.json').write_text(json.dumps(history, indent=2)+'\n')
    print(json.dumps(counts), flush=True)


if __name__ == '__main__':
    main()
