"""Combine census boards with complete, resumable kernel-audit validation.

The original campaign replayer remains frozen. This version can reuse locally
produced audit receipts only when source, object, dependency closure and Coq
runtime hashes match. Every uncached module is independently checked by coqchk.
Without usable local receipts, replay performs a full recursive audit.

Portable inputs never include audit receipts. Recorded audit metadata describes
the historical run; every replay writes its own actual audit mode under build/.
"""
import argparse
import json
from pathlib import Path
import subprocess
import time

from check_campaign import (ROOT, IDENT, aggregate_source, dependency_hashes,
                            inventory_source, ledger, load_manifest,
                            read_inventory, sha)
from kernel_audit_cache import audit, fresh_paths


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--manifest', type=Path, default=ROOT/'research/campaign-final-input.json')
    parser.add_argument('--report', type=Path, default=ROOT/'research/campaign-final-summary.json')
    parser.add_argument('--output-dir', type=Path, default=ROOT/'build/campaign-final')
    parser.add_argument('--namespace', default='BBB24CampaignFinal')
    parser.add_argument('--refresh', action='store_true')
    parser.add_argument('--resume', action='store_true')
    parser.add_argument('--compile-only', action='store_true', help='Diagnostic only: no audit, report or ledger publication')
    parser.add_argument('--timeout', type=int, default=14400)
    parser.add_argument('--audit-cache', type=Path, action='append', default=[],
                        help='Locally created exact-artifact audit receipt; not a portable proof input')
    parser.add_argument('--recursive', action='store_true', help='Force a fresh recursive audit')
    args = parser.parse_args()
    for field in ('manifest', 'report', 'output_dir'):
        setattr(args, field, getattr(args, field).resolve())
    if not IDENT.fullmatch(args.namespace):
        raise ValueError('Invalid campaign namespace')
    manifest, boards, paths, inputs = load_manifest(args.manifest)
    inputs['tools/check_campaign_v2.py'] = sha(Path(__file__))
    inputs['tools/kernel_audit_cache.py'] = sha(ROOT/'tools/kernel_audit_cache.py')
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
    for path in generated:
        receipt = path.with_suffix('.checked.json'); vo = path.with_suffix('.vo')
        current = {'source': sha(path), 'dependencies': dependency_hashes([path], flags), 'coq_version': compiler}
        if args.resume and receipt.exists() and vo.exists():
            prior = json.loads(receipt.read_text())
            if all(prior.get(key) == value for key, value in current.items()) and prior.get('vo_sha256') == sha(vo):
                print(f'Reused {path.stem}', flush=True); continue
        start = time.monotonic()
        with path.with_suffix('.log').open('w') as stream:
            subprocess.run(['coqc', '-native-compiler', 'no', *flags, str(path)], cwd=ROOT.parent,
                           stdout=stream, stderr=subprocess.STDOUT, check=True, timeout=args.timeout)
        receipt.write_text(json.dumps({**current, 'vo_sha256': sha(vo)}, indent=2)+'\n')
        print(f'Checked inventory {path.stem}: {time.monotonic()-start:.2f}s', flush=True)
    if args.compile_only:
        print('Compilation only; no audited report or ledger published.', flush=True)
        return
    receipt, audit_log = fresh_paths(args.output_dir, 'campaign-audit')
    checked = audit([args.namespace+'.Campaign'], [aggregate],
                    [(ROOT/path, namespace) for path, namespace in paths.items()],
                    receipt, audit_log, cache=args.audit_cache, recursive=args.recursive,
                    timeout=args.timeout)
    if dependencies != dependency_hashes(generated, flags):
        raise ValueError('Proof dependencies changed during the recursive audit')
    current_inputs = load_manifest(args.manifest)[3]
    current_inputs['tools/check_campaign_v2.py'] = sha(Path(__file__))
    current_inputs['tools/kernel_audit_cache.py'] = sha(ROOT/'tools/kernel_audit_cache.py')
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
    if args.refresh:
        report['recorded_audit'] = history
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
