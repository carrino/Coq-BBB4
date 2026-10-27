"""Replay the unassigned suffix of a frozen state-pipeline prefix.

Checked BOTH overlaps and queued-only BOTH overlaps are deferred separately.
Queued assignments never contribute a proof claim. Every selected family still
gets its own VM checker and actual pending-membership proof.
"""
import argparse
import csv
import hashlib
import io
import json
from pathlib import Path
from types import SimpleNamespace

import check_state_pipeline_batch as base
import check_state_pipeline_prefix as prefix
import state_work_assignment as assignment

ROOT = base.ROOT


def partition(prefix_input, assignment_input):
    desc, full, _, tail = prefix.load(SimpleNamespace(input=prefix_input))
    _, checked, queued = assignment.load(assignment_input)
    groups, deferred = [], []
    for shard in tail:
        retained = []
        for row in shard['rows']:
            status = assignment.classify(base.unpack(row), checked, queued)
            if status == 'unassigned':
                retained.append(row)
            else:
                deferred.append((row, status))
        if retained:
            if groups and groups[-1]['stage'] == shard['stage']:
                groups[-1]['rows'].extend(retained)
            else:
                groups.append({'stage': shard['stage'], 'certificate': shard['certificate'], 'rows': retained})
    if desc['selected_rows']+sum(len(g['rows']) for g in groups)+len(deferred) != full['selected_rows']:
        raise ValueError('Prefix, selected, and deferred rows do not partition the complete original input')
    return desc, full, groups, deferred


def descriptor(prefix_input, assignment_input):
    desc, full, groups, deferred = partition(prefix_input, assignment_input)
    return {
        'scope': 'Scheduling partition only; queued BOTH exclusions are not proof evidence.',
        'prefix_input': prefix.relative(prefix_input), 'prefix_input_sha256': base.sha(prefix_input),
        'assignment_input': prefix.relative(assignment_input), 'assignment_input_sha256': base.sha(assignment_input),
        'full_input': desc['full_input'], 'full_input_sha256': desc['full_input_sha256'],
        'full_candidate_rows': full['selected_rows'], 'prefix_rows': desc['selected_rows'],
        'selected_rows': sum(len(g['rows']) for g in groups),
        'deferred_checked_both': sum(status == 'checked_both' for _, status in deferred),
        'deferred_queued_both': sum(status == 'queued_both' for _, status in deferred),
        'state_bound': full['state_bound'], 'instruction_bound': None,
    }


def load(args):
    data = json.loads(args.input.read_text())
    p, a = ROOT/data['prefix_input'], ROOT/data['assignment_input']
    if base.sha(p) != data['prefix_input_sha256'] or base.sha(a) != data['assignment_input_sha256']:
        raise ValueError('Selected-state scheduling input changed')
    if data != descriptor(p, a):
        raise ValueError('Selected-state partition differs from the frozen original inventory')
    _, full, groups, deferred = partition(p, a)
    return data, full, groups, deferred


def source_hashes(loadpath):
    names = ['check_state_pipeline_selected.py', 'state_work_assignment.py', 'check_campaign.py']
    return {**prefix.source_hashes(loadpath),
            **{'tools/'+name: base.sha(ROOT/'tools'/name) for name in names}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--select', action='store_true')
    parser.add_argument('--select-only', action='store_true')
    parser.add_argument('--refresh', action='store_true')
    parser.add_argument('--resume', action='store_true')
    parser.add_argument('--input', type=Path, default=ROOT/'research/state-deep-selected-input.json')
    parser.add_argument('--report', type=Path, default=ROOT/'research/state-deep-selected-summary.json')
    parser.add_argument('--output-dir', type=Path, default=ROOT/'build/state-deep-selected')
    parser.add_argument('--namespace', default='BBB24StateDeepSelected')
    parser.add_argument('--prefix-input', type=Path)
    parser.add_argument('--assignment-input', type=Path)
    parser.add_argument('--timeout', type=int, default=1800)
    parser.add_argument('--limit-shards', type=int, default=0)
    args = parser.parse_args()
    if not args.namespace.isidentifier() or args.timeout <= 0 or args.limit_shards < 0:
        raise ValueError('Invalid namespace, timeout, or shard limit')
    if args.select:
        if not args.refresh or args.prefix_input is None or args.assignment_input is None:
            raise ValueError('--select requires --refresh and both scheduling inputs')
        args.input.parent.mkdir(parents=True, exist_ok=True)
        args.input.write_text(json.dumps(descriptor(args.prefix_input, args.assignment_input), indent=2)+'\n')
    data, full, groups, deferred = load(args)
    if args.select_only:
        print(json.dumps(data, indent=2), flush=True)
        return
    shards = prefix.schedule(groups)
    limit = args.limit_shards or len(shards)
    if not 0 < limit <= len(shards):
        raise ValueError('Invalid nonempty selected-shard limit')
    selected, unselected = shards[:limit], shards[limit:]
    args.output_dir.mkdir(parents=True, exist_ok=True)
    loadpath = ['-Q', str(ROOT/'theories'), 'BBB24', '-Q', str(args.output_dir.resolve()), args.namespace]
    sources = source_hashes(loadpath); input_hash = base.sha(args.input)
    if not args.refresh:
        old = json.loads(args.report.read_text())
        if old['source_sha256'] != sources or old['input_sha256'] != input_hash:
            raise ValueError('Selected-state proof input changed; refresh and re-audit')
    paths, modules = [], []
    for i, shard in enumerate(selected):
        module = f'StateSelected{i:03}'
        path = args.output_dir/(module+'.v')
        text = base.shard_text(shard['rows'], shard['certificate'], data['state_bound'])
        reuse = args.resume and prefix.reusable(path, text, sources)
        if not reuse:
            path.write_text(text)
            seconds = base.run(['coqc', '-native-compiler', 'no', *loadpath, str(path.resolve())],
                               path.with_suffix('.log'), args.timeout)
            path.with_suffix('.checked.json').write_text(json.dumps(
                {**prefix.evidence(path, sources), 'vo_sha256': base.sha(path.with_suffix('.vo'))}, indent=2)+'\n')
        else:
            seconds = 0
        print(f'{"Reused" if reuse else "Checked"} {module}: {seconds}s', flush=True)
        paths.append(path); modules.append(module)
    count = sum(len(shard['rows']) for shard in selected)
    aggregate_name = 'StateSelectedAll' if limit == len(shards) else f'StateSelectedPrefix{limit:03}'
    aggregate = args.output_dir/(aggregate_name+'.v')
    aggregate.write_text(base.aggregate(modules, count, data['state_bound'], args.namespace))
    base.run(['coqc', '-native-compiler', 'no', *loadpath, str(aggregate.resolve())],
             args.output_dir/(aggregate_name+'.log'), args.timeout)
    module = args.namespace+'.'+aggregate_name
    base.run(['coqchk', '-silent', '-bytecode-compiler', 'yes', *loadpath, module],
             args.output_dir/(aggregate_name+'.coqchk.log'), args.timeout*(len(paths)+1))
    if input_hash != base.sha(args.input) or sources != source_hashes(loadpath):
        raise ValueError('Selected-state source/input changed during audit')
    if (data, full, groups, deferred) != load(args):
        raise ValueError('Selected-state assignment changed during audit')
    theorem = module+'.state_families_discharged'
    stream = io.StringIO(); writer = csv.writer(stream, delimiter='\t', lineterminator='\n')
    writer.writerow(['machine', 'state_bound', 'instruction_bound', 'state_census_linked',
                     'instruction_census_linked', 'stage', 'proof'])
    writer.writerows((base.unpack(row), data['state_bound'], '', 'yes', 'no', shard['stage'], theorem)
                     for shard in selected for row in shard['rows'])
    ledger = stream.getvalue()
    remaining_codes = {row for shard in unselected for row in shard['rows']} | {row for row, _ in deferred}
    _, _, _, tail = prefix.load(SimpleNamespace(input=ROOT/data['prefix_input']))
    remainder = ''.join(base.unpack(row)+'\n' for shard in tail for row in shard['rows'] if row in remaining_codes)
    deferred_text = 'machine\tstatus\n'+''.join(base.unpack(row)+'\t'+status+'\n' for row, status in deferred)
    paths.append(aggregate)
    report = {
        'scope': 'State-only selected suffix closeout; queued BOTH deferrals remain unproved here.',
        'full_candidate_rows': data['full_candidate_rows'], 'original_prefix_rows': data['prefix_rows'],
        'selected_candidate_rows': data['selected_rows'],
        'deferred_checked_both': data['deferred_checked_both'], 'deferred_queued_both': data['deferred_queued_both'],
        'state_checked_families': count, 'state_census_linked_families': count,
        'instruction_checked_families': 0, 'state_bound': data['state_bound'], 'instruction_bound': None,
        'state_coverage_theorem': module+'.state_coverage', 'state_discharge_theorem': theorem,
        'state_residual_predicate': module+'.state_pending',
        'validation': 'Selected row VM checkers, actual pending membership, and recursive coqchk.',
        'input_sha256': input_hash, 'source_sha256': sources,
        'shard_sha256': {p.name: base.sha(p) for p in paths},
        'generated_ledger': prefix.relative(args.output_dir/(aggregate_name+'.tsv')),
        'ledger_sha256': hashlib.sha256(ledger.encode()).hexdigest(),
        'unselected_rows': len(remaining_codes),
        'generated_unselected': prefix.relative(args.output_dir/(aggregate_name+'.unselected.txt')),
        'unselected_sha256': hashlib.sha256(remainder.encode()).hexdigest(),
        'generated_deferred': prefix.relative(args.output_dir/(aggregate_name+'.deferred.tsv')),
        'deferred_sha256': hashlib.sha256(deferred_text.encode()).hexdigest(),
    }
    contents = json.dumps(report, indent=2)+'\n'
    if args.refresh:
        args.report.parent.mkdir(parents=True, exist_ok=True); args.report.write_text(contents)
    elif args.report.read_text() != contents:
        raise ValueError('Selected-state replay differs from recorded report')
    (ROOT/report['generated_ledger']).write_text(ledger)
    (ROOT/report['generated_unselected']).write_text(remainder)
    (ROOT/report['generated_deferred']).write_text(deferred_text)
    print(json.dumps({k: report[k] for k in ('state_checked_families', 'deferred_checked_both',
                                           'deferred_queued_both', 'unselected_rows')}), flush=True)


if __name__ == '__main__':
    main()
