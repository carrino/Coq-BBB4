"""Audit an exact completed prefix of a frozen state-pipeline board.

The small descriptor pins the complete original input, then selects a prefix of
its deterministic shard schedule. Default replay reconstructs every selected
certificate from that tracked input; ignored survey output is never required.
Original inputs, shard names, sources and receipts remain reusable by full replay.
"""
import argparse
import csv
import hashlib
import io
import json
from pathlib import Path
from types import SimpleNamespace

import check_state_pipeline_batch as base

ROOT = base.ROOT


def relative(path):
    return str(path.resolve().relative_to(ROOT))


def schedule(groups):
    result = []
    for group in groups:
        for offset in range(0, len(group['rows']), base.SHARD_SIZE):
            result.append({'module': f'StateClosure{len(result):03}',
                           'rows': group['rows'][offset:offset+base.SHARD_SIZE],
                           'stage': group['stage'], 'certificate': group['certificate']})
    return result


def source_hashes(loadpath):
    return {**base.source_hashes(loadpath),
            'tools/check_state_pipeline_prefix.py': base.sha(Path(__file__))}


def evidence(path, sources):
    return {'source_sha256': base.sha(path),
            'dependencies_sha256': {k: v for k, v in sources.items() if k.endswith('.v')}}


def reusable(path, text, sources):
    receipt = path.with_suffix('.checked.json')
    vo = path.with_suffix('.vo')
    if not (path.exists() and receipt.exists() and vo.exists()):
        return False
    if path.read_text() != text:
        return False
    return json.loads(receipt.read_text()) == {**evidence(path, sources), 'vo_sha256': base.sha(vo)}


def select(args):
    if not args.refresh or args.full_input is None or args.original_output_dir is None or args.original_namespace is None:
        raise ValueError('--select requires --refresh and the three original-board arguments')
    if not args.original_namespace.isidentifier():
        raise ValueError('Invalid original namespace')
    data, groups = base.load(SimpleNamespace(input=args.full_input))
    shards = schedule(groups)
    loadpath = ['-Q', str(ROOT/'theories'), 'BBB24',
                '-Q', str(args.original_output_dir.resolve()), args.original_namespace]
    sources = source_hashes(loadpath)
    completed = 0
    for shard in shards:
        path = args.original_output_dir/(shard['module']+'.v')
        text = base.shard_text(shard['rows'], shard['certificate'], data['state_bound'])
        if not reusable(path, text, sources):
            break
        completed += 1
    count = args.prefix_shards or completed
    if not 0 < count <= completed:
        raise ValueError(f'Requested {count} shards, but only {completed} unchanged contiguous shards are compiled')
    descriptor = {
        'scope': 'Exact completed prefix of a state-only board; no instruction claim.',
        'full_input': relative(args.full_input), 'full_input_sha256': base.sha(args.full_input),
        'original_output_dir': relative(args.original_output_dir),
        'original_namespace': args.original_namespace,
        'selected_shards': count, 'full_shards': len(shards),
        'selected_rows': sum(len(s['rows']) for s in shards[:count]),
        'full_selected_rows': data['selected_rows'],
        'state_bound': data['state_bound'], 'instruction_bound': None,
    }
    args.input.parent.mkdir(parents=True, exist_ok=True)
    args.input.write_text(json.dumps(descriptor, indent=2)+'\n')


def load(args):
    desc = json.loads(args.input.read_text())
    full_input = ROOT/desc['full_input']
    if base.sha(full_input) != desc['full_input_sha256']:
        raise ValueError('Complete original state input differs from the frozen descriptor')
    data, groups = base.load(SimpleNamespace(input=full_input))
    shards = schedule(groups)
    count = desc['selected_shards']
    if type(count) is not int or not 0 < count <= len(shards):
        raise ValueError('Invalid shard prefix length')
    if (desc['full_shards'] != len(shards) or desc['full_selected_rows'] != data['selected_rows']
            or desc['selected_rows'] != sum(len(s['rows']) for s in shards[:count])
            or desc['state_bound'] != data['state_bound'] or desc['instruction_bound'] is not None
            or not desc['original_namespace'].isidentifier()):
        raise ValueError('Prefix descriptor does not match the complete original inventory')
    return desc, data, shards[:count], shards[count:]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--select', action='store_true')
    parser.add_argument('--refresh', action='store_true')
    parser.add_argument('--resume', action='store_true')
    parser.add_argument('--input', type=Path, required=True)
    parser.add_argument('--report', type=Path, required=True)
    parser.add_argument('--output-dir', type=Path, required=True)
    parser.add_argument('--namespace', required=True)
    parser.add_argument('--timeout', type=int, default=1800)
    parser.add_argument('--full-input', type=Path)
    parser.add_argument('--original-output-dir', type=Path)
    parser.add_argument('--original-namespace')
    parser.add_argument('--prefix-shards', type=int, default=0,
                        help='For --select only; zero means all already compiled contiguous shards')
    args = parser.parse_args()
    if not args.namespace.isidentifier() or args.prefix_shards < 0 or args.timeout <= 0:
        raise ValueError('Invalid namespace, shard count, or timeout')
    if args.select:
        select(args)
    desc, data, selected, unselected = load(args)
    original_dir = ROOT/desc['original_output_dir']
    original_namespace = desc['original_namespace']
    if args.output_dir.resolve() == original_dir.resolve() or args.namespace == original_namespace:
        raise ValueError('Prefix aggregate must use a distinct directory and namespace')
    original_dir.mkdir(parents=True, exist_ok=True)
    args.output_dir.mkdir(parents=True, exist_ok=True)
    loadpath = ['-Q', str(ROOT/'theories'), 'BBB24',
                '-Q', str(original_dir.resolve()), original_namespace,
                '-Q', str(args.output_dir.resolve()), args.namespace]
    sources = source_hashes(loadpath)
    input_hash = base.sha(args.input)
    if not args.refresh:
        old = json.loads(args.report.read_text())
        if old['source_sha256'] != sources or old['input_sha256'] != input_hash:
            raise ValueError('Prefix source/input changed; explicitly refresh and re-audit')
    paths = []
    for shard in selected:
        path = original_dir/(shard['module']+'.v')
        text = base.shard_text(shard['rows'], shard['certificate'], data['state_bound'])
        reuse = args.resume and reusable(path, text, sources)
        if not reuse:
            # Completed full-board shards are byte-identical; never overwrite a
            # different source under the same original module name silently.
            if path.exists() and path.read_text() != text:
                raise ValueError(f'Original shard source differs: {path}')
            path.write_text(text)
            seconds = base.run(['coqc', '-native-compiler', 'no', *loadpath, str(path.resolve())],
                               path.with_suffix('.prefix.log'), args.timeout)
            path.with_suffix('.checked.json').write_text(json.dumps(
                {**evidence(path, sources), 'vo_sha256': base.sha(path.with_suffix('.vo'))}, indent=2)+'\n')
        else:
            seconds = 0
        print(f'{"Reused" if reuse else "Checked"} {shard["module"]}: {seconds}s', flush=True)
        paths.append(path)
    aggregate = args.output_dir/'StateClosurePrefixAll.v'
    aggregate.write_text(base.aggregate([s['module'] for s in selected], desc['selected_rows'],
                                        data['state_bound'], original_namespace))
    base.run(['coqc', '-native-compiler', 'no', *loadpath, str(aggregate.resolve())],
             args.output_dir/'aggregate.log', args.timeout)
    module = args.namespace+'.StateClosurePrefixAll'
    base.run(['coqchk', '-silent', '-bytecode-compiler', 'yes', *loadpath, module],
             args.output_dir/'coqchk.log', args.timeout*(len(paths)+1))
    if input_hash != base.sha(args.input) or sources != source_hashes(loadpath):
        raise ValueError('Prefix input/source changed during audit')
    # Also revalidate the full pinned input and its source report after audit.
    desc2, data2, selected2, unselected2 = load(args)
    if (desc, data, selected, unselected) != (desc2, data2, selected2, unselected2):
        raise ValueError('Full source inventory changed during audit')
    theorem = module+'.state_families_discharged'
    stream = io.StringIO()
    writer = csv.writer(stream, delimiter='\t', lineterminator='\n')
    writer.writerow(['machine', 'state_bound', 'instruction_bound', 'state_census_linked',
                     'instruction_census_linked', 'stage', 'proof'])
    writer.writerows((base.unpack(row), data['state_bound'], '', 'yes', 'no', shard['stage'], theorem)
                     for shard in selected for row in shard['rows'])
    ledger = stream.getvalue()
    remainder = ''.join(base.unpack(row)+'\n' for shard in unselected for row in shard['rows'])
    paths.append(aggregate)
    report = {
        'scope': 'State-only direct-core prefix closeout; no instruction or raw-table count claim.',
        'source_rows': data['source_rows'],
        'full_candidate_rows': data['selected_rows'],
        'state_checked_families': desc['selected_rows'],
        'state_census_linked_families': desc['selected_rows'],
        'instruction_checked_families': 0,
        'state_bound': data['state_bound'], 'instruction_bound': None,
        'state_coverage_theorem': module+'.state_coverage',
        'state_discharge_theorem': theorem,
        'state_residual_predicate': module+'.state_pending',
        'validation': 'Exact original shard prefix, VM checker and pending proofs, recursive coqchk.',
        'input_sha256': input_hash,
        'full_input': desc['full_input'], 'full_input_sha256': desc['full_input_sha256'],
        'original_namespace': original_namespace,
        'original_output_dir': desc['original_output_dir'],
        'source_sha256': sources,
        'shard_sha256': {relative(p): base.sha(p) for p in paths},
        'generated_ledger': relative(args.output_dir/'families.tsv'),
        'ledger_sha256': hashlib.sha256(ledger.encode()).hexdigest(),
        'unselected_rows': data['selected_rows']-desc['selected_rows'],
        'generated_unselected': relative(args.output_dir/'unselected.txt'),
        'unselected_sha256': hashlib.sha256(remainder.encode()).hexdigest(),
    }
    contents = json.dumps(report, indent=2)+'\n'
    if args.refresh:
        args.report.write_text(contents)
    elif args.report.read_text() != contents:
        raise ValueError('Prefix replay differs from the recorded report')
    (args.output_dir/'families.tsv').write_text(ledger)
    (args.output_dir/'unselected.txt').write_text(remainder)
    print(json.dumps({k: report[k] for k in ('state_checked_families', 'unselected_rows',
                                           'instruction_checked_families')}), flush=True)


if __name__ == '__main__':
    main()
