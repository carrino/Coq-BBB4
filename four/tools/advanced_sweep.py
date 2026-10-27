"""Resumable finite/history/repeated-word search over a prior sweep's remainder.

Search acceptance is untrusted until Coq replays the exact checker expression.
The previous sweep is immutable. Each stage records all candidate, rejection,
timeout, and stack-limit outcomes; failures stay in the next stage's input.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import subprocess

from pipeline_sweep import digest, encoded, read_rows, read_results

ROOT = Path(__file__).resolve().parents[1]
BUILD = ROOT/'build/advanced'
FIELDS = ('machine', 'stage', 'mode', 'bound', 'size', 'anchor', 'fuel', 'extra', 'history')


def source_hashes():
    pending = [ROOT/'tools'/n for n in
               ('ExtractAdvanced.v', 'advanced_probe.ml', 'advanced_sweep.py', 'pipeline_sweep.py')]
    files = set()
    imports = re.compile(r'From BBB24(?:\.([\w.]+))? Require (?:Import|Export)\s+([^.]*)\.')
    while pending:
        path = pending.pop()
        if path in files:
            continue
        files.add(path)
        if path.suffix == '.v':
            for prefix, modules in imports.findall(path.read_text()):
                for module in modules.split():
                    pending.append(ROOT/'theories'/Path(*filter(None, prefix.split('.')))/(module+'.v'))
    return {str(p.relative_to(ROOT)): digest(p) for p in sorted(files)}


def build_probe(probe):
    BUILD.mkdir(parents=True, exist_ok=True)
    commands = [
        ['coqc', '-native-compiler', 'no', '-Q', 'theories', 'BBB24', 'tools/ExtractAdvanced.v'],
        ['ocamlopt', '-w', '-a', '-I', 'build/advanced', '-c', 'build/advanced/checkers.mli'],
        ['ocamlopt', '-w', '-a', '-I', 'build/advanced', '-c', 'build/advanced/checkers.ml'],
        ['ocamlopt', '-w', '-a', '-I', 'build/advanced', '-c', '-o', 'build/advanced/advanced_probe.cmx', 'tools/advanced_probe.ml'],
        ['ocamlopt', '-w', '-a', '-I', 'build/advanced', 'unix.cmxa', 'build/advanced/checkers.cmx',
         'build/advanced/advanced_probe.cmx', '-o', str(probe.resolve())],
    ]
    for command in commands:
        subprocess.run(command, cwd=ROOT, check=True)


def stage_results(args, index, stage, remaining):
    shards = [remaining[i::args.workers] for i in range(args.workers)]
    paths = [args.output_dir/f'stage-{index:02d}-worker-{i:02d}.tsv' for i in range(args.workers)]
    running = []
    try:
        for i, (rows, path) in enumerate(zip(shards, paths)):
            found = read_results(path, set(rows), repair=not args.check)
            todo = [m for m in rows if m not in found]
            if todo and args.check:
                raise ValueError(f'Stage {index}, worker {i}: {len(todo)} results missing')
            if not todo:
                continue
            todo_path = args.output_dir/f'stage-{index:02d}-worker-{i:02d}-todo.txt'
            todo_path.write_text(encoded(todo))
            command = [str(args.probe.resolve()), stage['mode'], str(args.bound),
                       str(stage['size']), str(stage['anchor']), str(stage['fuel']),
                       str(stage['extra']), str(stage['history']), str(args.timeout),
                       str(todo_path.resolve())]
            output = path.open('a')
            try:
                process = subprocess.Popen(command, stdout=output)
            except BaseException:
                output.close()
                raise
            running.append((process, output))
        for process, _ in running:
            if process.wait() != 0:
                raise RuntimeError(f'Checker worker failed: {process.args}')
    finally:
        for process, output in running:
            if process.poll() is None:
                process.terminate()
            process.wait()
            output.close()
    found = {}
    for rows, path in zip(shards, paths):
        part = read_results(path, set(rows))
        if len(part) != len(rows):
            raise ValueError(f'Incomplete stage {index}: {path}')
        found.update(part)
    return found, [digest(p) if p.exists() else None for p in paths]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path, default=ROOT/'build/pipeline/low-budget/not-accepted.txt')
    parser.add_argument('--prior-report', type=Path, default=ROOT/'research/pipeline-low-budget.json')
    parser.add_argument('--output-dir', type=Path, default=BUILD/'pilot')
    parser.add_argument('--report', type=Path, default=ROOT/'research/advanced-pilot.json')
    parser.add_argument('--probe', type=Path, default=BUILD/'probe')
    parser.add_argument('--stages', type=Path, default=ROOT/'research/advanced-stages.json')
    parser.add_argument('--bound', type=int, default=4096)
    parser.add_argument('--timeout', type=float, default=0.25)
    parser.add_argument('--sample', type=int, default=128, help='Lowest machine SHA256 hashes; 0 selects the complete input')
    parser.add_argument('--workers', type=int, default=2)
    parser.add_argument('--build', action='store_true', help='Requires the Coq checker dependencies already compiled')
    parser.add_argument('--check', action='store_true', help='Validate saved complete logs without running search')
    args = parser.parse_args()
    if args.bound < 0 or args.sample < 0 or args.workers < 1 or not 0 < args.timeout < float('inf'):
        parser.error('invalid bound, sample size, worker count, or timeout')
    stages = json.loads(args.stages.read_text())
    if not stages:
        parser.error('at least one stage is required')
    for stage in stages:
        if set(stage) != {'mode', 'size', 'anchor', 'fuel', 'extra', 'history'} or stage['mode'] not in {'finite', 'hist', 'rw'}:
            parser.error('invalid stage fields or mode')
        if not all(type(stage[k]) is int for k in ('size', 'anchor', 'fuel', 'extra', 'history')):
            parser.error('checker parameters must be integers')
        if stage['size'] < 1 or stage['fuel'] < 1 or stage['extra'] < (2 if stage['mode'] == 'rw' else 1) or not 0 <= stage['anchor'] <= args.bound:
            parser.error('invalid checker parameters')
        if stage['history'] < 0 or (stage['mode'] != 'hist' and stage['history'] != 0):
            parser.error('history is nonnegative and must be zero for non-history modes')
    inventory = read_rows(args.input)
    prior = json.loads(args.prior_report.read_text())
    if prior['not_accepted_rows'] != len(inventory) or prior['not_accepted_sha256'] != digest(args.input):
        raise ValueError('Input does not match the prior report remainder')
    if args.build:
        build_probe(args.probe)
    rows = sorted(inventory, key=lambda m: hashlib.sha256(m.encode()).digest())
    if args.sample:
        rows = rows[:args.sample]
    args.output_dir.mkdir(parents=True, exist_ok=True)
    manifest = {
        'input_sha256': digest(args.input), 'input_rows': len(inventory),
        'prior_report_sha256': digest(args.prior_report), 'selected_rows': len(rows),
        'selection': 'lowest SHA256(machine UTF-8) values' if args.sample else 'all rows, ordered by SHA256(machine UTF-8)',
        'selected_sha256': hashlib.sha256(encoded(rows).encode()).hexdigest(),
        'bound': args.bound, 'both_bounds': True, 'workers': args.workers,
        'timeout_seconds_per_stage_row': args.timeout, 'stages': stages,
        'probe_sha256': digest(args.probe), 'extraction_sha256': digest(BUILD/'checkers.ml'),
        'sources_sha256': source_hashes(),
    }
    manifest_path = args.output_dir/'manifest.json'
    if manifest_path.exists():
        if json.loads(manifest_path.read_text()) != manifest:
            raise ValueError('Input, prior report, parameters, sources, or binary changed; use a new output directory')
    elif args.check:
        raise ValueError('No saved manifest to validate')
    else:
        manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True)+'\n')
        (args.output_dir/'selected.txt').write_text(encoded(rows))
    if (args.output_dir/'selected.txt').read_text() != encoded(rows):
        raise ValueError('Saved selected input differs')
    accepted = []
    reports = []
    remaining = rows
    for index, stage in enumerate(stages):
        found, log_hashes = stage_results(args, index, stage, remaining)
        counts = Counter(status for status, _ in found.values())
        reports.append({'stage': index, **stage, 'rows': len(remaining),
                        'statuses': dict(sorted(counts.items())),
                        'sum_row_seconds': round(sum(t for _, t in found.values()), 6),
                        'worker_results_sha256': log_hashes})
        accepted += [{'machine': m, 'stage': index, **stage, 'bound': args.bound}
                     for m in remaining if found[m][0] == 'candidate']
        remaining = [m for m in remaining if found[m][0] != 'candidate']
        print(json.dumps(reports[-1], sort_keys=True), flush=True)
    candidates = '\t'.join(FIELDS)+'\n' + ''.join(
        '\t'.join(str(row[k]) for k in FIELDS)+'\n' for row in accepted)
    report = {
        'status': 'Untrusted extracted checker search; zero kernel replay or census-link claims.',
        'manifest': manifest, 'results': reports, 'candidate_rows': len(accepted),
        'not_accepted_rows': len(remaining), 'kernel_checked_rows': 0, 'census_linked_rows': 0,
        'candidate_tsv_sha256': hashlib.sha256(candidates.encode()).hexdigest(),
        'not_accepted_sha256': hashlib.sha256(encoded(remaining).encode()).hexdigest(),
    }
    outputs = {args.output_dir/'candidates.tsv': candidates,
               args.output_dir/'not-accepted.txt': encoded(remaining),
               args.report: json.dumps(report, indent=2, sort_keys=True)+'\n'}
    for path, contents in outputs.items():
        if args.check:
            if not path.exists() or path.read_text() != contents:
                raise ValueError(f'Generated output differs: {path}')
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(contents)
    print(f'{len(accepted)} candidates; {len(remaining)} not accepted; no new proof claims.', flush=True)


if __name__ == '__main__':
    main()
