"""Reproducible, resumable search with the extracted BBB24 checker ladder.

This does not establish any theorem. Every accepted row remains a candidate
until its checker expression is replayed by Coq. The original census and
grouping inventories are never rewritten. Raw logs live in ignored build/.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
MACHINE = re.compile(r'(?:(?:[0-3][LR][AB]|---)){4}_(?:(?:[0-3][LR][AB]|---)){4}')
DEFAULT_STAGES = [
    {'mode': 'ng', 'size': 2, 'anchor': 128, 'fuel': 100, 'extra': 4},
    {'mode': 'ng', 'size': 3, 'anchor': 128, 'fuel': 200, 'extra': 4},
    {'mode': 'rw', 'size': 2, 'anchor': 128, 'fuel': 512, 'extra': 2},
]
STATUSES = {'candidate', 'rejected', 'timeout', 'stack_overflow'}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def encoded(rows):
    return ''.join(row + '\n' for row in rows)


def read_rows(path):
    rows = path.read_text().splitlines()
    if not rows or len(rows) != len(set(rows)) or any(not MACHINE.fullmatch(r) for r in rows):
        raise ValueError(f'Empty, duplicate, or invalid machine inventory: {path}')
    return rows


def read_results(path, expected, repair=False):
    if not path.exists():
        return {}
    raw = path.read_bytes()
    if raw and not raw.endswith(b'\n'):
        if not repair:
            raise ValueError(f'Interrupted partial row in {path}')
        raw = raw[:raw.rfind(b'\n') + 1]
        path.write_bytes(raw)
    found = {}
    for line in raw.decode().splitlines():
        machine, status, seconds = line.split('\t')
        if machine not in expected or machine in found or status not in STATUSES:
            raise ValueError(f'Invalid, duplicate, or out-of-scope result: {line}')
        seconds = float(seconds)
        if not 0 <= seconds < float('inf'):
            raise ValueError(f'Invalid duration: {line}')
        found[machine] = (status, seconds)
    return found


def source_hashes():
    pending = [ROOT / 'tools' / n for n in
               ('ExtractPipeline.v', 'pipeline_probe.ml', 'pipeline_sweep.py')]
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


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path, default=ROOT/'build/grouping/nonblank.representatives.txt')
    parser.add_argument('--output-dir', type=Path, default=ROOT/'build/pipeline/pilot')
    parser.add_argument('--report', type=Path, default=ROOT/'research/pipeline-pilot.json')
    parser.add_argument('--probe', type=Path, default=ROOT/'build/pipeline/probe')
    parser.add_argument('--stages', type=Path, help='JSON list of mode,size,anchor,fuel,extra objects')
    parser.add_argument('--bound', type=int, default=4096)
    parser.add_argument('--timeout', type=float, default=0.25, help='Seconds per row and stage')
    parser.add_argument('--sample', type=int, default=128, help='Lowest machine SHA256 hashes; 0 means every input row')
    parser.add_argument('--build', action='store_true', help='Extract and compile; requires checker .vo dependencies built first')
    parser.add_argument('--check', action='store_true', help='Validate complete saved logs and compare outputs without rerunning')
    args = parser.parse_args()
    if args.build:
        build = ROOT/'build/pipeline'
        build.mkdir(parents=True, exist_ok=True)
        commands = [
            ['coqc', '-native-compiler', 'no', '-Q', 'theories', 'BBB24', 'tools/ExtractPipeline.v'],
            ['ocamlopt', '-w', '-a', '-I', 'build/pipeline', '-c', 'build/pipeline/checkers.mli'],
            ['ocamlopt', '-w', '-a', '-I', 'build/pipeline', '-c', 'build/pipeline/checkers.ml'],
            ['ocamlopt', '-w', '-a', '-I', 'build/pipeline', '-c', '-o', 'build/pipeline/pipeline_probe.cmx', 'tools/pipeline_probe.ml'],
            ['ocamlopt', '-w', '-a', '-I', 'build/pipeline', 'unix.cmxa', 'build/pipeline/checkers.cmx',
             'build/pipeline/pipeline_probe.cmx', '-o', str(args.probe.resolve())],
        ]
        for command in commands:
            subprocess.run(command, cwd=ROOT, check=True)
    if args.bound < 0 or args.sample < 0 or not 0 < args.timeout < float('inf'):
        parser.error('bound/sample must be nonnegative and timeout finite and positive')
    stages = json.loads(args.stages.read_text()) if args.stages else DEFAULT_STAGES
    for stage in stages:
        if set(stage) != {'mode', 'size', 'anchor', 'fuel', 'extra'} or stage['mode'] not in {'ng', 'rw'}:
            parser.error('invalid stage fields or mode')
        if not all(type(stage[k]) is int for k in ('size', 'anchor', 'fuel', 'extra')):
            parser.error('stage parameters must be integers')
        if stage['size'] < 1 or stage['fuel'] < 1 or stage['extra'] < (2 if stage['mode'] == 'rw' else 1) or not 0 <= stage['anchor'] <= args.bound:
            parser.error('invalid stage parameters')
    if not stages:
        parser.error('at least one stage is required')
    inventory = read_rows(args.input)
    rows = sorted(inventory, key=lambda m: hashlib.sha256(m.encode()).digest())
    if args.sample:
        rows = rows[:args.sample]
    args.output_dir.mkdir(parents=True, exist_ok=True)
    manifest = {
        'input_sha256': digest(args.input), 'input_rows': len(inventory),
        'selected_rows': len(rows), 'selection': 'lowest SHA256(machine UTF-8) values' if args.sample else 'all rows, ordered by SHA256(machine UTF-8)',
        'selected_sha256': hashlib.sha256(encoded(rows).encode()).hexdigest(),
        'bound': args.bound, 'timeout_seconds_per_stage_row': args.timeout,
        'stages': stages, 'probe_sha256': digest(args.probe),
        'extraction_sha256': digest(ROOT/'build/pipeline/checkers.ml'),
        'sources_sha256': source_hashes(),
    }
    manifest_path = args.output_dir/'manifest.json'
    if manifest_path.exists():
        if json.loads(manifest_path.read_text()) != manifest:
            raise ValueError('Input, parameters, sources, or binary changed; use a new output directory')
    elif args.check:
        raise ValueError('No saved manifest to validate')
    else:
        manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True)+'\n')
        (args.output_dir/'selected.txt').write_text(encoded(rows))
    if (args.output_dir/'selected.txt').read_text() != encoded(rows):
        raise ValueError('Saved selected inventory differs')
    accepted = []
    reports = []
    remaining = rows
    for index, stage in enumerate(stages):
        results_path = args.output_dir/f'stage-{index:02d}.tsv'
        found = read_results(results_path, set(remaining), repair=not args.check)
        todo = [m for m in remaining if m not in found]
        if todo and args.check:
            raise ValueError(f'Stage {index} incomplete: {len(todo)} rows missing')
        if todo:
            todo_path = args.output_dir/f'stage-{index:02d}-todo.txt'
            todo_path.write_text(encoded(todo))
            command = [str(args.probe.resolve()), stage['mode'], str(args.bound),
                       str(stage['size']), str(stage['anchor']), str(stage['fuel']),
                       str(stage['extra']), str(args.timeout), str(todo_path.resolve())]
            with results_path.open('a') as output:
                subprocess.run(command, stdout=output, check=True)
            found = read_results(results_path, set(remaining))
        if len(found) != len(remaining):
            raise ValueError(f'Incomplete stage {index}')
        counts = Counter(status for status, _ in found.values())
        reports.append({'stage': index, **stage, 'rows': len(remaining),
                        'statuses': dict(sorted(counts.items())),
                        'sum_row_seconds': round(sum(t for _, t in found.values()), 6),
                        'results_sha256': digest(results_path) if results_path.exists() else None})
        accepted += [{'machine': m, 'stage': index, **stage, 'bound': args.bound}
                     for m in remaining if found[m][0] == 'candidate']
        remaining = [m for m in remaining if found[m][0] != 'candidate']
        print(json.dumps(reports[-1], sort_keys=True), flush=True)
    candidates = 'machine\tstage\tmode\tbound\tsize\tanchor\tfuel\textra\n' + ''.join(
        '\t'.join(str(row[k]) for k in ('machine', 'stage', 'mode', 'bound', 'size', 'anchor', 'fuel', 'extra'))+'\n'
        for row in accepted)
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
