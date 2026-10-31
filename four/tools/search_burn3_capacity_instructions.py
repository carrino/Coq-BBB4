"""Bounded existing-checker probes selected by finite instruction traces.

This discovery pilot targets early last-observed instructions and frequently
observed missing targets. Only separate Coq replay can establish a bound.
"""
import hashlib
import json
from pathlib import Path
import resource
import subprocess

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / 'build/burn3-capacity-instruction'
REPORT = ROOT / 'research/burn3-capacity-instruction-search.json'
PROBE = ROOT / 'build/wave3/driver-v2/probe'
STAGES = [
    dict(mode='hist', size=4, history=3, anchor=4096, fuel=16384, extra=32),
    dict(mode='hist', size=3, history=5, anchor=4096, fuel=16384, extra=32),
    dict(mode='hist', size=5, history=2, anchor=4096, fuel=16384, extra=32),
    dict(mode='hist', size=2, history=8, anchor=4096, fuel=16384, extra=32),
    dict(mode='rw', size=7, history=0, anchor=4096, fuel=8192, extra=2),
    dict(mode='rw', size=4, history=0, anchor=4096, fuel=8192, extra=3),
]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def exact(path, text):
    if path.exists() and path.read_text() != text:
        raise ValueError('Refusing to change frozen search artifact: ' + str(path))
    path.write_text(text)


def main():
    resource.setrlimit(resource.RLIMIT_AS, (2147483648, 2147483648))
    source = ROOT / 'research/burn3-capacity-instruction-diagnostics.json'
    diagnostics = json.loads(source.read_text())
    selected = []
    for row in diagnostics['rows']:
        target = row['targets'][str(row['missing_any_witness'][0])]
        if target['category'] == 'last_observed_before_anchor' or target['total_firings'] > 1000:
            selected.append(row['machine'])
    if len(selected) != 5:
        raise ValueError('Expected five targeted rows')
    sources = {str(p.relative_to(ROOT)): sha(p) for p in
               (source, PROBE, Path(__file__), ROOT / 'tools/advanced_probe_v2.ml')}
    remaining, results, candidates = selected.copy(), [], []
    BASE.mkdir(parents=True, exist_ok=True)
    for index, stage in enumerate(STAGES):
        if not remaining:
            break
        input_path = BASE / f'targeted-stage-{index:02d}-input.txt'
        result_path = BASE / f'targeted-stage-{index:02d}.tsv'
        exact(input_path, ''.join(machine + '\n' for machine in remaining))
        command = [str(PROBE), stage['mode'], '4096', str(stage['size']),
                   str(stage['anchor']), str(stage['fuel']), str(stage['extra']),
                   str(stage['history']), '2', str(input_path)]
        if not result_path.exists():
            result = subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                    text=True, timeout=2 * len(remaining) + 10, check=True)
            exact(result_path, result.stdout)
        rows = []
        for line in result_path.read_text().splitlines():
            machine, status, seconds = line.split('\t')
            if status not in ('candidate', 'rejected', 'timeout', 'stack_overflow'):
                raise ValueError('Unexpected native status')
            rows.append(dict(machine=machine, status=status, seconds=float(seconds)))
        if [row['machine'] for row in rows] != remaining:
            raise ValueError('Native output inventory differs')
        for row in rows:
            if row['status'] == 'candidate':
                candidates.append(dict(machine=row['machine'], bound=4096, **stage))
        remaining = [row['machine'] for row in rows if row['status'] != 'candidate']
        results.append(dict(stage=stage, output_sha256=sha(result_path), rows=rows))
        print(json.dumps(dict(stage=index, candidates=len(candidates), remaining=len(remaining))), flush=True)
    if any(sha(ROOT / name) != digest for name, digest in sources.items()):
        raise ValueError('Search source changed')
    report = dict(scope='Untrusted candidate search; no proof claims.', sources_sha256=sources,
                  selected=selected, results=results, candidates=candidates, remaining=remaining,
                  workers=1, timeout_per_stage_row=2)
    exact(REPORT, json.dumps(report, indent=2, sort_keys=True) + '\n')


if __name__ == '__main__':
    main()
