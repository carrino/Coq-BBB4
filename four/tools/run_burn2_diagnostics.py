"""Run the two bounded diagnostic clusters through existing state checkers."""
import json
import os
from pathlib import Path
import resource
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]


def exact(path, text):
    if path.exists() and path.read_text() != text:
        raise ValueError('Refusing to change frozen diagnostic input: ' + str(path))
    path.write_text(text)


def main():
    resource.setrlimit(resource.RLIMIT_AS, (2147483648, 2147483648))
    plan = json.loads((ROOT / 'research/burn2-state-diagnostic-plan.json').read_text())
    env = dict(os.environ, OMP_NUM_THREADS='1', OPENBLAS_NUM_THREADS='1', MKL_NUM_THREADS='1')
    for row in plan['plans']:
        prefix = ROOT / ('research/burn2-diagnostic-' + row['cluster'])
        input_path = prefix.with_name(prefix.name + '-input.txt')
        input_manifest = prefix.with_name(prefix.name + '-input-manifest.json')
        stages = prefix.with_name(prefix.name + '-stages.json')
        output = ROOT / ('build/burn2-diagnostic-' + row['cluster'])
        report = prefix.with_name(prefix.name + '-search.json')
        exact(input_path, ''.join(machine + '\n' for machine in row['machines']))
        exact(input_manifest, json.dumps({'scope': 'Untrusted finite-trace diagnostic selection.',
             'remaining_rows': row['rows'], 'remaining_sha256': row['input_sha256']}, indent=2) + '\n')
        exact(stages, json.dumps(row['stages'], indent=2) + '\n')
        output.mkdir(parents=True, exist_ok=True)
        tool = 'state_pipeline_sweep.py' if row['cluster'] == 'short' else 'state_repwl_sweep.py'
        command = [sys.executable, str(ROOT / 'tools' / tool), '--input', str(input_path),
                   '--input-manifest', str(input_manifest), '--output-dir', str(output),
                   '--report', str(report), '--stages', str(stages), '--probe', str(ROOT / row['probe']),
                   '--bound', str(row['bound']), '--timeout', str(row['timeout_seconds']), '--sample', '0']
        if report.exists():
            command.append('--check')
        with (output / 'sweep.log').open('w') as log:
            subprocess.run(command, stdout=log, stderr=subprocess.STDOUT, check=True, env=env,
                           timeout=row['rows'] * len(row['stages']) * row['timeout_seconds'] + 60)
        result = json.loads(report.read_text())
        print(json.dumps({'cluster': row['cluster'], 'candidates': result['candidate_rows'],
                          'remaining': result['not_accepted_rows'], 'stages': result['results']}), flush=True)


if __name__ == '__main__':
    main()
