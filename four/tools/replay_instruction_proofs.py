"""Rebuild every registered instruction batch with a fresh recursive audit."""
import argparse
import json
from pathlib import Path
import re
import resource
import subprocess
import sys
import time

from check_campaign import ROOT, sha


def command(name):
    if re.fullmatch(r'instruction-burn[1-9][0-9]*', name):
        return ['check_instruction_closure.py', '--name', name]
    drivers = {'instruction-tails': 'check_instruction_tails.py',
               'instruction-s030': 'check_instruction_s030.py',
               'instruction-sparse-return': 'check_instruction_sparse_return.py',
               'instruction-sparse-twos': 'check_instruction_sparse_twos.py',
               'instruction-unary-pair': 'check_instruction_unary_pair.py',
               'instruction-counter-context': 'check_instruction_counter_context.py',
               'instruction-boundary-counter': 'check_instruction_boundary_counter.py',
               'instruction-counter-conjugate': 'check_instruction_counter_conjugate.py',
               'instruction-counter-three': 'check_instruction_counter_three.py'}
    if name not in drivers:
        raise ValueError('No reviewed replay driver for accepted batch: ' + name)
    return [drivers[name]]


def accepted():
    path = ROOT / 'research/instruction-accepted-batches.json'
    data = json.loads(path.read_text())
    if data.get('schema_version') != 1 or not data.get('batches'):
        raise ValueError('Invalid accepted instruction registry')
    names = []
    for item in data['batches']:
        name = item['name']
        command(name)
        if name in names or sha(ROOT / 'research' / (name + '-checked.json')) != item['report_sha256']:
            raise ValueError('Repeated or changed accepted instruction report')
        names.append(name)
    return names


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--only', help='Replay one accepted batch')
    parser.add_argument('--list', action='store_true')
    parser.add_argument('--no-build-core', action='store_true')
    parser.add_argument('--jobs', type=int, default=2, help='Shared theory build workers')
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error('Worker count must be positive')
    names = accepted()
    if args.only:
        if args.only not in names:
            parser.error('Batch is not in the accepted registry')
        names = [args.only]
    if args.list:
        for name in names:
            print(name + ': ' + ' '.join(command(name)))
        return
    soft, hard = resource.getrlimit(resource.RLIMIT_STACK)
    target = 64 * 1024**2
    if hard != resource.RLIM_INFINITY and hard < target:
        raise ValueError('Instruction proof replay requires a 64 MiB stack limit')
    if soft != resource.RLIM_INFINITY and soft < target:
        resource.setrlimit(resource.RLIMIT_STACK, (target, hard))
    if not args.no_build_core:
        subprocess.run([sys.executable, str(ROOT / 'tools/instruction_core_targets.py'),
                        '--build', '--jobs', str(args.jobs)], check=True)
    build = ROOT / 'build/instruction-replay'
    build.mkdir(parents=True, exist_ok=True)
    result = dict(status='running', batches=[])
    output = build / 'result.json'
    output.write_text(json.dumps(result, indent=2) + '\n')
    for name in names:
        selected = command(name)
        cmd = [sys.executable, str(ROOT / 'tools' / selected[0]), *selected[1:]]
        log = build / (name + '.log')
        started = time.monotonic()
        print('Replaying ' + name + '; log: ' + str(log), flush=True)
        with log.open('w') as stream:
            run = subprocess.run(cmd, stdout=stream, stderr=subprocess.STDOUT, timeout=7200)
        result['batches'].append(dict(name=name, returncode=run.returncode,
                                     seconds=round(time.monotonic()-started, 3)))
        if run.returncode:
            result['status'] = 'failed'
            output.write_text(json.dumps(result, indent=2) + '\n')
            print('\n'.join(log.read_text(errors='replace').splitlines()[-60:]), file=sys.stderr)
            raise RuntimeError('Instruction proof replay failed: ' + name)
        output.write_text(json.dumps(result, indent=2) + '\n')
    result['status'] = 'passed'
    output.write_text(json.dumps(result, indent=2) + '\n')
    print('All selected instruction batches compiled and recursively audited.', flush=True)


if __name__ == '__main__':
    main()
