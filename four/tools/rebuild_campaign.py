"""Rebuild recorded census boards in dependency order from compact inputs.

No search is run. Each command replays a published proof bundle, and the final
step checks their combined coverage theorem. Use --list to inspect the exact
commands, --validate to check the board-to-step coverage without running proofs,
--only STEP for one dependency closure, or --jobs 2 on a 32 GiB host.
Individual replay tools control their own hash-checked resume behavior.
"""
import argparse
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
import json
from pathlib import Path
import re
import shlex
import subprocess
import time

REPO = Path(__file__).resolve().parents[2]


def read_plan(path, target):
    data = json.loads(path.read_text())
    steps = {}
    for step in data['steps']:
        name = step['id']
        if not re.fullmatch(r'[a-z][a-z0-9_-]*', name) or name in steps:
            raise ValueError('Invalid or repeated build step')
        if not step['command'] or any(not isinstance(arg, str) or not arg for arg in step['command']):
            raise ValueError(f'Invalid command for {name}')
        if any(not isinstance(dep, str) for dep in step.get('depends', [])):
            raise ValueError(f'Invalid dependency for {name}')
        if any(not isinstance(board, str) or not re.fullmatch(r'[A-Za-z][A-Za-z0-9_.]*', board)
               for board in step.get('boards', [])):
            raise ValueError(f'Invalid board module for {name}')
        steps[name] = step
    chosen, active = set(), set()
    def visit(name):
        if name in active:
            raise ValueError('Cycle in build dependencies')
        if name not in steps:
            raise ValueError(f'Unknown dependency or target: {name}')
        if name in chosen:
            return
        active.add(name)
        for dependency in steps[name].get('depends', []):
            visit(dependency)
        active.remove(name); chosen.add(name)
    visit(target)
    selected = {name: step for name, step in steps.items() if name in chosen}
    validate_coverage(selected, target)
    return selected


def validate_coverage(steps, target):
    """Check declared producer coverage; the final Coq audit proves the claims."""
    producers = {}
    for name, step in steps.items():
        for module in step.get('boards', []):
            if module in producers:
                raise ValueError(f'Multiple build steps produce {module}')
            producers[module] = name
    manifest = steps[target].get('coverage_manifest')
    if manifest is None:
        return {'target': target, 'steps': len(steps), 'boards': producers}
    path = REPO/manifest
    data = json.loads(path.read_text())
    modules = [board['module'] for board in data['boards']]
    if len(set(modules)) != len(modules):
        raise ValueError(f'Repeated module in {manifest}')
    missing = sorted(set(modules)-producers.keys())
    if missing:
        raise ValueError('Campaign boards without a reachable replay step: '+', '.join(missing))
    return {'target': target, 'steps': len(steps), 'manifest': manifest,
            'boards': {module: producers[module] for module in modules}}


def run_step(step, directory):
    log = directory/(step['id']+'.log')
    start = time.monotonic()
    print(f"Starting {step['id']}: {shlex.join(step['command'])}", flush=True)
    with log.open('w') as stream:
        process = subprocess.run(step['command'], cwd=REPO, stdout=stream, stderr=subprocess.STDOUT, check=False)
    seconds = time.monotonic()-start
    print(f"{'Passed' if process.returncode == 0 else 'FAILED'} {step['id']} ({seconds:.1f}s); log: {log}", flush=True)
    return process.returncode


def execute(steps, directory, jobs):
    pending, done, running, failed = set(steps), set(), {}, []
    directory.mkdir(parents=True, exist_ok=True)
    with ThreadPoolExecutor(max_workers=jobs) as pool:
        while pending or running:
            if not failed:
                for name, step in steps.items():
                    if len(running) >= jobs:
                        break
                    if name in pending and set(step.get('depends', [])) <= done:
                        running[pool.submit(run_step, step, directory)] = name
                        pending.remove(name)
            if not running:
                if failed:
                    break
                raise RuntimeError('No runnable build step')
            finished, _ = wait(running, timeout=30, return_when=FIRST_COMPLETED)
            for future in finished:
                name = running.pop(future)
                try:
                    code = future.result()
                except Exception as error:
                    print(f'FAILED {name}: {error}', flush=True)
                    code = 1
                if code:
                    failed.append(name)
                else:
                    done.add(name)
    if failed:
        raise RuntimeError('Replay failed: '+', '.join(failed)+'. Dependent steps were not started.')
    print(f'All {len(done)} selected replay steps passed.', flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--plan', type=Path, default=REPO/'four/research/campaign-build.json')
    parser.add_argument('--only', default='campaign')
    parser.add_argument('--jobs', type=int, default=1)
    parser.add_argument('--list', action='store_true')
    parser.add_argument('--validate', action='store_true',
                        help='Validate dependencies and declared board coverage; do not run proofs')
    parser.add_argument('--log-dir', type=Path, default=REPO/'four/build/campaign-rebuild')
    args = parser.parse_args()
    if not 1 <= args.jobs <= 8:
        parser.error('--jobs must be between 1 and 8; memory is usually the limiting factor')
    steps = read_plan(args.plan, args.only)
    if args.validate:
        print(json.dumps(validate_coverage(steps, args.only), indent=2))
        return
    if args.list:
        for name, step in steps.items():
            print(name+': '+shlex.join(step['command']))
        return
    execute(steps, args.log_dir, args.jobs)


if __name__ == '__main__':
    main()
