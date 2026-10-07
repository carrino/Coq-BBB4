#!/usr/bin/env python3
"""Compare individual lap boards with bundles, compiling the same proofs.

Common Coq and native prerequisites must already be built. Both phases
force source compilation followed by native companion compilation. Run
without other compiler jobs; this is a phase benchmark, not a cold build.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import json
from pathlib import Path
import platform
import subprocess
import time

import gen_lap_bundles as gen


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--bundles', default='BundleLAPT_000,BundleLAPT_001,BundleLAPQ_000,BundleLAPQ_001')
    ap.add_argument('--jobs', type=int, default=4)
    ap.add_argument('--output', type=Path, required=True)
    ap.add_argument('--coqc', default='coqc')
    ap.add_argument('--coqnative', default='coqnative')
    ap.add_argument('--phase', choices=['before','after','both'], default='both')
    ap.add_argument('--vm-only', action='store_true')
    args = ap.parse_args()
    if args.jobs < 1:
        ap.error('--jobs must be positive')
    selected = args.bundles.split(',')
    grouped = gen.groups()
    before, after = [], []
    for name in selected:
        paths = grouped[name]
        bundle = gen.BUNDLES/(name+'.v')
        if bundle.read_text() != gen.render_bundle(paths):
            raise ValueError(f'stale bundle: {bundle}')
        before.extend(paths)
        after.append(bundle)
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    record = dict(platform=platform.platform(), jobs=args.jobs,
                  compiler=subprocess.check_output([args.coqc,'--version'],text=True).strip(),
                  native_companions=not args.vm_only, boards=len(before),
                  bundles=selected, results=[])
    def save():
        (output/'timings.json').write_text(json.dumps(record,indent=2)+'\n')
    def run(path):
        commands = [[args.coqc,'-native-compiler','no','-w','-abstract-large-number',
                     '-Q',str(gen.REPO/'theories'),'BBB4',str(path)]]
        if not args.vm_only:
            commands.append([args.coqnative,'-Q',str(gen.REPO/'theories'),
                             'BBB4',str(path.with_suffix('.vo'))])
        start = time.monotonic()
        stages = []
        with (output/(path.stem+'.log')).open('w') as log:
            for command in commands:
                stage_start = time.monotonic()
                process = subprocess.run(command,cwd=gen.REPO,stdout=log,stderr=subprocess.STDOUT)
                stages.append(dict(compiler=command[0],seconds=round(time.monotonic()-stage_start,3),
                                   exit_code=process.returncode))
                if process.returncode:
                    break
        return dict(file=str(path),seconds=round(time.monotonic()-start,3),stages=stages)
    for phase, paths in [('before',before),('after',after)]:
        if args.phase not in ['both',phase]:
            continue
        start = time.monotonic()
        entry = dict(phase=phase,files=[])
        record['results'].append(entry)
        save()
        failed = False
        with ThreadPoolExecutor(max_workers=args.jobs) as pool:
            for future in as_completed([pool.submit(run,path) for path in paths]):
                value = future.result()
                entry['files'].append(value)
                failed |= any(s['exit_code'] for s in value['stages'])
                save()
                if len(entry['files']) % 25 == 0 or len(paths) <= 4 or failed:
                    print(f'{phase}: {len(entry["files"])}/{len(paths)} files; last {value}',flush=True)
        entry['wall_seconds'] = round(time.monotonic()-start,3)
        entry['sum_compile_seconds'] = round(sum(f['seconds'] for f in entry['files']),3)
        save()
        print(f'{phase}: {entry["wall_seconds"]} seconds wall',flush=True)
        if failed:
            raise SystemExit('compilation failed; see logs')


if __name__ == '__main__':
    main()
