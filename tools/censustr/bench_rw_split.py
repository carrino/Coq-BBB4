#!/usr/bin/env python3
"""Time original serial stages and their generated split on identical inputs.

Prerequisites through RepWLTr.vo must already be compiled with the chosen
Coq toolchain. This is a phase benchmark, not a from-source proof build.
All selected stage checks are recompiled even if their .vo files exist.
Native companion compilation, when requested, is timed as part of each
unit. Run before and after sequentially to avoid cross-run contention.

Example:
  python3 tools/censustr/bench_rw_split.py --stages 09 --jobs 4 \
      --coqc /path/to/coqc --baseline-ref 797d2692 --output /tmp/rw09-bench
"""
import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import json
import os
from pathlib import Path
import platform
import subprocess
import time

import gen_provtr_rw as gen

REPO = Path(__file__).resolve().parents[2]


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--stages', default='09', help='comma-separated stage numbers')
    ap.add_argument('--jobs', type=int, default=4)
    ap.add_argument('--coqc', default='coqc')
    ap.add_argument('--coqnative', help='also compile each native companion')
    ap.add_argument('--baseline-ref', required=True)
    ap.add_argument('--output', type=Path, required=True)
    ap.add_argument('--phase', choices=['both', 'before', 'after'], default='both')
    args = ap.parse_args()
    if args.jobs < 1:
        ap.error('--jobs must be positive')
    selected = sorted(set(map(int, args.stages.split(','))))
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    rows = gen.read_manifest(REPO/'tools/censustr/provtr_rw_stages.tsv')
    parts = gen.render_parts(rows)
    manifest = {}
    originals = []
    for n in selected:
        path = f'theories/CensusTr/ProvTr_RW_{n:02d}.v'
        old = subprocess.check_output(['git', 'show', f'{args.baseline_ref}:{path}'],
                                      cwd=REPO, text=True)
        expected = [r for r in rows if r['stage'] == n]
        actual = list(gen.ROW_RE.finditer(old))
        if not expected or len(actual) != len(expected):
            raise ValueError(f'baseline is not the original stage {n}')
        for match, row in zip(actual, expected):
            name = f'tm_rw{n:02d}_{row["index"]:04d}'
            if (match[1] != row['spec'] or match[7] != gen.tm_lambda(name, row['spec'])
                or tuple(map(int, match.groups()[9:])) != tuple(row[k] for k in gen.FIELDS[3:])):
                raise ValueError(f'baseline differs for {name}')
        before = output/f'Before_RW_{n:02d}.v'
        before.write_text(old)
        originals.append(before)
        for name, text in parts.items():
            if name.startswith(f'RWParts/ProvTr_RW_{n:02d}_'):
                path = REPO/'theories/CensusTr'/name
                if path.read_text() != text:
                    raise ValueError(f'stale generated part {path}')
                manifest[path] = text
    record = dict(host=platform.platform(), machine=platform.machine(),
                  logical_cpus=os.cpu_count(), jobs=args.jobs, stages=selected,
                  baseline_ref=args.baseline_ref,
                  coq_version=subprocess.check_output([args.coqc, '--version'], text=True).strip(),
                  native_companions=bool(args.coqnative), results=[])
    def save():
        (output/'timings.json').write_text(json.dumps(record, indent=2)+'\n')
    def run(path):
        start = time.monotonic()
        with (output/(path.stem+'.log')).open('w') as log:
            result = subprocess.run([args.coqc, '-native-compiler', 'no', '-Q',
                                     str(REPO/'theories'), 'BBB4', str(path)],
                                    cwd=REPO, stdout=log, stderr=subprocess.STDOUT)
            if result.returncode == 0 and args.coqnative:
                result = subprocess.run([args.coqnative, '-Q', str(REPO/'theories'),
                                         'BBB4', str(path.with_suffix('.vo'))],
                                        cwd=REPO, stdout=log, stderr=subprocess.STDOUT)
        value = dict(file=str(path), seconds=round(time.monotonic()-start, 3),
                     exit_code=result.returncode)
        print(json.dumps(value), flush=True)
        if result.returncode:
            raise RuntimeError(f'{path} failed; see {output/(path.stem+".log")}')
        return value
    def phase(label, paths, wrappers=()):
        start = time.monotonic()
        entry = dict(phase=label, files=[])
        record['results'].append(entry)
        with ThreadPoolExecutor(max_workers=args.jobs) as pool:
            for future in as_completed([pool.submit(run, p) for p in paths]):
                entry['files'].append(future.result())
                save()
        for path in wrappers:
            entry['files'].append(run(path))
        entry['wall_seconds'] = round(time.monotonic()-start, 3)
        entry['sum_compile_seconds'] = round(sum(x['seconds'] for x in entry['files']), 3)
        save()
        print(f'{label}: {entry["wall_seconds"]} seconds wall', flush=True)
    save()
    if args.phase in ['both', 'before']:
        phase('before', originals)
    if args.phase in ['both', 'after']:
        # Start the expensive singleton checks first, without changing list order.
        ordered = sorted(manifest, key=lambda p: -sum(
            int(m[5]) for m in gen.ROW_RE.finditer(manifest[p])))
        phase('after', ordered, [REPO/f'theories/CensusTr/ProvTr_RW_{n:02d}.v'
                                for n in selected])


if __name__ == '__main__':
    main()
