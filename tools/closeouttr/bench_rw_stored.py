#!/usr/bin/env python3
"""Recompile closeout searches and stored checks with prebuilt dependencies.

The before sources are reconstructed from the retained search parameters,
so this benchmark also works after a squash merge. The after phase includes
compiling all certificate data. Both phases run coqc and coqnative, with the
same batch concurrency. Run without other heavy jobs for comparable times.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
from pathlib import Path
import platform
import subprocess
import sys
import time

import gen_rw_stored as gen
from bench_lean_walk import worker


def main():
    if len(sys.argv) > 1 and sys.argv[1] == '--worker':
        raise SystemExit(worker(sys.argv[4:], sys.argv[2], sys.argv[3]))
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--batches', nargs='+', default=['BR_02'])
    ap.add_argument('--jobs', type=int, default=4)
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    if args.jobs < 1:
        ap.error('--jobs must be positive')
    if len(set(args.batches)) != len(args.batches):
        ap.error('--batches must not contain duplicates')
    certificates = gen.read_certificates()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    inputs = {}
    for batch in args.batches:
        certs = {name: cert for name, cert in certificates.items()
                 if gen.NAME.fullmatch(name)[1] == batch}
        if not certs:
            ap.error(f'no stored certificates for batch {batch}')
        path = gen.REPO / 'theories/CloseoutTr' / f'CBT_{batch}.v'
        source = path.read_text()
        before = output / f'Before_{batch}.v'
        before.write_text(gen.original_batch(source, certs) +
                          f'\nPrint Assumptions cbt_{batch}_covers.\n')
        inputs[batch] = dict(before=before, after=path, certificates=certs,
                             source_sha256=hashlib.sha256(source.encode()).hexdigest())
    flags = ['-Q', str(gen.REPO / 'theories'), 'BBB4', '-Q', str(output), 'CloseoutBench']
    record = dict(platform=platform.platform(), jobs=args.jobs, batches=args.batches,
                  compiler=subprocess.check_output(['coqc', '--version'], text=True).strip(),
                  revision=subprocess.check_output(['git', 'rev-parse', 'HEAD'],
                                                   cwd=gen.REPO, text=True).strip(),
                  prerequisites_prebuilt=True, native_companions=True,
                  batch_source_sha256={b: x['source_sha256'] for b, x in inputs.items()},
                  results=[])

    def measure(name, command):
        result_path = output / (name + '.json')
        result = subprocess.run([sys.executable, str(Path(__file__).resolve()),
                                 '--worker', str(output / (name + '.log')),
                                 str(result_path), *command], cwd=gen.REPO)
        value = json.loads(result_path.read_text())
        if result.returncode:
            raise RuntimeError(f'{name} failed; see {output / (name + ".log")}')
        return value

    def compile_batch(phase, batch):
        item = inputs[batch]
        files = ([gen.DATA / ('Data_' + name + '.v') for name in sorted(item['certificates'])]
                 if phase == 'after' else []) + [item[phase]]
        results = []
        for path in files:
            for compiler, suffix in [('coqc', '.v'), ('coqnative', '.vo')]:
                extra = ['-native-compiler', 'no'] if compiler == 'coqc' else []
                results.append(measure(f'{phase}_{path.stem}_{compiler}',
                                       [compiler, *extra, *flags, str(path.with_suffix(suffix))]))
        return dict(batch=batch, files=results)

    for phase in ['before', 'after']:
        start = time.monotonic()
        with ThreadPoolExecutor(max_workers=args.jobs) as pool:
            results = list(pool.map(lambda b: compile_batch(phase, b), args.batches))
        record['results'].append(dict(phase=phase, wall_seconds=time.monotonic()-start,
                                      batches=results))
        (output / 'timings.json').write_text(json.dumps(record, indent=2) + '\n')
        print(phase, record['results'][-1]['wall_seconds'], flush=True)
    audit = output / 'StoredCloseoutAssumptions.v'
    audit.write_text('\n'.join(
        f'From BBB4.CloseoutTr Require Import CBT_{b}.\nPrint Assumptions cbt_{b}_covers.'
        for b in args.batches) + '\n')
    record['audit'] = measure('assumptions', ['coqc', '-native-compiler', 'no', *flags, str(audit)])
    (output / 'timings.json').write_text(json.dumps(record, indent=2) + '\n')


if __name__ == '__main__':
    main()
