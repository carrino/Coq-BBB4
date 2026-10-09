#!/usr/bin/env python3
"""Compare the same RepWL parts with kernel search and stored certificates.

Checker prerequisites must already be built with the selected Coq. Every
measured source file is forcibly recompiled. The after phase includes both
certificate-data compilation and proof checking, not just loading .vo data.
Run without other heavy jobs. This is a phase benchmark, not a full walk.
The default VM pass produces .vo files; --mode native subsequently measures
their native companions, with prerequisite native companions already built.
The default before sources are regenerated from the unchanged row manifest,
so this comparison remains reproducible after a squash merge. An optional
--baseline-ref additionally checks those sources against an older revision.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import json
from pathlib import Path
import platform
import subprocess
import sys
import time

import gen_provtr_rw as gen
from bench_lean_walk import worker

REPO = Path(__file__).resolve().parents[2]


def main():
    if len(sys.argv) > 1 and sys.argv[1] == '--worker':
        raise SystemExit(worker(sys.argv[4:], sys.argv[2], sys.argv[3]))
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--baseline-ref')
    ap.add_argument('--certificates', nargs='+', metavar='RW_NN_NNNN',
                    help='measure parts containing these certificates; default: all')
    ap.add_argument('--coqc', default='coqc')
    ap.add_argument('--coqnative', default='coqnative')
    ap.add_argument('--mode', choices=['vm', 'native'], default='vm')
    ap.add_argument('--jobs', type=int, default=4)
    ap.add_argument('--output', required=True, type=Path)
    ap.add_argument('--phase', choices=['before', 'after', 'both'], default='both')
    args = ap.parse_args()
    if args.jobs < 1:
        ap.error('--jobs must be positive')
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    rows = gen.read_manifest(REPO/'tools/censustr/provtr_rw_stages.tsv')
    certs = gen.read_stored_certificates(rows)
    if not certs:
        ap.error('no stored certificates')
    names = {f'RW_{stage:02d}_{index:04d}': (stage, index) for stage, index in certs}
    selected = set(args.certificates or names)
    if selected - names.keys():
        ap.error('unknown certificates: ' + ', '.join(sorted(selected - names.keys())))
    original = gen.render_parts(rows)
    updated = gen.render_parts(rows, certificates=certs)
    parts = sorted(name for name in updated
                   if name.startswith('RWParts/') and
                   any(f'Require DataTr_{cert}.' in updated[name] for cert in selected))
    before_jobs, after_jobs = [], []
    for name in parts:
        relative = 'theories/CensusTr/'+name
        baseline = original[name]
        if args.baseline_ref:
            historical = subprocess.check_output(
                ['git', 'show', f'{args.baseline_ref}:{relative}'], cwd=REPO, text=True)
            if historical != baseline:
                raise ValueError(f'baseline is not the original proof: {name}')
        source = REPO/relative
        if source.read_text() != updated[name]:
            raise ValueError(f'stale proof source: {name}')
        old = output/('Before_'+source.name)
        old.write_text(baseline)
        before_jobs.append((source.stem, [old]))
        data_files = []
        for stage, index in certs:
            data = f'DataTr_RW_{stage:02d}_{index:04d}'
            if f'Require {data}.' in updated[name]:
                data_name = f'RWCerts/{data}.v'
                path = REPO/'theories/CensusTr'/data_name
                if path.read_text() != updated[data_name]:
                    raise ValueError(f'stale certificate source: {path}')
                data_files.append(path)
        after_jobs.append((source.stem, data_files+[source]))
    record = dict(platform=platform.platform(), jobs=args.jobs,
                  baseline_ref=args.baseline_ref,
                  baseline_kind='original-search-source',
                  compiler=subprocess.check_output([args.coqc, '--version'],text=True).strip(),
                  native_companions=args.mode == 'native',
                  certificates=len(selected), selected_certificates=sorted(selected), results=[])
    def save():
        filename = 'native_timings.json' if args.mode == 'native' else 'timings.json'
        (output/filename).write_text(json.dumps(record,indent=2)+'\n')
    def run(job):
        name, paths = job
        started = time.monotonic()
        files = []
        for path in paths:
            if args.mode == 'native':
                artifact = path.with_suffix('.vo')
                if not artifact.is_file():
                    raise ValueError(f'run the VM pass first: missing {artifact}')
                command = [args.coqnative, '-Q', str(REPO/'theories'),
                           'BBB4', str(artifact)]
                log_name = path.stem+'.native.log'
            else:
                command = [args.coqc, '-native-compiler', 'no',
                           '-w', '-abstract-large-number', '-Q',
                           str(REPO/'theories'), 'BBB4', str(path)]
                log_name = path.stem+'.log'
            result_path = output / (log_name + '.json')
            result = subprocess.run(
                [sys.executable, str(Path(__file__).resolve()), '--worker',
                 str(output / log_name), str(result_path), *command], cwd=REPO)
            measured = json.loads(result_path.read_text())
            files.append(dict(measured, file=str(path),
                              seconds=round(measured['wall_seconds'], 3)))
            if result.returncode:
                break
        value = dict(part=name,seconds=round(time.monotonic()-started,3),files=files)
        print(json.dumps(value),flush=True)
        return value
    for phase,jobs in [('before',before_jobs),('after',after_jobs)]:
        if args.phase not in ['both',phase]:
            continue
        start = time.monotonic()
        entry = dict(phase=phase,parts=[])
        record['results'].append(entry)
        save()
        failed = False
        with ThreadPoolExecutor(max_workers=args.jobs) as pool:
            for future in as_completed([pool.submit(run,job) for job in jobs]):
                value = future.result()
                entry['parts'].append(value)
                failed |= any(f['exit_code'] for f in value['files'])
                save()
        entry['wall_seconds'] = round(time.monotonic()-start,3)
        entry['sum_compile_seconds'] = round(sum(p['seconds'] for p in entry['parts']),3)
        save()
        print(f'{phase}: {entry["wall_seconds"]} seconds wall',flush=True)
        if failed:
            raise SystemExit('compilation failed; see logs')


if __name__ == '__main__':
    main()
