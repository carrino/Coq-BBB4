#!/usr/bin/env python3
"""Time unchanged native census units, with prerequisites already built.

Run this script before and after rebuilding RunTr_WalkCompute.vo. Each sample
uses a fresh coqc process and checks the actual unit theorem, including its
assumptions. It never installs benchmark objects into the production walk.
"""
import argparse
import hashlib
import json
import platform
from pathlib import Path
import resource
import subprocess
import sys
import time

REPO = Path(__file__).resolve().parents[2]


def worker(source, log, result):
    _, hard = resource.getrlimit(resource.RLIMIT_STACK)
    resource.setrlimit(resource.RLIMIT_STACK, (hard, hard))
    command = ['coqc', '-Q', 'theories', 'BBB4', '-native-compiler', 'ondemand',
               '-w', '-abstract-large-number', str(source)]
    before = resource.getrusage(resource.RUSAGE_CHILDREN)
    start = time.monotonic()
    with open(log, 'w') as stream:
        proc = subprocess.run(command, cwd=REPO, stdout=stream,
                              stderr=subprocess.STDOUT)
    usage = resource.getrusage(resource.RUSAGE_CHILDREN)
    closed = 'Closed under the global context' in Path(log).read_text()
    record = dict(command=command, wall_seconds=time.monotonic() - start,
                  user_seconds=usage.ru_utime - before.ru_utime,
                  system_seconds=usage.ru_stime - before.ru_stime,
                  max_rss_bytes=usage.ru_maxrss * (1 if sys.platform == 'darwin' else 1024),
                  exit_code=proc.returncode, closed_assumptions=closed)
    Path(result).write_text(json.dumps(record, indent=2) + '\n')
    return proc.returncode or (0 if closed else 1)


def main():
    if len(sys.argv) > 1 and sys.argv[1] == '--worker':
        return worker(*sys.argv[2:])
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path, required=True)
    ap.add_argument('--units', nargs='+', type=int, default=[10, 63])
    args = ap.parse_args()
    if any(i < 0 or i >= 96 for i in args.units):
        ap.error('units must be in the unchanged 96-unit partition')
    config = subprocess.check_output(['coqc', '-config'], text=True)
    if 'COQ_NATIVE_COMPILER_DEFAULT=no' in config:
        ap.error('a native-capable Coq is required; VM fallback is not a native benchmark')
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    if (output / 'metadata.json').exists():
        ap.error('use a new output directory to preserve earlier measurements')
    sources = ['theories/ClosureTr.v', 'theories/CensusTr/DecideTr.v',
               'theories/Checkers/WrapTr.v', 'theories/Checkers/NGramTr.v',
               'theories/CensusTr/RunTr_Compute.v',
               'theories/CensusTr/RunTr_WalkCompute.v']
    metadata = dict(platform=platform.platform(),
                    revision=subprocess.check_output(['git', 'rev-parse', 'HEAD'],
                                                     cwd=REPO, text=True).strip(),
                    coq=subprocess.check_output(['coqc', '--version'], text=True),
                    source_sha256={p: hashlib.sha256((REPO / p).read_bytes()).hexdigest()
                                   for p in sources})
    (output / 'metadata.json').write_text(json.dumps(metadata, indent=2) + '\n')
    for unit in args.units:
        source = output / f'BenchUnit{unit:02d}.v'
        original = REPO / f'theories/CensusTr/Compute/UnitTr_{unit:02d}.v'
        source.write_text(original.read_text() + f'\nPrint Assumptions unit_tr_{unit:02d}.\n')
        result = output / f'unit{unit:02d}.json'
        subprocess.run([sys.executable, str(Path(__file__).resolve()), '--worker',
                        str(source), str(source.with_suffix('.log')), str(result)],
                       cwd=REPO, check=True)
        print(result.read_text(), flush=True)
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
