#!/usr/bin/env python3
"""Compare VM/native conversion for identical complete closeout batches.

Build the native computation dependencies first, stop competing compiler jobs,
then use --batches NG_11 RW_03 --output work/closeout-native. Copies are compiled
in fresh processes; production proof objects are never overwritten.
"""
import argparse
import hashlib
import json
from pathlib import Path
import platform
import resource
import subprocess
import sys
import time

from native_checks import rewrite

REPO = Path(__file__).resolve().parents[2]


def worker(source, log, result):
    _, hard = resource.getrlimit(resource.RLIMIT_STACK)
    resource.setrlimit(resource.RLIMIT_STACK, (hard, hard))
    before = resource.getrusage(resource.RUSAGE_CHILDREN)
    start = time.monotonic()
    command = ['coqc', '-native-compiler', 'ondemand', '-Q', 'theories', 'BBB4',
               '-w', '-abstract-large-number', str(source)]
    with Path(log).open('w') as stream:
        process = subprocess.run(command, cwd=REPO, stdout=stream, stderr=subprocess.STDOUT)
    usage = resource.getrusage(resource.RUSAGE_CHILDREN)
    audit = Path(log).read_text()
    # These consumer theorems use the existing CTape denotation axiom.
    # Do not mistake their assumptions for closed boolean benchmark goals.
    expected = 'FunctionalExtensionality.functional_extensionality_dep'
    footprint = (audit[audit.index('Axioms:'):].strip() if 'Axioms:' in audit else '')
    declarations = [line for line in footprint.splitlines() if line and not line[0].isspace()]
    audited = declarations == ['Axioms:', expected]
    record = dict(command=command, wall_seconds=time.monotonic() - start,
                  user_seconds=usage.ru_utime - before.ru_utime,
                  system_seconds=usage.ru_stime - before.ru_stime,
                  max_rss_bytes=usage.ru_maxrss * (1 if sys.platform == 'darwin' else 1024),
                  exit_code=process.returncode, assumption_audit=footprint,
                  expected_assumptions=audited)
    Path(result).write_text(json.dumps(record, indent=2) + '\n')
    return process.returncode or (0 if audited else 1)


def main():
    if len(sys.argv) > 1 and sys.argv[1] == '--worker':
        return worker(*sys.argv[2:])
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--batches', nargs='+', default=['NG_11', 'RW_03'])
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if 'COQ_NATIVE_COMPILER_DEFAULT=no' in subprocess.check_output(['coqc', '-config'], text=True):
        parser.error('native-capable Coq required')
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    if (output / 'metadata.json').exists():
        parser.error('use a new output directory')
    sources = {}
    for batch in args.batches:
        path = REPO / 'theories/CloseoutTr' / f'CBT_{batch}.v'
        source = path.read_text()
        native = rewrite(source)
        vm = native.replace('native_cast_no_check', 'vm_cast_no_check')
        if native == vm:
            parser.error(f'{batch} contains no selected native searches')
        sources[batch] = dict(source=source, vm=vm, native=native)
    metadata = dict(platform=platform.platform(),
                    coq=subprocess.check_output(['coqc', '--version'], text=True),
                    revision=subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=REPO, text=True).strip(),
                    batch_sha256={b: hashlib.sha256(s['source'].encode()).hexdigest() for b, s in sources.items()})
    (output / 'metadata.json').write_text(json.dumps(metadata, indent=2) + '\n')
    for batch, item in sources.items():
        for evaluator in ['vm', 'native']:
            source = output / f'Bench_{batch}_{evaluator}.v'
            source.write_text(item[evaluator] + f'\nPrint Assumptions cbt_{batch}_covers.\n')
            result = source.with_suffix('.json')
            subprocess.run([sys.executable, str(Path(__file__).resolve()), '--worker',
                            str(source), str(source.with_suffix('.log')), str(result)], check=True)
            print(result.read_text(), flush=True)
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
