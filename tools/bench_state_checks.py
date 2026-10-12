#!/usr/bin/env python3
"""Compare VM/native evaluation of complete state certificate batches.

Build their imported modules first with a native-capable Coq. Run without
competing builds for wall-time comparisons. For example:

  python3 tools/bench_state_checks.py --output work/state-bench --reference-revision 5aa7cd98d \
    theories/Machines/Bulk/TCyc_05.v

Both variants preserve definitions and theorem statements, audit the final
theorem's assumptions, and compile copies without overwriting proof objects.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import resource
import subprocess
import sys

REPO = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--reference-revision', help='also check the files from this local Git revision')
    parser.add_argument('--evaluators', nargs='+', choices=['vm', 'native'], default=['vm', 'native'])
    parser.add_argument('files', nargs='+', type=Path)
    args = parser.parse_args()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    _, hard = resource.getrlimit(resource.RLIMIT_STACK)
    resource.setrlimit(resource.RLIMIT_STACK, (hard, hard))
    if 'COQ_NATIVE_COMPILER_DEFAULT=no' in subprocess.check_output(['coqc', '-config'], text=True):
        parser.error('a native-capable Coq is required')
    sources = {str(p): p.read_text() for p in args.files}
    if args.reference_revision:
        sources = {
            **{args.reference_revision + ':' + str(p): subprocess.check_output(
                ['git', 'show', args.reference_revision + ':' + str(p)], cwd=REPO, text=True)
               for p in args.files},
            **sources,
        }
    metadata = {
        'revision': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=REPO, text=True).strip(),
        'coq': subprocess.check_output(['coqc', '--version'], text=True),
        'sha256': {p: hashlib.sha256(s.encode()).hexdigest() for p, s in sources.items()},
    }
    (output / 'metadata.json').write_text(json.dumps(metadata, indent=2) + '\n')
    for index, (name, source) in enumerate(sources.items()):
        theorems = re.findall(r'(?:Theorem|Lemma)\s+(\w+)', source)
        if not theorems:
            parser.error(f'{name}: no theorem to audit')
        for mode in args.evaluators:
            body = re.sub(r'\bProof\.(.*?)\bQed\.',
                          lambda m: re.sub(r'\b(?:vm|native)_compute\b', mode + '_compute', m[0]),
                          source, flags=re.S)
            path = output / f'Bench_{index}_{Path(name).stem}_{mode}.v'
            path.write_text(body + f'\nPrint Assumptions {theorems[-1]}.\n')
            log = path.with_suffix('.log')
            with log.open('w') as stream:
                subprocess.run([sys.executable, str(REPO / 'tools/time_command.py'),
                                '--log', str(output / 'times.jsonl'), '--phase', name + ':' + mode,
                                '--', 'coqc', '-native-compiler', 'ondemand', '-Q', 'theories', 'BBB4',
                                '-w', '-abstract-large-number', str(path)],
                               cwd=REPO, stdout=stream, stderr=subprocess.STDOUT, check=True)
            audit = log.read_text()
            if 'Axioms:' in audit:
                declarations = [line for line in audit[audit.index('Axioms:'):].splitlines()
                                if line and not line[0].isspace() and not line.startswith('>>>')]
                if declarations != ['Axioms:', 'FunctionalExtensionality.functional_extensionality_dep']:
                    raise RuntimeError(f'unexpected assumptions: see {log}')
            elif 'Closed under the global context' not in audit:
                raise RuntimeError(f'missing assumption audit: see {log}')
            print(f'{name}: {mode} passed ({log})', flush=True)


if __name__ == '__main__':
    main()
