#!/usr/bin/env python3
"""Compare relaxation and SCC-order ranks through the same verified checkers.

Build the current native computation dependencies first, then run with no
competing compilers. Sources are copied to --output; production proof objects
are never overwritten. Both variants use native conversion and the current
checker, so this measures the rank-search change independently of VM/native
speedups. Example:

  python3 tools/censustr/bench_repwl_ranks.py --output work/ranks \
    theories/CensusTr/RWParts/ProvTr_RW_15_P005.v \
    theories/CloseoutTr/CBT_RW_03.v
"""
import argparse
import hashlib
import json
from pathlib import Path
import platform
import re
import resource
import subprocess
import sys
import time

REPO = Path(__file__).resolve().parents[2]


def reference_source():
    header = '''From Coq Require Import Arith Bool List PArith.
From Coq Require Import FSets.FMapPositive MSets.MSetPositive.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape Closure ClosureTr.
From BBB4.Checkers Require Import RepWL.
From BBB4.Census Require Import RepWLSearch.
From BBB4.CensusTr Require Import RepWLTr RepWLMBTr.
Import ListNotations.
'''
    parts = [header]
    for prefix, module, end in [('rw', 'RepWLTr', '(** ** Tier W-wrap:'),
                                ('mb', 'RepWLMBTr', '(** ** The wrapped tier:')]:
        text = (REPO / 'theories/CensusTr' / (module + '.v')).read_text()
        body = text[text.index(f'Definition {prefix}_procedure_tr '):text.index(end)]
        if body.count('iproc_rounds_tr ') != 1:
            raise ValueError(f'expected the SCC-order search in {module}')
        body = body.replace('iproc_rounds_tr ', 'iproc_rounds ')
        body = body.replace(f'{prefix}_procedure_tr', f'{prefix}_procedure_reference')
        body = body.replace(f'{prefix}_tier_tr', f'{prefix}_tier_reference')
        parts.append(body)
    return '\n'.join(parts)


def worker(source, output):
    source, output = Path(source), Path(output)
    _, hard = resource.getrlimit(resource.RLIMIT_STACK)
    resource.setrlimit(resource.RLIMIT_STACK, (hard, hard))
    command = ['coqc', '-native-compiler', 'ondemand', '-w', '-abstract-large-number',
               '-Q', 'theories', 'BBB4', '-Q', str(output), 'RankBench', str(source)]
    before = resource.getrusage(resource.RUSAGE_CHILDREN)
    start = time.monotonic()
    with source.with_suffix('.log').open('w') as log:
        result = subprocess.run(command, cwd=REPO, stdout=log, stderr=subprocess.STDOUT)
    usage = resource.getrusage(resource.RUSAGE_CHILDREN)
    log = source.with_suffix('.log').read_text()
    footprint = log[log.index('Axioms:'):].strip() if 'Axioms:' in log else ''
    declarations = [s for s in footprint.splitlines() if s and not s[0].isspace()]
    audited = declarations == ['Axioms:', 'FunctionalExtensionality.functional_extensionality_dep']
    record = dict(command=command, wall_seconds=time.monotonic() - start,
                  user_seconds=usage.ru_utime - before.ru_utime,
                  system_seconds=usage.ru_stime - before.ru_stime,
                  max_rss_bytes=usage.ru_maxrss * (1 if sys.platform == 'darwin' else 1024),
                  exit_code=result.returncode, expected_assumptions=audited,
                  assumptions=footprint)
    source.with_suffix('.json').write_text(json.dumps(record, indent=2) + '\n')
    return result.returncode or (0 if audited else 1)


def main():
    if len(sys.argv) > 1 and sys.argv[1] == '--worker':
        return worker(*sys.argv[2:])
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path, required=True)
    ap.add_argument('sources', type=Path, nargs='+')
    args = ap.parse_args()
    if 'COQ_NATIVE_COMPILER_DEFAULT=no' in subprocess.check_output(['coqc', '-config'], text=True):
        ap.error('a native-capable Coq is required')
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    if (output / 'metadata.json').exists():
        ap.error('use a new output directory')
    inputs = []
    for path in args.sources:
        path = (REPO / path).resolve()
        text = path.read_text()
        if not re.search(r'\b(?:rw|mb)_tier_tr_sound\b', text):
            ap.error(f'no RepWL searches in {path}')
        if path.stem.startswith('CBT_'):
            theorem = 'cbt_' + path.stem[4:] + '_covers'
        else:
            match = re.fullmatch(r'ProvTr_RW_(\d+)_P(\d+)', path.stem)
            if not match:
                ap.error(f'unsupported proof source: {path}')
            theorem = f'ptw_{match[1]}_p{match[2]}_nqhtr'
        inputs.append((path, text, theorem))
    reference = reference_source()
    metadata = dict(coq=subprocess.check_output(['coqc', '--version'], text=True),
                    platform=platform.platform(),
                    revision=subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=REPO, text=True).strip(),
                    source_sha256={str(p.relative_to(REPO)): hashlib.sha256(s.encode()).hexdigest()
                                   for p, s, _ in inputs},
                    reference_sha256=hashlib.sha256(reference.encode()).hexdigest(),
                    search_sha256=hashlib.sha256((REPO / 'theories/CensusTr/RepWLSearchTr.v').read_bytes()).hexdigest())
    (output / 'metadata.json').write_text(json.dumps(metadata, indent=2) + '\n')
    ref = output / 'RankReference.v'
    ref.write_text(reference)
    _, hard = resource.getrlimit(resource.RLIMIT_STACK)
    resource.setrlimit(resource.RLIMIT_STACK, (hard, hard))
    with (output / 'reference.log').open('w') as log:
        subprocess.run(['coqc', '-native-compiler', 'yes', '-Q', 'theories', 'BBB4',
                        '-Q', str(output), 'RankBench', str(ref)], cwd=REPO,
                       stdout=log, stderr=subprocess.STDOUT, check=True)
    for path, body, theorem in inputs:
        for mode in ['relaxation', 'scc_order']:
            text = body
            if mode == 'relaxation':
                for prefix in ['rw', 'mb']:
                    text = text.replace(f'{prefix}_tier_tr_sound', f'{prefix}_tier_reference_sound')
            source = output / (path.stem + '_' + mode + '.v')
            source.write_text('From RankBench Require Import RankReference.\n' + text +
                              f'\nPrint Assumptions {theorem}.\n')
            subprocess.run([sys.executable, str(Path(__file__).resolve()), '--worker',
                            str(source), str(output)], check=True)
            print(source.with_suffix('.json').read_text(), flush=True)
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
