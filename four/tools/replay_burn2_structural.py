"""Portably replay the frozen structural batch without changing its evidence.

The original checker pinned all core sources present when its first proof was
recorded. Validate exactly those pins: later unrelated core files do not alter
that historical dependency snapshot. Regenerate the exact recorded sources,
compile current objects and recursively audit them. Historical object hashes
are never substituted for a current audit.
"""
import argparse
import json
from pathlib import Path
import subprocess
import time

import check_burn2_structural as frozen
from kernel_audit_cache_v3 import audit, fresh_paths

ROOT, NS = frozen.ROOT, frozen.NS


def verify_pins(evidence, report_hash, adapter_hash):
    if frozen.sha(frozen.REPORT) != report_hash or frozen.sha(__file__) != adapter_hash:
        raise ValueError('Published report or adapter changed during replay')
    if frozen.sha(frozen.INPUT) != evidence['input_sha256']:
        raise ValueError('Frozen structural input changed')
    for group in ('source_inputs_sha256', 'helper_sha256', 'core_source_sha256'):
        for name, expected in evidence[group].items():
            path = (ROOT/name).resolve()
            if not path.is_relative_to(ROOT) or frozen.sha(path) != expected:
                raise ValueError('Frozen artifact differs: ' + name)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', type=Path, default=frozen.BUILD)
    parser.add_argument('--timeout', type=int, default=600)
    parser.add_argument('--audit-timeout', type=int, default=1800)
    parser.add_argument('--resume', action='store_true')
    parser.add_argument('--generate-only', action='store_true')
    args = parser.parse_args()
    if args.timeout < 1 or args.audit_timeout < 1:
        raise ValueError('Timeouts must be positive')
    output = args.output_dir.resolve()
    if not output.is_relative_to(ROOT/'build'):
        raise ValueError('Output must be under ignored four/build')
    report_hash, adapter_hash = frozen.sha(frozen.REPORT), frozen.sha(__file__)
    report = json.loads(frozen.REPORT.read_text())
    evidence = report['evidence']
    verify_pins(evidence, report_hash, adapter_hash)
    data = json.loads(frozen.INPUT.read_text())
    paths, descriptor = frozen.generate(data, output)
    if descriptor != evidence['descriptor']:
        raise ValueError('Regenerated board descriptor differs')
    if {p.name: frozen.sha(p) for p in paths} != evidence['generated_source_sha256']:
        raise ValueError('Regenerated proof sources differ')
    source_count = sum(len(s['machines']) for s in data['ordinary_sources']) + len(data['weighted_sources'])
    if source_count != evidence['source_certificate_count'] or len(data['rows']) != evidence['checked_targets']:
        raise ValueError('Frozen source/target inventory differs')
    verify_pins(evidence, report_hash, adapter_hash)
    if args.generate_only:
        print(json.dumps(dict(generated_modules=len(paths), targets=len(data['rows']),
                              published_report_unchanged=True)))
        return
    loadpaths = [(ROOT/'theories', 'BBB24'), (output, NS)]
    flags = [arg for path, namespace in loadpaths for arg in ('-Q', str(path), namespace)]
    core_objects = {str(Path(name).with_suffix('.vo')): frozen.sha((ROOT/name).with_suffix('.vo'))
                    for name in evidence['core_source_sha256']}
    runtime = subprocess.check_output(['coqc', '--version'], text=True)
    compilation = []
    started = time.monotonic()
    for i, path in enumerate(paths):
        proof_input = dict(source_sha256=frozen.sha(path), core_object_sha256=core_objects,
                           predecessor_object_sha256={p.name: frozen.sha(p.with_suffix('.vo')) for p in paths[:i]},
                           coq_version=runtime)
        receipt = path.with_suffix('.compiled.json')
        cached = args.resume and receipt.exists() and path.with_suffix('.vo').exists()
        if cached:
            cached = json.loads(receipt.read_text()) == {**proof_input, 'object_sha256':frozen.sha(path.with_suffix('.vo'))}
        before = time.monotonic()
        if not cached:
            with path.with_suffix('.replay.log').open('w') as log:
                subprocess.run(['coqc', '-noglob', '-w', '-abstract-large-number', '-native-compiler', 'no',
                                *flags, str(path)], stdout=log, stderr=subprocess.STDOUT,
                               timeout=args.timeout, check=True, preexec_fn=frozen.limits)
            receipt.write_text(frozen.serialized({**proof_input, 'object_sha256':frozen.sha(path.with_suffix('.vo'))}))
        compilation.append(dict(module=path.stem, cached=cached, seconds=round(time.monotonic()-before,3)))
        print(json.dumps(compilation[-1]), flush=True)
    receipt, log = fresh_paths(output, 'portable-kernel-audit')
    checked = audit([NS+'.Inventory'], [paths[-1]], loadpaths, receipt, log,
                    recursive=True, timeout=args.audit_timeout)
    verify_pins(evidence, report_hash, adapter_hash)
    if {p.name:frozen.sha(p) for p in paths} != evidence['generated_source_sha256']:
        raise ValueError('Generated proof source changed during audit')
    actual_objects = {p.with_suffix('.vo').name:frozen.sha(p.with_suffix('.vo')) for p in paths}
    result = dict(status='Exact recorded sources compiled and recursively kernel audited.',
                  frozen_report_sha256=report_hash, adapter_sha256=adapter_hash,
                  published_report_unchanged=True, checked_targets=len(data['rows']),
                  source_certificate_count=source_count, generated_modules=len(paths),
                  compilation=compilation, current_object_sha256=actual_objects,
                  historical_object_sha256=report['actual_object_sha256'],
                  kernel_receipt=str(receipt.relative_to(ROOT)), kernel_receipt_sha256=frozen.sha(receipt),
                  kernel_modules=len(checked['snapshot']['graph']), kernel_seconds=checked['elapsed_seconds'],
                  seconds=round(time.monotonic()-started,3))
    (output/'portable-replay.json').write_text(frozen.serialized(result))
    print(json.dumps({k:result[k] for k in ('status','checked_targets','kernel_modules','published_report_unchanged','seconds')}),flush=True)


if __name__ == '__main__':
    main()
