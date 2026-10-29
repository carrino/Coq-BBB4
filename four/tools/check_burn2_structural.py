"""Replay the expanded-source conjugacy batch from compact tracked inputs.

Rebuild only the 64 source certificates actually used by the 67 transports,
then check prefix intersections, all-completion bounds, original pending
membership and exact target inventory. No old generated source board is needed.
Published inputs/reports stay immutable; current object/audit receipts live in
the ignored output directory. Discovery hashes are never proof evidence.
"""
import argparse
import base64
import hashlib
import json
from pathlib import Path
import resource
import subprocess
import sys
import time
import zlib

import check_closure_wave as closure
import check_conjugate_batch as conjugate
from check_campaign import inventory_source
from generate_pipeline_examples import codes
from kernel_audit_cache_v3 import audit, fresh_paths
from weighted_codec_v2 import bundle_decode
import check_weighted_portfolio as portfolio

ROOT = Path(__file__).resolve().parents[1]
INPUT = ROOT / 'research/burn2-structural-input.json'
REPORT = ROOT / 'research/burn2-structural-checked.json'
BUILD = ROOT / 'build/burn2-structural/proof'
NS = 'BBB24Burn2Structural'


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def serialized(data):
    return json.dumps(data, indent=2, sort_keys=True) + '\n'


def immutable(path, text):
    if path.exists() and path.read_text() != text:
        raise ValueError('Refuse to replace frozen artifact: ' + str(path))
    if not path.exists():
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)


def read_bundle(path):
    data = json.loads(path.read_text())
    if data.get('encoding') == 'zlib-base64':
        raw = zlib.decompress(base64.b64decode(data['data'], validate=True))
        if hashlib.sha256(raw).hexdigest() != data['uncompressed_sha256']:
            raise ValueError('Compressed source hash differs')
        data = json.loads(raw)
    return data


def selection(data):
    if data['source_bound'] != 4096 or data['output_bound'] != 8192:
        raise ValueError('Unexpected source/output bound')
    for name, expected in data['pins'].items():
        path = (ROOT/name).resolve()
        if not path.is_relative_to(ROOT) or sha(path) != expected:
            raise ValueError('Frozen source input differs: ' + name)
    ordinary = []
    for spec in data['ordinary_sources']:
        if spec['path'] not in data['pins']:
            raise ValueError('Unpinned ordinary source')
        source = read_bundle(ROOT/spec['path'])
        if source['columns'] != closure.FIELDS:
            raise ValueError('Unexpected ordinary source columns')
        rows = [dict(zip(source['columns'], r)) for r in source['rows']]
        if len(rows) != len({r['machine'] for r in rows}):
            raise ValueError('Duplicate source machine')
        pool = {r['machine']: r for r in rows}
        for machine in spec['machines']:
            row = pool[machine]
            closure.validate_row(row)
            if row['bound'] != 4096:
                raise ValueError('Ordinary source bound differs')
            ordinary.append(row)
    registry_path = data['weighted_registry']
    if registry_path not in data['pins']:
        raise ValueError('Unpinned weighted registry')
    registry = json.loads((ROOT/registry_path).read_text())
    weighted_pool = {}
    for spec in registry['bundles']:
        if data['pins'].get(spec['path']) != spec['sha256']:
            raise ValueError('Unpinned weighted bundle')
        rows = bundle_decode((ROOT/spec['path']).read_text())
        if len(rows) != spec['rows']:
            raise ValueError('Weighted source count differs')
        for row in rows:
            if row['machine'] in weighted_pool:
                raise ValueError('Duplicate weighted source')
            weighted_pool[row['machine']] = row
    weighted = [weighted_pool[m] for m in data['weighted_sources']]
    machines = [r['machine'] for r in ordinary+weighted]
    if len(machines) != len(set(machines)):
        raise ValueError('Repeated selected source')
    conjugate.validate(data, machines, data)
    return ordinary, weighted, machines


def source_spec(name, weighted=False):
    return dict(module=NS+'.'+name, board='board', bound=4096,
                nonhalt='board_nonhalt' if weighted else 'nonhalt',
                small_sound='board_small_sound' if weighted else 'small_sound')


def generate(data, output):
    ordinary, weighted, machines = selection(data)
    output.mkdir(parents=True, exist_ok=True)
    source_paths, specs = [], []
    for offset in range(0, len(ordinary), 8):
        name = f'OrdinarySources{offset//8:03d}'
        path = output/(name+'.v')
        immutable(path, closure.shard_source(ordinary[offset:offset+8]))
        source_paths.append(path)
        specs.append(source_spec(name))
    engine = portfolio.configure()
    path = output/'WeightedSources.v'
    immutable(path, engine.shard_source(weighted))
    source_paths.append(path)
    specs.append(source_spec('WeightedSources', True))
    config = dict(source_bound=4096, output_bound=8192, sources=specs)
    # The frozen renderer has a write interface; generate in a private staging
    # directory, then require exact equality with any already generated source.
    import tempfile
    with tempfile.TemporaryDirectory(dir=output, prefix='generate-') as staging:
        generated = conjugate.generate(config, machines, data['rows'], Path(staging), NS)
        for p in generated:
            target = output/p.name
            immutable(target, p.read_text())
            source_paths.append(target)
    inventory = dict(path=str(INPUT.relative_to(ROOT)), format='columns', order='input')
    original = dict(id='Burn2Structural', scope='both', rows=len(data['rows']),
                    module=NS+'.ConjugateAll', board='board', sound='sound',
                    small_sound='small_sound', was_pending='was_pending',
                    instruction_bound=8192, state_bound=8192,
                    inventories=[inventory], machines=[r[0] for r in data['rows']])
    path = output/'Inventory.v'
    immutable(path, inventory_source(original))
    source_paths.append(path)
    descriptor = {k: v for k, v in original.items() if k != 'machines'}
    descriptor.update(module=NS+'.Inventory',
                      load_paths=[dict(path=str(BUILD.relative_to(ROOT)), namespace=NS)])
    return source_paths, descriptor


def helper_hashes():
    paths = {Path(__file__).resolve()}
    for module in sys.modules.values():
        path = getattr(module, '__file__', None)
        if path and Path(path).resolve().is_relative_to(ROOT/'tools'):
            paths.add(Path(path).resolve())
    return {str(p.relative_to(ROOT)): sha(p) for p in sorted(paths)}


def limits():
    resource.setrlimit(resource.RLIMIT_AS, (3*1024**3, 3*1024**3))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', type=Path, default=BUILD)
    parser.add_argument('--timeout', type=int, default=600)
    parser.add_argument('--audit-timeout', type=int, default=1800)
    parser.add_argument('--resume', action='store_true')
    parser.add_argument('--generate-only', action='store_true')
    args = parser.parse_args()
    output = args.output_dir.resolve()
    if not output.is_relative_to(ROOT/'build'):
        raise ValueError('Output must be under ignored four/build')
    data = json.loads(INPUT.read_text())
    paths, descriptor = generate(data, output)
    helpers = helper_hashes()
    core = {str(p.relative_to(ROOT)): sha(p) for p in sorted((ROOT/'theories').rglob('*.v'))}
    evidence = dict(input_sha256=sha(INPUT), source_inputs_sha256=data['pins'],
                    helper_sha256=helpers, core_source_sha256=core,
                    generated_source_sha256={p.name: sha(p) for p in paths},
                    descriptor=descriptor, checked_targets=len(data['rows']),
                    source_certificate_count=sum(len(s['machines']) for s in data['ordinary_sources'])+len(data['weighted_sources']),
                    state_bound=8192, instruction_bound=8192)
    if REPORT.exists():
        previous = json.loads(REPORT.read_text())
        if previous['evidence'] != evidence:
            raise ValueError('Frozen report evidence differs')
    if args.generate_only:
        print(json.dumps(dict(generated_modules=len(paths), targets=len(data['rows']))))
        return
    loadpaths = [(ROOT/'theories', 'BBB24'), (output, NS)]
    flags = [arg for p, n in loadpaths for arg in ('-Q', str(p), n)]
    core_objects = {str(p.relative_to(ROOT)): sha(p) for p in sorted((ROOT/'theories').rglob('*.vo'))}
    runtime = subprocess.check_output(['coqc', '--version'], text=True)
    compilation = []
    for path in paths:
        proof_input = dict(source_sha256=sha(path), core_object_sha256=core_objects,
                           predecessor_object_sha256={p.name: sha(p.with_suffix('.vo')) for p in paths[:paths.index(path)]},
                           coq_version=runtime)
        receipt = path.with_suffix('.compiled.json')
        cached = args.resume and receipt.exists() and path.with_suffix('.vo').exists()
        if cached:
            cached = json.loads(receipt.read_text()) == {**proof_input, 'object_sha256':sha(path.with_suffix('.vo'))}
        started = time.monotonic()
        if not cached:
            with path.with_suffix('.log').open('w') as log:
                subprocess.run(['coqc', '-noglob', '-w', '-abstract-large-number', '-native-compiler', 'no', *flags, str(path)],
                               stdout=log, stderr=subprocess.STDOUT, timeout=args.timeout,
                               check=True, preexec_fn=limits)
            receipt.write_text(serialized({**proof_input, 'object_sha256':sha(path.with_suffix('.vo'))}))
        compilation.append(dict(module=path.stem, cached=cached, seconds=round(time.monotonic()-started,3)))
        print(json.dumps(compilation[-1]), flush=True)
    receipt, log = fresh_paths(output, 'kernel-audit')
    checked = audit([NS+'.Inventory'], [paths[-1]], loadpaths, receipt, log,
                    recursive=True, timeout=args.audit_timeout)
    if sha(INPUT) != evidence['input_sha256'] or helper_hashes() != helpers:
        raise ValueError('Input or helper changed during checking')
    for name, expected in {**data['pins'], **core}.items():
        if sha(ROOT/name) != expected:
            raise ValueError('Frozen source changed during checking: '+name)
    for path in paths:
        if sha(path) != evidence['generated_source_sha256'][path.name]:
            raise ValueError('Generated proof source changed during checking')
    runtime_report = dict(evidence=evidence, status='recursively kernel audited',
                          compilation=compilation,
                          kernel_receipt=str(receipt.relative_to(ROOT)), kernel_receipt_sha256=sha(receipt),
                          kernel_modules=len(checked['snapshot']['graph']),
                          kernel_seconds=checked['elapsed_seconds'],
                          actual_object_sha256={p.with_suffix('.vo').name:sha(p.with_suffix('.vo')) for p in paths})
    (output/'runtime.json').write_text(serialized(runtime_report))
    if not REPORT.exists():
        immutable(REPORT, serialized(runtime_report))
    print(json.dumps(dict(checked_targets=len(data['rows']), source_certificates=evidence['source_certificate_count'],
                          audit_modules=runtime_report['kernel_modules'], descriptor=descriptor)), flush=True)


if __name__ == '__main__':
    main()
