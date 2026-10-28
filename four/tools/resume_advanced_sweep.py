"""Continue a frozen sweep using the guarded-alarm driver, with explicit lineage.

The previous manifest and completed log prefixes remain immutable. The final
report records both driver versions; imported rows are not attributed to the
new driver. All ordinary advanced_sweep.py arguments are supported, together
with --resume-from DIR for the first continuation.
"""
import hashlib
import json
from pathlib import Path
import subprocess
import sys

import advanced_sweep as base
from pipeline_sweep import digest, encoded, read_rows

ROOT = base.ROOT
DRIVER = ROOT/'build/wave3/driver-v2/probe'


def value(argv, option, default=None):
    positions = [i for i, token in enumerate(argv) if token == option]
    return argv[positions[-1]+1] if positions else default


def replace(argv, option, new):
    out = []
    i = 0
    while i < len(argv):
        if argv[i] == option:
            i += 2
        else:
            out.append(argv[i]); i += 1
    return out+[option, str(new)]


def build_probe(probe):
    DRIVER.parent.mkdir(parents=True, exist_ok=True)
    for command in [
        ['ocamlopt', '-w', '-a', '-I', 'build/advanced', '-c', '-o',
         'build/wave3/driver-v2/advanced_probe_v2.cmx', 'tools/advanced_probe_v2.ml'],
        ['ocamlopt', '-w', '-a', '-I', 'build/advanced', 'unix.cmxa',
         'build/advanced/checkers.cmx', 'build/wave3/driver-v2/advanced_probe_v2.cmx',
         '-o', str(probe.resolve())],
    ]:
        subprocess.run(command, cwd=ROOT, check=True)


def main():
    argv = sys.argv[1:]
    origin_arg = value(argv, '--resume-from')
    if origin_arg:
        index = argv.index('--resume-from'); del argv[index:index+2]
    output_arg = value(argv, '--output-dir')
    report_arg = value(argv, '--report')
    if not output_arg or not report_arg:
        raise ValueError('Explicit --output-dir and --report are required')
    output = Path(output_arg)
    report_path = Path(report_arg)
    output.mkdir(parents=True, exist_ok=True)
    metadata_path = output/'prefix-provenance.json'
    if origin_arg and not metadata_path.exists():
        if (output/'manifest.json').exists():
            raise ValueError('Cannot import prefixes into an existing unrelated run')
        origin = Path(origin_arg)
        old_raw = (origin/'manifest.json').read_bytes()
        old = json.loads(old_raw)
        inp = Path(value(argv, '--input', str(ROOT/'build/pipeline/low-budget/not-accepted.txt')))
        stages = Path(value(argv, '--stages', str(ROOT/'research/advanced-stages.json')))
        prior = Path(value(argv, '--prior-report', str(ROOT/'research/pipeline-low-budget.json')))
        rows = sorted(read_rows(inp), key=lambda m: hashlib.sha256(m.encode()).digest())
        sample = int(value(argv, '--sample', '128'))
        if sample:
            rows = rows[:sample]
        expected = {
            'input_sha256': digest(inp), 'prior_report_sha256': digest(prior),
            'selected_sha256': hashlib.sha256(encoded(rows).encode()).hexdigest(),
            'bound': int(value(argv, '--bound', '4096')),
            'workers': int(value(argv, '--workers', '2')),
            'timeout_seconds_per_stage_row': float(value(argv, '--timeout', '0.25')),
            'stages': json.loads(stages.read_text()),
            'extraction_sha256': digest(ROOT/'build/advanced/checkers.ml'),
        }
        for key, wanted in expected.items():
            if old.get(key) != wanted:
                raise ValueError(f'Continuation parameter mismatch: {key}')
        prefixes = []
        for source in sorted(origin.glob('stage-??-worker-??.tsv')):
            raw = source.read_bytes()
            raw = raw[:raw.rfind(b'\n')+1]
            target = output/source.name
            if target.exists():
                raise ValueError(f'Refusing to overwrite an existing log: {target}')
            target.write_bytes(raw)
            prefixes.append({'file': source.name, 'bytes': len(raw),
                             'rows': len(raw.splitlines()),
                             'sha256': hashlib.sha256(raw).hexdigest()})
        metadata = {'status': 'Completed search rows imported from an earlier driver; not proof claims.',
                    'source_manifest_sha256': hashlib.sha256(old_raw).hexdigest(),
                    'source_manifest': old, 'prefixes': prefixes}
        metadata_path.write_text(json.dumps(metadata, indent=2, sort_keys=True)+'\n')
    if not metadata_path.exists():
        if '--check' in argv:
            raise ValueError('No saved provenance for checking')
        metadata_path.write_text(json.dumps({'prefixes': []}, indent=2)+'\n')
    metadata = json.loads(metadata_path.read_text())
    for prefix in metadata['prefixes']:
        with (output/prefix['file']).open('rb') as source:
            raw = source.read(prefix['bytes'])
        if hashlib.sha256(raw).hexdigest() != prefix['sha256']:
            raise ValueError(f'Imported log prefix changed: {prefix["file"]}')
    original_hashes = base.source_hashes
    base.source_hashes = lambda: {
        **original_hashes(),
        'tools/advanced_probe_v2.ml': digest(ROOT/'tools/advanced_probe_v2.ml'),
        'tools/resume_advanced_sweep.py': digest(Path(__file__)),
        'continuation/prefix-provenance.json': digest(metadata_path),
    }
    base.build_probe = build_probe
    internal_report = output/'run.json'
    sys.argv = [sys.argv[0]]+replace(replace(argv, '--probe', DRIVER), '--report', internal_report)
    base.main()
    report = json.loads(internal_report.read_text())
    report['execution_provenance'] = metadata
    report['status'] += ' Imported completed prefixes retain their original driver provenance.'
    contents = json.dumps(report, indent=2, sort_keys=True)+'\n'
    if '--check' in argv:
        if report_path.read_text() != contents:
            raise ValueError('Final continuation report differs')
    else:
        report_path.parent.mkdir(parents=True, exist_ok=True)
        report_path.write_text(contents)


if __name__ == '__main__':
    main()
