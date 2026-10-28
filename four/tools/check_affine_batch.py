"""Reproduce the checked outcomes of the frozen 786-candidate affine sample.

The compact input bundle contains untrusted search certificates. Generated Coq
shards stay under build/. Every accepted row receives a non-halting theorem and
both 4096 bounds for all completions; rejected rows prove that this particular
checker invocation returns false. Existing census links are preserved; this
batch does not itself discharge any additional census obligations.

Run `make -C four` first, then this script with Coq on PATH. `--refresh` discovers
the checker outcomes and replaces the report only after compilation and coqchk.
The default verifies the recorded outcomes and hashes, then checks the proofs.
"""
import argparse
import csv
import hashlib
import json
import re
import subprocess
import time
from collections import Counter
from pathlib import Path

import generate_affine as generator

ROOT = Path(__file__).resolve().parents[1]
BUNDLE = ROOT / 'research/affine-batch-certs.json'
REPORT = ROOT / 'research/affine-batch-summary.json'
LEDGER = ROOT / 'research/affine-batch.tsv'
BUILD = ROOT / 'build/affine-batch'
SHARD_SIZE = 32
CFUEL, FUEL = 4096, 8192


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def source_hashes():
    paths = [Path(__file__).resolve(), ROOT / 'tools/generate_affine.py',
             ROOT.parent / 'tools/gen_irulesblkpfx_certs.py']
    # Pin every checked source, not just the wrapper around the affine engine.
    paths += sorted((ROOT / 'theories').rglob('*.v'))
    # Unrelated new checker ports must not invalidate this isolated batch.
    used = {'Statement', 'StatementTr', 'Spec', 'CTape', 'Instructions', 'Bounds',
            'Labels', 'Census', 'CycleCensus', 'GTape', 'Mirror', 'IRuleCensus'}
    paths = [p for p in paths if p.suffix != '.v' or p.stem in used
             or 'IRules' in p.parts or p.name in ('Cycle.v', 'TCycler.v')]
    paths += [ROOT/'research/burndown-verified.json']
    registry = json.loads(paths[-1].read_text())
    proof_source = ROOT / registry['proof_source']
    if sha(proof_source) != registry['proof_source_sha256']:
        raise ValueError(f'Original proof source hash changed: {proof_source}')
    paths.extend([proof_source, ROOT/'theories/Bootstrap.v'])
    for relative, expected in registry.get('census_closeout', {}).get('source_sha256', {}).items():
        path = ROOT / relative
        if sha(path) != expected:
            raise ValueError(f'Census closeout source hash changed: {path}')
        paths.append(path)
    return {str(p.relative_to(ROOT.parent)): sha(p) for p in paths}


def load_inputs():
    bundle = json.loads(BUNDLE.read_text())
    with (ROOT / 'research/burndown-sample.tsv').open() as f:
        baseline = list(csv.DictReader(f, delimiter='\t'))
    candidates = {r['machine'] for r in baseline
                  if r['status'] in ('coq_checked', 'candidate_unchecked')}
    if len(candidates) != 786 or set(bundle) != candidates:
        raise ValueError('Certificate bundle must exactly match 786 baseline candidates')
    cert_dir = BUILD / 'certs'
    cert_dir.mkdir(parents=True, exist_ok=True)
    paths = []
    for machine, contents in sorted(bundle.items()):
        if not re.fullmatch(r'[0-3LRAB_\-]{25}', machine):
            raise ValueError(f'Invalid machine identifier: {machine}')
        path = cert_dir / f'{machine}.cert'
        path.write_text(contents)
        cert = generator.shared.parse_cert(path)
        if cert.get('machine') != machine or cert.get('type') != 'irules':
            raise ValueError(f'Certificate identity/type mismatch: {machine}')
        # The shared parser intentionally ignores claims; reject unsupported
        # multivariable syntax rather than silently dropping its equations.
        if any(line.split()[0] in {'nvar', 'mmrow', 'xmin', 'x0', 'tplrunmv'}
               for line in contents.splitlines() if line.split()):
            raise ValueError(f'Multivariable certificate unsupported: {machine}')
        paths.append(path)
    return paths


def checker_term(path):
    name = generator.shared.cname(path.stem)
    return f'ir_check 4096%N 4096%N tm_{name} cert_{name} {CFUEL} {FUEL}'


def certificate(path):
    return generator.emit(path).replace('200000 300000', f'{CFUEL} {FUEL}')


def definitions(path):
    return certificate(path).split('Lemma checked_', 1)[0]


def command(args, log, timeout):
    start = time.monotonic()
    with log.open('w') as f:
        subprocess.run(args, cwd=ROOT.parent, stdout=f, stderr=subprocess.STDOUT,
                       check=True, timeout=timeout)
    return time.monotonic() - start


def coqc(path, timeout):
    return command(['coqc', '-w', '-abstract-large-number', '-native-compiler', 'no',
                    '-Q', str(ROOT/'theories'), 'BBB24', '-Q', str(BUILD), 'BBB24Batch',
                    str(path)], path.with_suffix('.log'), timeout)


def discover(paths, timeout):
    outcomes = []
    for index in range(0, len(paths), SHARD_SIZE):
        chunk = paths[index:index+SHARD_SIZE]
        output = BUILD / f'Probe{index//SHARD_SIZE:03}.v'
        output.write_text(generator.HEADER + ''.join(definitions(p) for p in chunk)
                          + '\nEval vm_compute in ['
                          + ';\n'.join(checker_term(p) for p in chunk) + '].\n')
        coqc(output, timeout)
        text = output.with_suffix('.log').read_text()
        if not re.fullmatch(r'\s*=\s*\[(?:true|false|[;\s])*\]\s*: list bool\s*', text):
            raise ValueError(f'Unexpected Coq probe output: {output}')
        flags = re.findall(r'\b(true|false)\b', text)
        if len(flags) != len(chunk):
            raise ValueError(f'Wrong number of Coq outcomes: {output}')
        outcomes.extend(flag == 'true' for flag in flags)
        print(f'Probed {len(outcomes)}/{len(paths)}', flush=True)
    return outcomes


def make_shards(paths, outcomes):
    shards = []
    rows = []
    registry = json.loads((ROOT/'research/burndown-verified.json').read_text())
    linked = set(registry.get('census_closeout', {}).get('machines', []))
    if not linked <= set(registry['machines']):
        raise ValueError('Existing census links must refer to registered checked families')
    for index in range(0, len(paths), SHARD_SIZE):
        module = f'AffineBatch{index//SHARD_SIZE:03}'
        output = BUILD / f'{module}.v'
        pieces = [generator.HEADER]
        for p, accepted in zip(paths[index:index+SHARD_SIZE], outcomes[index:index+SHARD_SIZE]):
            name = generator.shared.cname(p.stem)
            if accepted:
                pieces.append(certificate(p))
                theorem = f'BBB24Batch.{module}.completions_{name}'
            else:
                pieces.append(definitions(p) + f'\nLemma rejected_{name} :\n  '
                              + checker_term(p) + ' = false.\n'
                              + 'Proof. vm_compute. reflexivity. Qed.\n')
                theorem = f'BBB24Batch.{module}.rejected_{name}'
            rows.append({'machine': p.stem,
                         'status': 'coq_checked' if accepted else 'checker_rejected',
                         'certificate_sha256': sha(p), 'theorem': theorem,
                         'state_bound': 4096 if accepted else '',
                         'instruction_bound': 4096 if accepted else '',
                         'census_linked': 'yes' if p.stem in linked else 'no'})
        output.write_text(''.join(pieces))
        shards.append(output)
    return shards, rows


def summarize(shards, rows):
    version = subprocess.check_output(['coqc', '--version'], text=True).splitlines()[0]
    old = set(json.loads((ROOT/'research/burndown-verified.json').read_text())['machines'])
    accepted = {r['machine'] for r in rows if r['status'] == 'coq_checked'}
    if not old <= accepted:
        raise ValueError('A previously checked example no longer passes')
    report = {
        'scope': '786 baseline sample candidates only; no additional census obligations discharged',
        'coq_version': version,
        'sample_sha256': json.loads((ROOT/'research/triage-256.json').read_text())['sample_sha256'],
        'bundle_sha256': sha(BUNDLE),
        'parameters': {'state_bound': 4096, 'instruction_bound': 4096,
                       'cfuel': CFUEL, 'fuel': FUEL, 'shard_size': SHARD_SIZE},
        'counts': dict(sorted(Counter(r['status'] for r in rows).items())),
        'previously_checked': len(old), 'new_checked': len(accepted - old),
        'census_linked': sum(r['census_linked'] == 'yes' for r in rows),
        'new_census_linked': 0,
        'validation': 'coqc vm_compute proofs plus recursive coqchk; generated .v files are ignored',
        'source_sha256': source_hashes(),
        'shard_sha256': {p.name: sha(p) for p in shards},
    }
    return report


def verify(paths, outcomes, timeout):
    shards, rows = make_shards(paths, outcomes)
    elapsed = 0
    for shard in shards:
        elapsed += coqc(shard, timeout)
        print(f'Checked {shard.stem}', flush=True)
    elapsed += command(['coqchk', '-silent', '-bytecode-compiler', 'yes',
                        '-Q', str(ROOT/'theories'), 'BBB24', '-Q', str(BUILD), 'BBB24Batch',
                        'BBB24.AffineCloseout', *[f'BBB24Batch.{p.stem}' for p in shards]],
                       BUILD/'coqchk.log', timeout * len(shards))
    return summarize(shards, rows), rows, elapsed


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--refresh', action='store_true')
    parser.add_argument('--timeout', type=int, default=300, help='Seconds per proof shard')
    args = parser.parse_args()
    paths = load_inputs()
    if args.refresh:
        outcomes = discover(paths, args.timeout)
    else:
        expected = json.loads(REPORT.read_text())
        if expected['bundle_sha256'] != sha(BUNDLE) or expected['source_sha256'] != source_hashes():
            raise ValueError('Input/proof source hashes changed; use --refresh to recheck')
        with LEDGER.open() as f:
            old_rows = list(csv.DictReader(f, delimiter='\t'))
        if [r['machine'] for r in old_rows] != [p.stem for p in paths]:
            raise ValueError('Ledger must list each input once in sorted order')
        if any(r['status'] not in {'coq_checked', 'checker_rejected'} for r in old_rows):
            raise ValueError('Invalid recorded checker outcome')
        outcomes = [r['status'] == 'coq_checked' for r in old_rows]
    report, rows, elapsed = verify(paths, outcomes, args.timeout)
    serialized = json.dumps(report, indent=2) + '\n'
    import io
    buffer = io.StringIO(newline='')
    writer = csv.DictWriter(buffer, fieldnames=list(rows[0]), delimiter='\t', lineterminator='\n')
    writer.writeheader(); writer.writerows(rows)
    if args.refresh:
        REPORT.write_text(serialized)
        LEDGER.write_text(buffer.getvalue())
    elif REPORT.read_text() != serialized or LEDGER.read_text() != buffer.getvalue():
        raise ValueError('Recorded affine batch evidence differs from checked outputs')
    print(json.dumps({'counts': report['counts'], 'new_checked': report['new_checked'],
                      'checking_seconds': round(elapsed, 2),
                      'census_linked': report['census_linked'], 'new_census_linked': 0}))


if __name__ == '__main__':
    main()
