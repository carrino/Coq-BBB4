#!/usr/bin/env python3
"""Validate the frozen desktop scan and prepare untrusted Coq replay inputs.

No archive paths are extracted. Canonical scan rows are mapped back to the
original partial tables; Coq will replay those tables from the blank tape.
This tool earns no proof credit and does not establish census coverage.
"""
import argparse
from collections import Counter
import csv
import hashlib
import io
import itertools
import json
from pathlib import Path, PurePosixPath
import tarfile

from replay_observations import json_object, load_input
from scan_candidates import canonical

ROOT = Path(__file__).resolve().parents[1]
ARCHIVE_SHA256 = '8c0ddcb7c3bbc3a1a7efdf8e505a21f9e61410958a29eabf5930a743fb292c4d'
CUTOFF = 32779478
UPPER_WIDTH = 454402378
FAST_WIDTH = 65536


def digest(data):
    return hashlib.sha256(data).hexdigest()


def require(condition, message):
    if not condition:
        raise ValueError(message)


def read_archive(path):
    require(digest(path.read_bytes()) == ARCHIVE_SHA256, 'unexpected frozen archive hash')
    files, total = {}, 0
    with tarfile.open(path, 'r:gz') as archive:
        names = set()
        for member in archive:
            name = PurePosixPath(member.name)
            require(not name.is_absolute() and '..' not in name.parts and
                    member.name not in names, 'unsafe or repeated archive path')
            names.add(member.name)
            require(member.isfile() or member.isdir(), 'unsupported archive member')
            if member.isdir():
                continue
            total += member.size
            require(total <= 128 * 1024**2, 'archive exceeds size limit')
            require(len(name.parts) == 2 and name.parts[0] == 'instruction-scan-01',
                    'unexpected archive layout')
            files[name.name] = archive.extractfile(member).read()
    expected = {'manifest.json', 'summary.json', 'results.jsonl'} | {
        f'worker-{i:02}.jsonl' for i in range(8)}
    require(set(files) == expected, 'missing or extra archive files')
    return files


def parse_json(data):
    return json.loads(data, object_pairs_hook=json_object)


def transform(machine, perm, mirror):
    cells = [row[i:i+3] for row in machine.split('_') for i in (0, 3)]
    result = ['---'] * 8
    for q in range(4):
        for a in range(2):
            tr = cells[2*q+a]
            if tr != '---':
                direction = {'L': 'R', 'R': 'L'}[tr[1]] if mirror else tr[1]
                tr = tr[0] + direction + chr(65 + perm[ord(tr[2])-65])
            result[2*perm[q]+a] = tr
    return '_'.join(result[2*q] + result[2*q+1] for q in range(4))


def original_visits(original, row):
    for rest in itertools.permutations(range(1, 4)):
        perm = (0,) + rest
        for mirror in (False, True):
            if transform(original, perm, mirror) == row['machine']:
                return [row['instruction_first'][2*perm[q]+a]
                        for q in range(4) for a in range(2)]
    raise ValueError('canonical alias is not a start-preserving symmetry')


def nomination(original, row):
    """Derive a total state invariant, adding one step to reach that set.

    The C scanner skips undefined transitions in its closure test. Reject such
    nominations here: its status alone is insufficient for completion proofs.
    The Coq checker independently verifies all observations and closedness.
    """
    visits = original_visits(original, row)
    seen = [t is not None for t in visits]
    cells = [r[i:i+3] for r in original.split('_') for i in (0, 3)]
    tail = [seen[2*q] and seen[2*q+1] for q in range(4)]
    for k, observed in enumerate(seen):
        if observed:
            require(cells[k] != '---', 'observed undefined slot cannot establish a total tail')
            require(tail[ord(cells[k][2])-65], 'observed transition leaves the tail set')
    require(any(tail), 'empty tail set')
    width = row['instruction_control_closed_at'] - CUTOFF + 1
    require(0 <= width <= UPPER_WIDTH, 'nomination exceeds the proposed global width')
    # The all-eight branch does not need an invariant. Otherwise every slot in
    # the invariant is seen and defined, and all its successors stay inside it.
    mask = 0 if all(seen) else sum(1 << q for q in range(4) if tail[q])
    return width, mask


def tsv(rows, fields):
    out = io.StringIO(newline='')
    writer = csv.DictWriter(out, fieldnames=fields, delimiter='\t', lineterminator='\n')
    writer.writeheader()
    writer.writerows(rows)
    return out.getvalue().encode()


def prepare(archive_path, output):
    files = read_archive(archive_path)
    manifest, summary = (parse_json(files[n]) for n in ('manifest.json', 'summary.json'))
    rows = [parse_json(line) for line in files['results.jsonl'].splitlines()]
    workers = [parse_json(line) for i in range(8)
               for line in files[f'worker-{i:02}.jsonl'].splitlines()]
    require(sorted(workers, key=lambda r: r['machine']) == rows, 'worker/results mismatch')
    require(manifest['mode'] == 'instruction' and manifest['start'] == CUTOFF and
            manifest['cap'] == 500000000 and manifest['proof_credit'] == 0,
            'unexpected scan configuration')
    require(manifest['scanner_source_sha256'] == digest((ROOT/'tools/scan.cpp').read_bytes()) and
            manifest['driver_sha256'] == digest((ROOT/'tools/scan_candidates.py').read_bytes()),
            'scanner source identity mismatch')
    _, source, bound = load_input(ROOT/'research/observation-weekend.json')
    require(len(manifest['sources']) == 1 and
            manifest['sources'][0]['sha256'] == bound['input']['sha256'], 'source identity mismatch')
    aliases = {}
    for entry in source:
        aliases.setdefault(canonical(entry['machine']), []).append(entry['machine'])
    aliases = {k: sorted(set(v)) for k, v in aliases.items()}
    require(aliases == manifest['aliases'], 'aliases do not match original source')
    require([r['machine'] for r in rows] == sorted(aliases), 'duplicate or missing result rows')
    require(len(rows) == manifest['canonical_candidates'] == summary['canonical_candidates'] and
            len(source) == manifest['distinct_input_rows'] == manifest['sources'][0]['distinct_rows'],
            'source/result counts disagree')
    outcomes = dict(sorted(Counter(r['status'] for r in rows).items()))
    require(summary['proof_credit'] == 0 and outcomes == summary['outcomes'], 'summary mismatch')
    for row in rows:
        require(row['start'] == CUTOFF and row['cap'] == manifest['cap'], 'row bounds mismatch')
        require(row['status'] in ('cap', 'closed-control-mask'), 'unexpected scan outcome')
        for kind, length in (('state', 4), ('instruction', 8)):
            visits = row[kind + '_first']
            require(len(visits) == length and all(t is None or
                    (type(t) is int and CUTOFF <= t <= row['stopped_at']) for t in visits),
                    'invalid first-visit array')
        closed = row['instruction_control_closed_at']
        require((closed is None and row['status'] == 'cap' and row['stopped_at'] == row['cap']) or
                (closed == row['stopped_at'] and row['status'] == 'closed-control-mask' and
                 CUTOFF <= closed <= row['cap']), 'invalid stop/closure time')
    for kind in ('state', 'instruction'):
        latest = max((t, r['machine'], k) for r in rows
                     for k, t in enumerate(r[kind+'_first']) if t is not None)
        require(summary[kind+'_record'] == dict(horizon=latest[0], extra_wait=latest[0]-CUTOFF,
                machine=latest[1], target_index=latest[2]), 'record mismatch')
        require(summary[kind+'_control_mask_candidates'] == sum(
                r[kind+'_control_closed_at'] is not None for r in rows), 'closure count mismatch')
    indexed = {r['machine']: r for r in rows}
    fast, slow, holdouts = [], [], []
    for entry in source:
        row = indexed[canonical(entry['machine'])]
        item = {k: entry[k] for k in ('source_index', 'machine', 'ptr')}
        if row['instruction_control_closed_at'] is None:
            visits = original_visits(entry['machine'], row)
            item['missing_instruction_mask'] = sum(1 << k for k, t in enumerate(visits) if t is None)
            holdouts.append(item)
        else:
            item['width'], item['tail_mask'] = nomination(entry['machine'], row)
            (fast if item['width'] <= FAST_WIDTH else slow).append(item)
    require((len(fast), len(slow), len(holdouts)) == (9480, 507, 6397), 'frozen selection changed')
    fields = ['source_index', 'machine', 'ptr', 'width', 'tail_mask']
    artifacts = {'instruction-observations.tsv': tsv(fast, fields),
                 'instruction-observations-slow.tsv': tsv(slow, fields),
                 'instruction-scan-holdouts.tsv': tsv(holdouts, fields[:3] + ['missing_instruction_mask'])}
    spec = dict(schema_version=1, input='instruction-observations.tsv',
                input_sha256=digest(artifacts['instruction-observations.tsv']), rows=len(fast),
                cutoff=CUTOFF, upper_width=UPPER_WIDTH, default_batch_size=16,
                beep_mode='instruction', tail_invariant='total-state-mask-with-both-symbols-observed',
                status='Untrusted nominations for independent Coq replay; no batch proof credit',
                archive_sha256=ARCHIVE_SHA256, maximum_local_width=FAST_WIDTH)
    validation = dict(schema_version=1, proof_credit=0, coverage_proved=False,
        scope='Instruction scan of the 16384 state-selected families only; not an instruction census',
        archive_sha256=ARCHIVE_SHA256, source_sha256=bound['input']['sha256'],
        scanner_source_sha256=manifest['scanner_source_sha256'], driver_sha256=manifest['driver_sha256'],
        binary_sha256=manifest['binary_sha256'], summary=summary,
        checks=['archive hash and safe member layout', 'worker/results exact agreement',
                'source and scanner hashes', 'canonical alias coverage', 'recomputed summary',
                'observed transitions defined', 'total closed state invariant',
                'original table coordinates restored; one-step endpoint extension'],
        fast_nominations=len(fast), slow_nominations=len(slow), scan_holdouts=len(holdouts),
        fast_all_eight=sum(r['tail_mask'] == 0 for r in fast),
        fast_total_tail=sum(r['tail_mask'] != 0 for r in fast),
        artifacts={k: dict(bytes=len(v), sha256=digest(v)) for k, v in artifacts.items()})
    artifacts['instruction-observations.json'] = (json.dumps(spec, indent=2)+'\n').encode()
    artifacts['instruction-scan-validation.json'] = (json.dumps(validation, indent=2)+'\n').encode()
    output.mkdir(parents=True, exist_ok=True)
    for name, data in artifacts.items():
        (output/name).write_bytes(data)
    return validation


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--archive', type=Path, required=True)
    parser.add_argument('--output', type=Path, default=ROOT/'build/instruction-nominations')
    args = parser.parse_args()
    print(json.dumps(prepare(args.archive, args.output), indent=2))


if __name__ == '__main__':
    main()
