#!/usr/bin/env python3
"""Regenerate the reviewed desktop proof index; this does no Coq checking."""
import csv
import hashlib
import io
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def main():
    record = json.loads((ROOT / 'research/observation-desktop-validation.json').read_text())
    raw = (ROOT / 'research/observation-weekend.tsv').read_bytes()
    if hashlib.sha256(raw).hexdigest() != record['input_sha256']:
        raise SystemExit('Observation input differs from the reviewed snapshot')
    rows = list(csv.DictReader(io.StringIO(raw.decode()), delimiter='\t', strict=True))
    index = record['proof_index']
    if len(rows) != index['rows'] or index['batch_size'] != 16:
        raise SystemExit('Observation count or partition differs from the reviewed batch')
    result = io.StringIO(newline='')
    writer = csv.DictWriter(result, ['machine', 'ptr', 'theorem'], delimiter='\t', lineterminator='\n')
    writer.writeheader()
    for i, row in enumerate(rows):
        writer.writerow({'machine': row['machine'], 'ptr': row['ptr'],
                         'theorem': f'BBBWait42Observation.Part{i // 16:06d}.all_completions'})
    data = result.getvalue().encode()
    if hashlib.sha256(data).hexdigest() != index['sha256']:
        raise SystemExit('Generated index differs from the reviewed index')
    output = ROOT / 'build/observation-desktop-proved.tsv'
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_bytes(data)
    print(f'Wrote {len(rows)} reviewed family identities to {output}; no Coq checking performed.')


if __name__ == '__main__':
    main()
