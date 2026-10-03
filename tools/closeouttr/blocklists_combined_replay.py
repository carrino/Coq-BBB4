#!/usr/bin/env python3
"""Replay combined-potential block-list batches from their saved Coq data.

Search metadata records the checker parameters and certificate SHA-256;
large certificate strings occur only in the generated Coq batches.
"""
import argparse
from collections import defaultdict
import hashlib
import json
from pathlib import Path
import tempfile
import cbt
import fuelmixtr_batch as mix
import fuelphasetr_batch as phase

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
RECORDS = HERE / 'fuelcombined_blocklists.jsonl'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    batches = defaultdict(list)
    for record in map(json.loads, RECORDS.read_text().splitlines()):
        if record['status'] != 'found':
            continue
        batch, index = record['certificate_batch'], record['certificate_index']
        engine = record['engine']
        assert engine in ('mix', 'phase')
        text = (ROOT / 'theories/CloseoutTr' / (batch + '.v')).read_text()
        prefix = 'fuelmixtr' if engine == 'mix' else 'fuelphase'
        name = f'{prefix}_{batch[4:]}_{index:04d}'
        start = f'Definition {name} : Instr -> list fmxcomp * list positive :=\n'
        cert = text.split(start, 1)[1].split('\n  end.', 1)[0] + '\n  end'
        assert hashlib.sha256(cert.encode()).hexdigest() == record['certificate_sha256'], name
        batches[batch].append((index, dict(record, cert=cert)))
    for batch, records in sorted(batches.items()):
        target = ROOT / 'theories/CloseoutTr' / (batch + '.v')
        engines = {r['engine'] for _, r in records}
        assert len(engines) == 1
        emitter = mix if engines == {'mix'} else phase
        with tempfile.TemporaryDirectory() as tmp:
            cbt.CT = tmp
            emitter.write_records('AST', int(batch.rsplit('_', 1)[1]), sorted(records))
            generated = (Path(tmp) / (batch + '.v')).read_text()
        if args.check:
            assert target.read_text() == generated, batch
        else:
            target.write_text(generated)
        print(('checked' if args.check else 'wrote'), batch)


if __name__ == '__main__':
    main()
