#!/usr/bin/env python3
"""Check byte-exact batch emission using certificates already saved in Coq.

The search records retain parameters, grammars and certificate hashes.
Large certificate strings are stored once, in the kernel-checked batches.
"""
from collections import defaultdict
import hashlib
import json
from pathlib import Path
import tempfile
import cbt
import fuelphasetr_batch as phase

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]


def main():
    batches = defaultdict(list)
    for name in ('fuelphasetr_blocklists_cores.jsonl',
                 'fuelphasetr_blocklists_mates.jsonl'):
        for r in map(json.loads, (HERE / name).read_text().splitlines()):
            if r['status'] != 'found':
                continue
            batch, index = r['certificate_batch'], r['certificate_index']
            text = (ROOT / 'theories/CloseoutTr' / (batch+'.v')).read_text()
            ident = f'fuelphase_{batch[4:]}_{index:04d}'
            cert = text.split(f'Definition {ident} : Instr -> list fmxcomp * list positive :=\n',1)[1]
            cert = cert.split(f'\n\nDefinition {ident}_l0',1)[0]
            assert cert.endswith('.'), ident
            cert = cert[:-1]
            assert hashlib.sha256(cert.encode()).hexdigest() == r['certificate_sha256'], ident
            r['cert'] = cert
            batches[batch].append((index,r))
    for batch, records in sorted(batches.items()):
        target = ROOT / 'theories/CloseoutTr' / (batch+'.v')
        with tempfile.TemporaryDirectory() as tmp:
            cbt.CT = tmp
            phase.write_records('AST',int(batch.rsplit('_',1)[1]),sorted(records))
            assert (Path(tmp)/(batch+'.v')).read_text() == target.read_text(), batch
        print('checked',batch)


if __name__ == '__main__':
    main()
