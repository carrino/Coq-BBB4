#!/usr/bin/env python3
"""Replay the period-three block-list certificates into CBT_AST_102.v.

Discovery used the ordinary learner with a larger position period:
    LG4_PERIODS=3 python3 tools/closeouttr/blc5/lx5.py find \
        tools/closeouttr/blc5/ast102_rows.txt OUT.jsonl --jobs 3 --timeout 300

The finder and emitter are untrusted. The unchanged ListGlueLexTr checker
validates every transition, bootstrap, invariant edge, and liveness rank.
"""
import argparse
import json
import tempfile
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import lx5
import cbt


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    rows = (HERE / 'ast102_rows.txt').read_text().splitlines()
    found = {c['spec']: c for c in map(json.loads, (HERE / 'ast102.jsonl').read_text().splitlines())}
    certs = [lx5.detuplex(found[row]) for row in rows]
    if any('err' in cert for cert in certs):
        raise SystemExit('certificate discovery failed')
    for cert in certs:
        table = lx5.T.parse(cert['spec'])
        if cert.get('mir'):
            table = lx5.T.mirror(table)
        error = lx5.c_checkx(cert, table)
        if error:
            raise SystemExit('certificate replay failed: ' + str(error))
    output = Path(cbt.batch_path('AST', 102))
    with tempfile.TemporaryDirectory() as temporary:
        cbt.CT = temporary
        generated = cbt.write_batch('AST', 102,
            ['From BBB4.Checkers Require Import LapDecider.',
             'From BBB4.Counters Require Import TriGlueTr ListGlue2Tr ListGlueLexTr.'],
            [(cert['spec'], lx5.renderx(cert)) for cert in certs],
            'period-three list language with far-end lexicographic liveness')
        contents = Path(generated).read_bytes()
    if args.check:
        if not output.is_file() or output.read_bytes() != contents:
            raise SystemExit('generated AST102 differs from ' + str(output))
        print('AST102: exact replay and generated source match')
    else:
        output.write_bytes(contents)
        print(output)


if __name__ == '__main__':
    main()
