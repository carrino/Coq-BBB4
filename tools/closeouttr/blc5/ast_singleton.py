#!/usr/bin/env python3
"""Reproduce AST100 using the landed block-list lexicographic checker.

The certificate in ast100.jsonl was found by the unchanged BLC5 finder:
    python3 tools/closeouttr/blc5/lx5.py find ROWS.txt OUT.jsonl --jobs 1 --timeout 400
where ROWS.txt contains 1RB1LB_1RC1LD_1LA0RC_1LC0LA. Finding needs SciPy;
replaying the saved certificate and emitting Coq need only standard Python:
    python3 tools/closeouttr/blc5/ast_singleton.py
    python3 tools/closeouttr/blc5/ast_singleton.py --check
"""
import argparse
import json
from pathlib import Path
import tempfile

import lx5
import cbt


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    saved = Path(__file__).with_name('ast100.jsonl')
    records = [json.loads(line) for line in saved.read_text().splitlines() if line]
    assert len(records) == 1
    cert = lx5.detuplex(records[0])
    assert cert['spec'] == '1RB1LB_1RC1LD_1LA0RC_1LC0LA'
    table = lx5.T.parse(cert['spec'])
    if cert.get('mir'):
        table = lx5.T.mirror(table)
    error = lx5.c_checkx(cert, table)
    if error:
        raise SystemExit('certificate replay failed: ' + str(error))
    output = Path(cbt.batch_path('AST', 100))
    with tempfile.TemporaryDirectory() as temporary:
        cbt.CT = temporary
        generated = cbt.write_batch(
            'AST', 100,
            ['From BBB4.Checkers Require Import LapDecider.',
             'From BBB4.Counters Require Import TriGlueTr ListGlue2Tr ListGlueLexTr.'],
            [(cert['spec'], lx5.renderx(cert))],
            'block-list counter with affine tail relations and far-end lexicographic '
            'liveness by ListGlueLexTr')
        contents = Path(generated).read_bytes()
    if args.check:
        if not output.is_file() or output.read_bytes() != contents:
            raise SystemExit('generated AST100 differs from ' + str(output))
        print('AST100: exact replay and generated source match')
    else:
        output.write_bytes(contents)
        print(output)


if __name__ == '__main__':
    main()
