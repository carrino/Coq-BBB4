#!/usr/bin/env python3
"""Emit right-reset period-three batches; --check checks saved output."""
import argparse
import json
from pathlib import Path
from period3_batch import ROOT, render


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    records = json.loads(Path(__file__).with_name('period3_right_reset_ast.json').read_text())
    assert len(records) == 2
    for nn, record in zip((115, 116), records):
        text = render(nn, record, [{'spec': '1RB0LC_1RC1RD_1LA1LC_1RB0RA'}])
        text = text.replace('tools/closeouttr/period3_batch.py',
                            'tools/closeouttr/period3_right_reset_batch.py')
        text = text.replace('FiniteInstrTr Period3FiniteTr.',
                            'FiniteInstrTr Period3FiniteTr Period3RightResetTr.')
        text = text.replace('apply(p3_D0_finite _ S0)', 'apply pr_D0_finite')
        path = ROOT / f'theories/CloseoutTr/CBT_AST_{nn}.v'
        if args.check:
            assert path.read_text() == text, path
        else:
            path.write_text(text)
        print(('checked' if args.check else 'wrote'), path.relative_to(ROOT))


if __name__ == '__main__':
    main()
