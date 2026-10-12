#!/usr/bin/env python3
"""Compare VM/native evaluation of identical manifest-backed RepWL searches.

Build RepWLTr.vo and its native dependencies first. Each evaluator checks a
fresh copy of the same boolean goal and reports closed assumptions. Generated
benchmark objects never replace production proof objects.
"""
import argparse
import json
from pathlib import Path
import subprocess
import sys

import gen_provtr_rw as gen

HERE = Path(__file__).resolve().parent


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--row', default='09:0', help='stage:index from the frozen manifest')
    ap.add_argument('--output', required=True, type=Path)
    args = ap.parse_args()
    stage, index = map(int, args.row.split(':'))
    rows = gen.read_manifest(HERE / 'provtr_rw_stages.tsv')
    row = next(r for r in rows if (r['stage'], r['index']) == (stage, index))
    config = subprocess.check_output(['coqc', '-config'], text=True)
    if 'COQ_NATIVE_COMPILER_DEFAULT=no' in config:
        ap.error('native-capable Coq required; VM fallback would invalidate this comparison')
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    if (output / 'metadata.json').exists():
        ap.error('use a new output directory')
    metadata = dict(row=row, coq=subprocess.check_output(['coqc', '--version'], text=True))
    (output / 'metadata.json').write_text(json.dumps(metadata, indent=2) + '\n')
    params = ' '.join(str(row[k]) for k in gen.FIELDS[3:])
    for evaluator in ['vm', 'native']:
        source = output / f'Check_{evaluator}.v'
        source.write_text(
            'From BBB4 Require Import BBB4_Statement.\n'
            'From BBB4.CensusTr Require Import RepWLTr.\n'
            + gen.tm_lambda('tm', row['spec']) + '\n'
            + f'Lemma check : rw_tier_tr tm {params} = true.\n'
            + f'Proof. {evaluator}_cast_no_check (eq_refl true). Qed.\n'
            + 'Print Assumptions check.\n')
        result = output / f'{evaluator}.json'
        subprocess.run([sys.executable, str(HERE / 'bench_short_circuit.py'), '--worker',
                        str(source), str(source.with_suffix('.log')), str(result)], check=True)
        print(result.read_text(), flush=True)


if __name__ == '__main__':
    main()
