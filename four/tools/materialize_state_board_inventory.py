"""Export a compact packed17 inventory from a completed state-board report.

The report and its exact ledger are pinned in the output. Campaign compilation
independently proves that this inventory equals the imported Coq board.
"""
import argparse
import csv
import io
import json
from pathlib import Path

from check_state_pipeline_batch import ROOT, pack, sha


def contents(report_path):
    report = json.loads(report_path.read_text())
    ledger_path = ROOT/report['generated_ledger']
    if sha(ledger_path) != report['ledger_sha256']:
        raise ValueError('Completed state ledger differs from its audited report')
    with ledger_path.open() as stream:
        rows = list(csv.DictReader(stream, delimiter='\t'))
    count = report['state_census_linked_families']
    if count != report['state_checked_families'] or len(rows) != count or report['instruction_checked_families'] != 0:
        raise ValueError('Completed state-board counts or scope differ')
    if report['instruction_bound'] is not None:
        raise ValueError('State inventory unexpectedly claims an instruction bound')
    for row in rows:
        if (row['state_census_linked'] != 'yes' or row['instruction_census_linked'] != 'no'
                or row['instruction_bound'] or row['state_bound'] != str(report['state_bound'])
                or row['proof'] != report['state_discharge_theorem']):
            raise ValueError('Ledger row differs from its checked state theorem')
    packed = [pack(row['machine']) for row in rows]
    if len(set(packed)) != len(packed):
        raise ValueError('Repeated direct family in completed state inventory')
    meta = {'scope': 'State-only inventory; Campaign independently checks exact equality to the imported board.',
            'encoding': 'packed17, A0 least significant; code=4*write+2*right+next_B, 16 undefined',
            'report': str(report_path.resolve().relative_to(ROOT)), 'report_sha256': sha(report_path),
            'ledger_sha256': report['ledger_sha256'], 'state_bound': report['state_bound'],
            'instruction_bound': None, 'state_families': count}
    head = json.dumps(meta, indent=2)[:-2]
    body = ',\n    '.join(', '.join(map(str, packed[i:i+24])) for i in range(0, len(packed), 24))
    return head+',\n  "rows": [\n    '+body+'\n  ]\n}\n'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--report', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    text = contents(args.report)
    if args.output.exists():
        if args.output.read_text() != text:
            raise ValueError('Existing compact completed inventory differs')
    elif args.check:
        raise ValueError('Missing compact completed inventory')
    else:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text)
    print(f'Validated completed state inventory: {args.output}', flush=True)


if __name__ == '__main__':
    main()
