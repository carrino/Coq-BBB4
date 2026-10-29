"""Prepare the remaining fresh-state cohort for a bounded history sweep.

This is search scheduling only. The excluded rows are exact inventories of
completed burn2 proof batches; any new native acceptance still needs Coq replay.
Running this script does not launch the search.
"""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PREFIX = ROOT / 'research/burn3-history'
INVENTORIES = (
    ('burn2-state-pilot', 119),
    ('burn2-state-full', 754),
    ('burn2-state-ordinary-pilot', 14),
    ('burn2-state-full-ordinary', 121),
    ('burn2-diagnostic-short', 9),
)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def exact(path, text):
    if path.exists() and path.read_text() != text:
        raise ValueError('Refusing to change frozen search input: ' + str(path))
    if not path.exists():
        path.write_text(text)


def save(path, data):
    exact(path, json.dumps(data, indent=2, sort_keys=True) + '\n')


def main():
    source = ROOT / 'research/burn2-state-input.txt'
    source_manifest = ROOT / 'research/burn2-state-input.json'
    inventory = source.read_text().splitlines()
    prior = json.loads(source_manifest.read_text())
    if len(inventory) != len(set(inventory)) or len(inventory) != 2089:
        raise ValueError('Expected 2089 distinct source-state obligations')
    if sha(source) != prior['remaining_sha256']:
        raise ValueError('Source-state cohort differs from its frozen manifest')
    excluded, provenance = set(), []
    for prefix, expected in INVENTORIES:
        path = ROOT / 'research' / (prefix + '-machines.json')
        report = ROOT / 'research' / (prefix + '-checked.json')
        # Completed report presence and byte pins make this a reproducible
        # scheduling selection; the aggregate proof checker validates evidence.
        data = json.loads(path.read_text())
        rows = [row['machine'] for row in data['rows']]
        if len(rows) != len(set(rows)) or len(rows) != expected:
            raise ValueError('Unexpected accepted inventory: ' + prefix)
        if excluded.intersection(rows) or not set(rows) <= set(inventory):
            raise ValueError('Accepted inventory overlap or foreign source row')
        excluded.update(rows)
        provenance.append({'inventory': str(path.relative_to(ROOT)),
                           'inventory_sha256': sha(path),
                           'report': str(report.relative_to(ROOT)),
                           'report_sha256': sha(report), 'rows': len(rows)})
    remaining = sorted(set(inventory) - excluded,
                       key=lambda row: hashlib.sha256(row.encode()).digest())
    if len(excluded) != 1017 or len(remaining) != 1072:
        raise ValueError('Unexpected burn3 history partition')
    text = ''.join(machine + '\n' for machine in remaining)
    input_path = PREFIX.with_name(PREFIX.name + '-input.txt')
    manifest = PREFIX.with_name(PREFIX.name + '-input-manifest.json')
    stages_path = PREFIX.with_name(PREFIX.name + '-stages.json')
    stages = [dict(mode='hist', size=width, anchor=4096, fuel=16384,
                   extra=32, history=history) for width, history in [(4, 3), (3, 5)]]
    exact(input_path, text)
    save(manifest, {'scope': 'Untrusted search scheduling only; no new proof claims.',
                    'source': str(source.relative_to(ROOT)),
                    'source_sha256': sha(source),
                    'source_manifest_sha256': sha(source_manifest),
                    'source_rows': len(inventory),
                    'excluded_inventories': provenance,
                    'excluded_rows': len(excluded),
                    'remaining_rows': len(remaining),
                    'remaining_sha256': sha(input_path),
                    'selection': 'All remaining rows ordered by SHA256(machine UTF-8)'})
    save(stages_path, stages)
    command = ['python3', 'four/tools/state_pipeline_sweep.py',
               '--input', 'four/research/burn3-history-input.txt',
               '--input-manifest', 'four/research/burn3-history-input-manifest.json',
               '--stages', 'four/research/burn3-history-stages.json',
               '--output-dir', 'four/build/burn3-history',
               '--report', 'four/research/burn3-history-search.json',
               '--probe', 'four/build/state-pipeline/probe',
               '--bound', '4096', '--timeout', '2', '--sample', '0']
    save(PREFIX.with_name(PREFIX.name + '-plan.json'), {
        'scope': 'Untrusted discovery; accepted rows require fresh Coq replay.',
        'input_rows': len(remaining), 'state_bound': 4096,
        'instruction_bound': None, 'workers': 1,
        'address_space_limit_bytes': 2147483648,
        'timeout_seconds_per_stage_row': 2,
        'maximum_native_row_budget_seconds': len(remaining) * len(stages) * 2,
        'pilot': {'input_rows': 21, 'state_candidates': 9,
                  'total_native_row_seconds': 6.907805,
                  'warning': 'The diagnostic pilot is not a random sample.'},
        'command': command, 'producer_sha256': sha(Path(__file__)),
        'prepared_files_sha256': {str(path.relative_to(ROOT)): sha(path)
                                 for path in (input_path, manifest, stages_path)}})
    print(json.dumps({'source': len(inventory), 'excluded': len(excluded),
                      'remaining': len(remaining), 'command': command}))


if __name__ == '__main__':
    main()
