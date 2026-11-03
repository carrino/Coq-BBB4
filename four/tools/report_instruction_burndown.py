"""Report exact historical instruction holdouts and recorded proof upgrades.

This is portable inventory accounting. For fresh kernel verification, run the
registered proof replayers first. No global instruction upper bound is claimed.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re

from check_campaign import ROOT, read_inventory, sha
from instruction_residual import residual


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    baseline = ROOT / 'research/instruction-baseline.json'
    remaining, pins = residual(baseline, sha(baseline))
    initial = len(remaining)
    upgrades, accepted = [], set()
    registry_path = ROOT / 'research/instruction-accepted-batches.json'
    registry = json.loads(registry_path.read_text())
    if registry.get('schema_version') != 1 or not registry.get('batches'):
        raise ValueError('Invalid accepted instruction batch registry')
    pins[str(registry_path.relative_to(ROOT))] = sha(registry_path)
    seen = set()
    for entry in registry['batches']:
        name = entry['name']
        if not re.fullmatch(r'instruction-[a-z0-9-]+', name) or name in seen:
            raise ValueError('Invalid or repeated accepted instruction batch')
        seen.add(name)
        report_path = ROOT / 'research' / (name + '-checked.json')
        if sha(report_path) != entry['report_sha256']:
            raise ValueError('Accepted instruction report differs: ' + name)
        report = json.loads(report_path.read_text())
        spec = report['descriptor']['inventories'][0]
        path = ROOT / spec['path']
        if sha(path) != report['inventory_sha256']:
            raise ValueError('Recorded proof inventory differs: ' + name)
        machines = read_inventory(spec)
        if (len(machines) != len(set(machines)) or len(machines) != report['new_instruction_families'] or
                not set(machines) <= remaining or accepted & set(machines)):
            raise ValueError('Repeated, missing or out-of-baseline proof credit')
        accepted.update(machines)
        remaining.difference_update(machines)
        pins[str(report_path.relative_to(ROOT))] = sha(report_path)
        pins[spec['path']] = sha(path)
        upgrades.append(dict(name=name, new_instruction_families=len(machines),
                             theorem=report['descriptor']['module'] + '.sound'))
    text = ''.join(machine + '\n' for machine in sorted(remaining))
    summary = dict(scope='Historical hard-cohort instruction inventory; not a global instruction census theorem.',
        historical_holdouts=initial, new_instruction_families=len(accepted),
        remaining_instruction_families=len(remaining), new_state_families=0,
        global_instruction_upper_bound_proved=False,
        remaining_machine_text_sha256=hashlib.sha256(text.encode()).hexdigest(),
        inputs_sha256=pins, upgrades=upgrades)
    output = ROOT / 'research/instruction-burndown-summary.json'
    content = json.dumps(summary, indent=2, sort_keys=True) + '\n'
    if args.check:
        if not output.exists() or output.read_text() != content:
            raise ValueError('Published instruction scoreboard differs')
    else:
        output.write_text(content)
    directory = ROOT / 'build/instruction-burndown'
    directory.mkdir(parents=True, exist_ok=True)
    (directory / 'remaining.txt').write_text(text)
    print(json.dumps({key: summary[key] for key in ('historical_holdouts', 'new_instruction_families',
                     'remaining_instruction_families', 'global_instruction_upper_bound_proved')}, indent=2))


if __name__ == '__main__':
    main()
