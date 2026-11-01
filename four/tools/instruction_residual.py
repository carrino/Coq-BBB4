"""Read the frozen historical instruction holdouts for research accounting.

This validates exact IDs and cohort membership. It is not a kernel audit or a
proof that this historical hard cohort is the entire global instruction census.
"""
import hashlib
import json
from pathlib import Path

from check_campaign import ROOT, read_inventory, sha


def residual(report_path, expected_sha256):
    report_path = Path(report_path).resolve()
    name = str(report_path.relative_to(ROOT))
    if sha(report_path) != expected_sha256:
        raise ValueError('Frozen instruction baseline differs: ' + name)
    data = json.loads(report_path.read_text())
    machines = read_inventory(dict(path=name, format='packed17', order='machine'))
    text = ''.join(m + "\n" for m in machines)
    if (len(machines) != data['inventory_rows'] or len(set(machines)) != len(machines) or
            hashlib.sha256(text.encode()).hexdigest() != data['machine_text_sha256']):
        raise ValueError('Incomplete, repeated or changed instruction baseline')
    cohort_spec = data['cohort']
    cohort_path = ROOT / cohort_spec['path']
    if sha(cohort_path) != cohort_spec['sha256']:
        raise ValueError('Frozen comparison cohort differs')
    cohort = read_inventory(dict(path=cohort_spec['path'], format='packed17'))
    if len(set(cohort)) != cohort_spec['rows'] or not set(machines) <= set(cohort):
        raise ValueError('Instruction baseline is outside its comparison cohort')
    return set(machines), {name: expected_sha256, cohort_spec['path']: cohort_spec['sha256']}
