"""Replay the right-tape parity theorem and two complete state families.

The compact tuples are proposals only. Every graph and marker edge is rebuilt
in Coq, then a full recursive coqchk audit covers the inventory and regressions.
No prior accepted package or core theorem is rewritten.
"""
import argparse
import hashlib
import json
from pathlib import Path
import resource
import subprocess
import time

from check_campaign import dependency_hashes, inventory_source
from generate_pipeline_examples import codes
import check_burn9_context_marker as wrappers
import kernel_audit_cache_v3 as kernel

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / 'research/burn14-right-parity'
OUTPUT = ROOT / 'build/burn14-right-parity/proof'
NS = 'BBB24Burn14RightParity'
TEMPLATES = ['RightParity.v', 'Regression.v']


def artifact(suffix):
    return BASE.with_name(BASE.name + '-' + suffix)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def exact(path, text):
    if path.exists() and path.read_text() != text:
        raise ValueError('Frozen artifact differs: ' + str(path))
    if not path.exists():
        path.write_text(text)


def example(index, row):
    table = ';'.join(map(str, codes(row['machine'])))
    w1, w2, w3 = row['weights'][1:]
    params = (f"{row['parity_mask']}%N {row['color_bits']}%N {w1} {w2} {w3} "
              f"{row['history']} {row['width']} {row['anchor']} {row['fuel']} {row['rounds']}")
    return f'''From Coq Require Import List NArith.
From BBB24 Require Import Statement Spec Pipeline.
From {NS} Require Import RightParity.
Import ListNotations.
Definition machine_{index} := machine_of_codes[{table}].
Lemma right_parity_accepted : rp_check machine_{index} {params}=true.
Proof. vm_compute;reflexivity. Qed.
Theorem nonhalt_{index} : NonHalt machine_{index}.
Proof. exact(proj1(rp_check_sound _ _ _ _ _ _ _ _ _ _ _ right_parity_accepted)). Qed.
Theorem state_zero_{index} : QHBound 0 machine_{index}.
Proof. exact(proj2(rp_check_sound _ _ _ _ _ _ _ _ _ _ _ right_parity_accepted)). Qed.
Print Assumptions state_zero_{index}.
'''


def board(rows):
    return wrappers.board(rows).replace(wrappers.NS, NS)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--timeout', type=int, default=300)
    parser.add_argument('--audit-timeout', type=int, default=1800)
    args = parser.parse_args()
    if min(args.timeout, args.audit_timeout) <= 0:
        parser.error('Positive budgets required')
    resource.setrlimit(resource.RLIMIT_AS, (3 * 1024**3, 3 * 1024**3))
    OUTPUT.mkdir(parents=True, exist_ok=True)
    input_path = artifact('input.json')
    report_path = artifact('checked.json')
    inventory_path = artifact('machines.json')
    old = json.loads(report_path.read_text()) if report_path.exists() else None
    protected = {p: sha(p) for p in (report_path, inventory_path) if p.exists()}
    data = json.loads(input_path.read_text())
    rows = data['rows']
    assert len(rows) == len({r['machine'] for r in rows}) == 2 and data['state_bound'] == 0
    for row in rows:
        assert row['code'] == sum(v * 17**i for i, v in enumerate(codes(row['machine'])))
        assert len(row['weights']) == 4 and row['weights'][0] == 0
        assert row['parity_mask'] in range(2, 16, 2) and int(row['color_bits']) >= 0
    templates = [ROOT / 'proof-sources/burn14-right-parity' / name for name in TEMPLATES]
    template_pins = {str(p.relative_to(ROOT)): sha(p) for p in templates}
    assert template_pins == data['template_sha256']
    selection = ROOT / data['selection_report']
    assert sha(selection) == data['selection_sha256']
    assert rows == json.loads(selection.read_text())['rows']
    dependency_report = ROOT / 'research/burn12-history-marker-checked.json'
    assert sha(dependency_report) == data['generic_report_sha256']
    generic = json.loads(dependency_report.read_text())
    for group in ('inputs_sha256', 'template_sha256', 'source_sha256', 'object_sha256'):
        for name, digest in generic[group].items():
            assert sha(ROOT / name) == digest, name
    native_report = ROOT / 'research/burn14-right-parity-native.json'
    assert sha(native_report) == data['native_report_sha256']
    inputs = {str(p.relative_to(ROOT)): sha(p) for p in (input_path, selection, dependency_report, native_report)}
    load_paths = [(ROOT / 'theories', 'BBB24'),
                  (ROOT / 'build/burn12-history-marker/proof', 'BBB24Burn12HistoryMarker'), (OUTPUT, NS)]
    flags = [part for p, ns in load_paths for part in ('-Q', str(p), ns)]
    files = []
    for template in templates:
        path = OUTPUT / template.name
        exact(path, template.read_text())
        files.append(path)
    for index, row in enumerate(rows):
        path = OUTPUT / f'Example{index:02d}.v'
        exact(path, example(index, row))
        files.append(path)
    path = OUTPUT / 'Board.v'
    exact(path, board(rows))
    files.append(path)
    descriptor = dict(id='burn14_right_parity', scope='state', rows=len(rows), state_bound=0,
                      instruction_bound=None, module=NS + '.Inventory', board='board',
                      small_sound='small_sound', sound='sound', was_pending='was_pending',
                      proof_source=str((OUTPUT / 'Inventory.v').relative_to(ROOT)),
                      exact_inventory_theorem=NS + '.Inventory.inventory_exact',
                      inventories=[dict(path=str(inventory_path.relative_to(ROOT)), format='rows')],
                      load_paths=[dict(path=str(p.relative_to(ROOT)), namespace=ns) for p, ns in load_paths[1:]])
    path = OUTPUT / 'Inventory.v'
    exact(path, inventory_source(dict(descriptor, module=NS + '.Board', machines=[r['machine'] for r in rows])))
    files.append(path)
    sources = dependency_hashes(files, flags)
    for name in ('check_burn14_right_parity.py', 'check_burn14_right_parity_native.py', 'check_burn9_context_marker.py',
                 'check_campaign.py', 'check_shadow_links.py', 'generate_pipeline_examples.py',
                 'kernel_audit_cache_v3.py'):
        sources['tools/' + name] = sha(ROOT / 'tools' / name)
    inventory = json.dumps(dict(rows=[dict(machine=r['machine']) for r in rows]), indent=2) + '\n'
    stable = dict(inputs_sha256=inputs, template_sha256=template_pins, source_sha256=sources,
                  descriptor=descriptor, inventory_sha256=hashlib.sha256(inventory.encode()).hexdigest(),
                  checked_state_families=len(rows), checked_instruction_families=0)
    if old:
        assert all(old[key] == value for key, value in stable.items())
    timings = {}
    for path in files:
        started = time.monotonic()
        with path.with_suffix('.log').open('w') as log:
            subprocess.run(['coqc', '-w', '-abstract-large-number', '-native-compiler', 'no', *flags, str(path)],
                           stdout=log, stderr=subprocess.STDOUT, check=True, timeout=args.timeout)
        timings[path.stem] = round(time.monotonic() - started, 3)
        print(f'Compiled {path.stem}: {timings[path.stem]}s', flush=True)
    receipt, log = kernel.fresh_paths(OUTPUT, 'kernel-audit')
    started = time.monotonic()
    audit = kernel.audit([NS + '.Inventory', NS + '.Regression'], [files[-1], files[1]], load_paths,
                         receipt, log, recursive=True, timeout=args.audit_timeout)
    assert all(sha(ROOT / p) == digest for p, digest in {**inputs, **sources, **template_pins}.items())
    assert all(sha(p) == digest for p, digest in protected.items())
    current = dict(stable, scope='Two exact complete state-zero census families, all completions. No instruction claim.',
                   compile_seconds=timings, kernel_receipt=str(receipt.relative_to(ROOT)),
                   kernel_receipt_sha256=sha(receipt), kernel_audit='Full recursive coqchk, including ten boundary regressions.',
                   audit_seconds=round(time.monotonic() - started, 3),
                   checked_modules=len(audit['checked_modules']), reused_modules=len(audit['reused_modules']),
                   object_sha256={str(p.with_suffix('.vo').relative_to(ROOT)): sha(p.with_suffix('.vo')) for p in files})
    if old is None:
        exact(inventory_path, inventory)
        exact(report_path, json.dumps(current, indent=2, sort_keys=True) + '\n')
    (OUTPUT / 'current-proof-receipt.json').write_text(json.dumps(current, indent=2, sort_keys=True) + '\n')
    print('Two right-parity state families fully audited.', flush=True)


if __name__ == '__main__':
    main()
