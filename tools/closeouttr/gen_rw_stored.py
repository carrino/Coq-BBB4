#!/usr/bin/env python3
"""Replace selected closeout searches with kernel-checked stored certificates.

Certificate JSON files are ordinary, untrusted source data named after the
existing row (for example BR_02_0000.json). Machine rows, theorem names and
batch lists stay unchanged. Only the checker application and its imports
change. gen_closeout_tr.py invokes this emitter, including in --check mode.
"""
from pathlib import Path
import re
import sys

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
sys.path.insert(0, str(REPO / 'tools/censustr'))
import rw_stored
from cbt import spec_row

CERTIFICATES = HERE / 'rw_certificates'
DATA = REPO / 'theories/CloseoutTr/RWCerts'
BEGIN = '(* BEGIN STORED REPWL IMPORTS *)\n'
END = '(* END STORED REPWL IMPORTS *)\n'
NAME = re.compile(r'([A-Z][A-Z0-9]{0,7}_\d{2,})_\d{4}')


def checker_pair(name, cert):
    original = 'rw_tier_tr_sound _ ' + ' '.join(
        str(cert[k]) for k in ['L', 'T', 't', 'fuel', 'M'])
    stored = 'rw_check_stored_tr_sound _ ' + ' '.join(
        str(cert[k]) for k in ['L', 'T', 't', 'M'])
    module = 'Data_' + name
    return original, stored + f' {module}.keys {module}.ranks {module}.cert'


def read_certificates(directory=CERTIFICATES):
    certificates = {}
    for path in sorted(Path(directory).glob('*.json')):
        if not NAME.fullmatch(path.stem):
            raise ValueError(f'invalid closeout certificate name: {path}')
        certificates[path.stem] = rw_stored.read(path)
    return certificates


def rewrite_batch(source, certificates):
    """Preserve the source except for exact, recognized checker proofs."""
    referenced = set(re.findall(r'\bData_([A-Z][A-Z0-9]{0,7}_\d{2,}_\d{4})\.keys\b', source))
    if referenced - set(certificates):
        raise ValueError(f'stored proof without certificate source: {sorted(referenced - set(certificates))}')
    block = re.compile(re.escape(BEGIN) + r'.*?' + re.escape(END), re.S)
    if source.count(BEGIN) != source.count(END) or source.count(BEGIN) > 1:
        raise ValueError('malformed stored RepWL import block')
    source = block.sub('', source)
    imports = ['From BBB4.Checkers Require Import RepWLStoredTr.']
    for name, cert in sorted(certificates.items()):
        module = 'Data_' + name
        prefix = (
            f'(* spec {cert["spec"]} *)\n'
            f'Definition r_{name} : list (option Trans) := {spec_row(cert["spec"])}.\n'
            f'Lemma cv_{name} : coversTr (row_to_tm r_{name}).\n')
        if source.count(prefix) != 1:
            raise ValueError(f'certificate does not match exactly one machine row: {name}')
        original, stored = checker_pair(name, cert)

        def proof(checker):
            return ('Proof. apply coversTr_nqh, (' + checker + '). '
                    'vm_cast_no_check (eq_refl true). Qed.')

        old, new = prefix + proof(original), prefix + proof(stored)
        if old in source:
            source = source.replace(old, new, 1)
        elif new not in source:
            raise ValueError(f'unrecognized proof or mismatched parameters: {name}')
        imports.append(f'From BBB4.CloseoutTr.RWCerts Require {module}.')
    if certificates:
        anchor = 'Import ListNotations.\n'
        if source.count(anchor) != 1:
            raise ValueError('expected one ListNotations import')
        source = source.replace(anchor, BEGIN + '\n'.join(imports) + '\n' + END + anchor)
    return source


def original_batch(source, certificates):
    """Recover the search version for repeatable before/after benchmarks."""
    if rewrite_batch(source, certificates) != source:
        raise ValueError('benchmark input is not current generated source')
    source = re.sub(re.escape(BEGIN) + r'.*?' + re.escape(END), '', source, flags=re.S)
    for name, cert in certificates.items():
        original, stored = checker_pair(name, cert)
        source = source.replace(stored, original, 1)
    return source


def generated_files(certificates):
    """Return all outputs without mutating files, so --check stays read-only."""
    files, batches = {}, {}
    for name, cert in certificates.items():
        batch = NAME.fullmatch(name)[1]
        batches.setdefault(batch, {})[name] = cert
        files[DATA / ('Data_' + name + '.v')] = rw_stored.render(cert)
    for path in (REPO / 'theories/CloseoutTr').glob('CBT_*.v'):
        if BEGIN in path.read_text() and path.stem[4:] not in batches:
            raise ValueError(f'stored batch without certificate sources: {path}')
    for batch, certs in batches.items():
        path = REPO / 'theories/CloseoutTr' / ('CBT_' + batch + '.v')
        files[path] = rewrite_batch(path.read_text(), certs)
    expected = {p for p in files if p.parent == DATA}
    unexpected = set(DATA.glob('Data_*.v')) - expected
    if unexpected:
        raise ValueError(f'certificate data without JSON source: {sorted(unexpected)}')
    return files
