#!/usr/bin/env python3
"""Replay FuelPhase certificates with shared numeral definitions.

Sharing changes only the Coq spelling of constants. The decoded certificate
must match its recorded SHA-256. FuelPhaseTargetTr checks one instruction;
FuelMixPartialTr checks the other seven in a smaller abstraction. Stored Coq files are the sole
certificate payload; no old Git objects or external search output are needed.
"""
import argparse
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import re
import tempfile
import cbt
import fuelphasetr_batch as phase

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
RECORDS = ('fuelphasetr_blocklists_cores.jsonl', 'fuelphasetr_blocklists_mates.jsonl')
NAT = r'(?:\d+|\(\d+ \* 1000 \+ \d+\))'
PAIR = re.compile(r'\((\d+)%positive, (' + NAT + r')\)')
POS = re.compile(r'\b(\d+)%positive')


@lru_cache(None)
def nat_value(text):
    if text.isdecimal():
        return int(text)
    a, b = text[1:-1].rsplit(' * 1000 + ', 1)
    return nat_value(a) * 1000 + int(b)


def compact(cert, prefix):
    values = sorted({nat_value(m[2]) for m in PAIR.finditer(cert)})
    names = {v: f'{prefix}_n{i}' for i, v in enumerate(values)}
    declarations = []
    previous, previous_name = 0, '0'
    for value in values:
        name = names[value]
        declarations.append(f'Local Definition {name} : nat := {value-previous} + {previous_name}.')
        previous, previous_name = value, name
    shared = PAIR.sub(lambda m: f'({m[1]}%positive, {names[nat_value(m[2])]})', cert)
    keys = sorted({int(m[1]) for m in POS.finditer(shared)})
    names = {k: f'{prefix}_p{i}' for i, k in enumerate(keys)}
    declarations += [f'Local Definition {names[k]} : positive := {k}%positive.' for k in keys]
    shared = POS.sub(lambda m: names[int(m[1])], shared)
    declarations = '\n'.join(declarations)
    declarations, shared = pack_tables(declarations, shared, prefix, len(values), len(keys))
    assert expand(declarations, shared, prefix) == cert
    return declarations, shared


def varint(value):
    assert 0 < value < 65536
    out=''
    while value >= 8:
        out += format(8 + value % 8,'x')
        value //= 8
    return out + format(value,'x')


def delta_chunks(values):
    payloads=[]
    for i in range(0,len(values),128):
        previous=0; payload=''
        for key,value in values[i:i+128]:
            payload += varint(key-previous)
            if value is not None:
                assert 0 < value < 256
                payload += f'{value:02x}'
            previous=key
        payloads.append('0x'+payload+'%huint')
    return '['+';\n    '.join(payloads)+']'


def read_delta_chunks(text, pairs):
    values=[]
    for payload in re.findall(r'0x([0-9a-f]+)%huint',text):
        i=0; previous=0; count=0
        while i < len(payload):
            scale=1; delta=0
            for _ in range(6):
                digit=int(payload[i],16); i+=1
                delta+=scale*(digit%8)
                if digit<8:break
                scale*=8
            else:raise ValueError('oversized key delta')
            assert delta>0
            previous+=delta;count+=1
            if pairs:
                rank=int(payload[i:i+2],16);i+=2
                assert rank>0
                values.append((previous-1,rank-1))
            else:values.append(previous-1)
        assert count<=128
    return values


def pack_tables(declarations, shared, prefix, nvalues, nkeys):
    assert nvalues < 256 and nkeys < 65536
    pair_table = re.compile(rf'\[((?:\({prefix}_p\d+, {prefix}_n\d+\)(?:;\s*)?)+)\]')
    def pairs(match):
        values = [(int(k)+1,int(v)+1) for k,v in re.findall(rf'{prefix}_p(\d+), {prefix}_n(\d+)',match[1])]
        payload = delta_chunks(values)
        return f'(hfd_dphi {prefix}_keys {prefix}_ranks {payload})'
    packed = pair_table.sub(pairs,shared)
    key_table = re.compile(rf'\[((?:{prefix}_p\d+(?:;\s*)?)+)\]')
    def keys(match):
        values = [int(k)+1 for k in re.findall(rf'{prefix}_p(\d+)',match[1])]
        return f'(hfd_dgate {prefix}_keys {delta_chunks([(v,None)for v in values])})'
    packed = key_table.sub(keys,packed)
    assert not re.search(rf'\b{prefix}_[np]\d+\b',packed)
    declarations += f'\nLocal Definition {prefix}_keys := hfd_pool ['+'; '.join(f'{prefix}_p{i}' for i in range(nkeys))+'].'
    declarations += f'\nLocal Definition {prefix}_ranks := hfd_pool ['+'; '.join(f'{prefix}_n{i}' for i in range(nvalues))+'].'
    return declarations, packed


def unpack_tables(packed,prefix):
    def dpairs(match):
        return '['+';\n     '.join(f'({prefix}_p{k}, {prefix}_n{v})' for k,v in read_delta_chunks(match[1],True))+']'
    packed = re.sub(rf'\(hfd_dphi {prefix}_keys {prefix}_ranks (\[[^\]]*\])\)',dpairs,packed)
    def dkeys(match):
        return '['+';\n     '.join(f'{prefix}_p{k}'for k in read_delta_chunks(match[1],False))+']'
    return re.sub(rf'\(hfd_dgate {prefix}_keys (\[[^\]]*\])\)',dkeys,packed)


def expand(declarations, shared, prefix):
    numbers, literals = {'0': 0}, {}
    for name, delta, previous in re.findall(
            rf'Local Definition ({prefix}_n\d+) : nat := (\d+) \+ (\w+)\.', declarations):
        value = int(delta) + numbers[previous]
        numbers[name] = value
        literals[name] = phase.ft.gf.gb.fmt_nat(value)
    for name, value in re.findall(
            rf'Local Definition ({prefix}_p\d+) : positive := (\d+)%positive\.', declarations):
        literals[name] = value + '%positive'
    shared = unpack_tables(shared,prefix)
    return re.sub(rf'\b{prefix}_[np]\d+\b', lambda m: literals[m[0]], shared)


def extract(record, text):
    batch, index = record['certificate_batch'], record['certificate_index']
    ident = f'fuelphase_{batch[4:]}_{index:04d}'
    declarations, cert = text.split(
        f'Definition {ident} : Instr -> list fmxcomp * list positive :=\n', 1)
    cert = cert.split(f'\n\nDefinition {ident}_l0', 1)[0]
    assert cert.endswith('.'), ident
    cert = expand(declarations, cert[:-1], 'sh' + batch.rsplit('_', 1)[1])
    assert hashlib.sha256(cert.encode()).hexdigest() == record['certificate_sha256'], ident
    return cert


def emit(record):
    nn = int(record['certificate_batch'].rsplit('_', 1)[1])
    assert record['certificate_index'] == 0 and record['t'] == 0 and record['modulus'] == 2
    name = f'fuelphase_AST_{nn}_0000'
    declarations, cert = compact(record['cert'], f'sh{nn}')
    preamble = [declarations, f'Definition {name} : Instr -> list fmxcomp * list positive :=\n{cert}.']
    names = []
    for suffix, words in zip(('l0', 'l1', 'r0', 'r1'), record['left_grams'] + record['right_grams']):
        gram_name = name + '_' + suffix
        names.append(gram_name)
        preamble.append(f'Definition {gram_name} : list (list Sym) := {phase.emit_grams(words)}.')
    partial = record['partial']
    target = '(St' + 'ABCD'[record['target'][0]] + ', S' + str(record['target'][1]) + ')'
    preamble += [f'Definition {name}_partial : Instr -> list fmxcomp * list positive :=\n{partial}.',
                 f'Definition {name}_skip (q : Instr) : bool := instr_eqb q {target}.']
    proof = 'apply coversTr_nqh. '

    if record['mirrored']:
        proof += 'apply neverqhtr_mirror. '
    proof += (f'apply (ngram_check_neverqh_fuelmixtr_except_sound _ 3 0 '
              f'{record["partial_fuel"]} {record["partial_rounds"]} {name}_skip {name}_partial).\n'
              f'  - intros [[] []] H; try discriminate.\n'
              f'    apply (ngram_check_recurrent_phase2tr_sound _ {record["n"]} {record["fuel"]} '
              + ' '.join(names) + f' {target} ({name} {target})). vm_compute. reflexivity.\n'
              '  - vm_compute. reflexivity.')
    return cbt.write_batch('AST', nn,
        ['From Coq Require Import Hexadecimal.',
         'From BBB4.Checkers Require Import NGram FuelMixTr FuelMixPartialTr FuelPhaseTargetTr HexFuelData.',
         'From BBB4.CensusTr Require Import TNF_QHTr.'], [(record['spec'], proof)],
        'compact phase recurrence for one instruction, FuelMix for the other seven',
        preamble='\n\n'.join(preamble))


def replay(record, check=True):
    target = ROOT / 'theories/CloseoutTr' / (record['certificate_batch'] + '.v')
    source = target.read_text()
    ident = f'fuelphase_{record['certificate_batch'][4:]}_0000'
    partial = source.split(f'Definition {ident}_partial : Instr -> list fmxcomp * list positive :=\n',1)[1].split(f'.\n\nDefinition {ident}_skip',1)[0]
    assert hashlib.sha256(partial.encode()).hexdigest() == record['partial_sha256']
    record = dict(record, cert=extract(record, source), partial=partial)
    original_directory = cbt.CT
    try:
        with tempfile.TemporaryDirectory() as tmp:
            cbt.CT = tmp
            generated = Path(emit(record)).read_text()
    finally:
        cbt.CT = original_directory
    if check:
        assert generated == source, target
    else:
        target.write_text(generated)
    print(('checked' if check else 'wrote'), record['certificate_batch'])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    for path in RECORDS:
        for record in map(json.loads, (HERE / path).read_text().splitlines()):
            if record.get('certificate_format') in ('hex-delta-target-v1',):
                replay(record, args.check)


if __name__ == '__main__':
    main()
