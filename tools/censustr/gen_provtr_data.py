#!/usr/bin/env python3
"""Emit the instruction census's ordered proven lists as data-only Coq.

This source reader is untrusted. RunTr reattaches the original Forall
proofs to the generated lists; Coq must check their convertibility. A
dropped, reordered or incorrectly encoded machine cannot pass that gate.
Definitions of prov_tr/provqh_tr and their proofs remain in RunTr.v.
"""
import argparse
from pathlib import Path
import re

from gen_walk_shards import tm_lambda

REPO = Path(__file__).resolve().parents[2]
CENSUS = REPO/'theories/CensusTr'


def uncomment(text):
    out, depth, i = [], 0, 0
    while i < len(text):
        token = text[i:i+2]
        if token == '(*':
            depth += 1; i += 2
        elif token == '*)' and depth:
            depth -= 1; i += 2
            if not depth:
                out.append(' ')
        else:
            if not depth:
                out.append(text[i])
            i += 1
    if depth:
        raise ValueError('unterminated Coq comment')
    return ''.join(out)


def spec_from_name(name):
    match = re.fullmatch(r'tm_((?:(?:[01][LR][ABCD]|XXX|___){2}_){3}'
                         r'(?:[01][LR][ABCD]|XXX|___){2})', name)
    if not match:
        return None
    body = match[1]
    return '_'.join(''.join('---' if body[o+s:o+s+3] in ['XXX','___']
                           else body[o+s:o+s+3] for s in [0,3])
                    for o in [0,7,14,21])


def machine_spec(body):
    transitions = {}
    for q, s, action in re.findall(
            r'\|\s*St([ABCD]),\s*S([01])\s*=>\s*(.*?)(?=\||\bend\b)', body, re.S):
        action = action.strip()
        if action == 'None':
            value = '---'
        else:
            match = (re.fullmatch(r'Some\s*\(mkTrans S([01]) D([LR]) St([ABCD])\)', action)
                     or re.fullmatch(r'mk S([01]) D([LR]) St([ABCD])', action))
            if not match:
                raise ValueError(f'unrecognized transition: {action}')
            value = ''.join(match.groups())
        if q+s in transitions:
            raise ValueError('duplicate transition')
        transitions[q+s] = value
    if len(transitions) != 8:
        raise ValueError('expected eight explicit transitions')
    return '_'.join(transitions[q+'0']+transitions[q+'1'] for q in 'ABCD')


class Inventory:
    def __init__(self, census=CENSUS):
        census = Path(census)
        paths = {p.stem:p for p in census.glob('ProvTr_*.v')
                 if p.stem != 'ProvTr_Data'}
        paths.update({p.stem:p for p in (census/'RWParts').glob('*.v')})
        paths['RunTr'] = census/'RunTr.v'
        self.defs, self.by_name = {}, {}
        for module, path in paths.items():
            source = uncomment(path.read_text())
            for name, typ, body in re.findall(
                    r'^Definition (\w+)\s*:\s*(list TM|TM)\s*:=\s*(.*?)\.(?=\s|$)',
                    source, re.M | re.S):
                self.defs[module,name] = typ,body
                self.by_name.setdefault(name,[]).append(module)

    def resolve(self, name, module='RunTr', visiting=frozenset()):
        if '.' in name:
            module, name = name.rsplit('.',1)
        key = module,name
        if key not in self.defs:
            # Imported board names encode their machine. This remains an
            # untrusted hint: RunTr's kernel conversion checks every entry.
            spec = spec_from_name(name)
            if spec is not None:
                return [spec]
            choices = self.by_name.get(name,[])
            if len(choices) != 1:
                raise ValueError(f'ambiguous or missing definition: {key}, {choices}')
            module = choices[0]
            key = module, name
        if key in visiting:
            raise ValueError(f'cyclic list definition: {key}')
        visiting = visiting | {key}
        typ, body = self.defs[key]
        if typ == 'TM':
            if body.startswith('fun '):
                return [machine_spec(body)]
            if not re.fullmatch(r'\w+(?:\.\w+)*',body.strip()):
                raise ValueError(f'unrecognized machine alias: {key}: {body}')
            return self.resolve(body.strip(),module,visiting)
        # Only list literals and concatenations of named lists are accepted.
        refs = re.findall(r'\b\w+(?:\.\w+)*\b',body)
        if re.sub(r'\b\w+(?:\.\w+)*\b|[\[\];+\s]', '', body):
            raise ValueError(f'unrecognized list expression: {key}: {body}')
        return [spec for ref in refs for spec in self.resolve(ref,module,visiting)]


def render(inventory, chunk=100):
    if chunk < 1:
        raise ValueError('chunk must be positive')
    files = {}
    for original, module, name in [('prov_tr','ProvTr_Data','prov_tr_data'),
                                   ('provqh_tr','ProvQHTr_Data','provqh_tr_data')]:
        rows = inventory.resolve(original)
        parts = []
        for start in range(0,len(rows),chunk):
            part = f'{module}_{start//chunk:03d}'
            parts.append(part)
            body = ['(** GENERATED by tools/censustr/gen_provtr_data.py -- DO NOT EDIT.\n'
                    f'    Untrusted machine data for [{original}], indices {start}..{min(start+chunk,len(rows))-1}. *)',
                    'From Coq Require Import List.',
                    'From BBB4 Require Import BBB4_Statement.',
                    'Import ListNotations.\n']
            names = []
            for index,spec in enumerate(rows[start:start+chunk],start):
                tm = f'machine_{index:05d}'
                names.append(tm)
                body.extend([f'(* {spec} *)',tm_lambda(tm,spec)])
            body.append('Definition rows : list TM :=\n  ['+';\n   '.join(names)+'].\n')
            files[f'Data/{part}.v'] = '\n'.join(body)
        body = ['(** GENERATED by tools/censustr/gen_provtr_data.py -- DO NOT EDIT.\n'
                f'    {len(rows)} machines in [{original}] order, without board proofs.\n'
                '    RunTr reattaches the original Forall proof by kernel conversion. *)',
                'From Coq Require Import List.',
                'From BBB4 Require Import BBB4_Statement.',
                'From BBB4.CensusTr.Data Require '+' '.join(parts)+'.',
                'Import ListNotations.\n',
                f'Definition {name} : list TM :=\n  '+' ++\n  '.join(p+'.rows' for p in parts)+'.\n']
        files[module+'.v'] = '\n'.join(body)
    return files


def generate(check=False, project=REPO/'_CoqProject'):
    files = {CENSUS/name:source for name,source in render(Inventory()).items()}
    old = set((CENSUS/'Data').glob('Prov*Tr_Data_*.v'))
    if old-set(files):
        raise ValueError('unexpected old data files')
    if project is not None:
        project = Path(project)
        source = project.read_text()
        have = set(source.splitlines())
        files[project] = source + ''.join(str(p.relative_to(REPO))+'\n'
                                        for p in sorted(files) if str(p.relative_to(REPO)) not in have)
    stale = [p for p,s in files.items() if not p.exists() or p.read_text() != s]
    if check and stale:
        raise ValueError('stale generated files: '+', '.join(map(str,stale)))
    if not check:
        for path in stale:
            path.parent.mkdir(parents=True,exist_ok=True)
            path.write_text(files[path])
    print(f'proven data: {"checked" if check else "wrote"} {len(files) if check else len(stale)} files')


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--check',action='store_true')
    ap.add_argument('--no-coqproject',action='store_true')
    args = ap.parse_args()
    generate(args.check,None if args.no_coqproject else REPO/'_CoqProject')


if __name__ == '__main__':
    main()
