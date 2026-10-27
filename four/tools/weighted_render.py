"""Render untrusted four-symbol weighted certificates as kernel replay obligations."""
from pathlib import Path

HEADER = '''From Coq Require Import List ZArith NArith.
From BBB24 Require Import Statement StatementTr CTape Spec Bounds Census Mirror CycleCensus WeightedNGram WeightedCensus.
From BBB24.Checkers Require Import NGram.
Import ListNotations.
'''

def coqlist(items):
    return '[' + ';'.join(map(str, items)) + ']'

def symbols(items):
    if any(type(x) is not int or not 0 <= x < 4 for x in items):
        raise ValueError('Invalid symbol list')
    return coqlist('S' + str(x) for x in items)

def node(c):
    if len(c) != 4 or type(c[0]) is not int or not 0 <= c[0] < 2 or type(c[2]) is not int or not 0 <= c[2] < 4:
        raise ValueError('Invalid context state/head')
    return '(St' + chr(65+c[0]) + ',(' + symbols(c[1]) + ',S' + str(c[2]) + ',' + symbols(c[3]) + '))'

def naturals(items):
    if any(type(x) is not int or x < 0 for x in items):
        raise ValueError('Nonnegative integer certificate field required')
    return coqlist(str(x) + '%nat' for x in items)

def integers(items):
    if any(type(x) is not int for x in items):
        raise ValueError('Integer certificate field required')
    return coqlist('(' + str(x) + ')%Z' for x in items)

def render(row):
    g = row['graph']
    if g['states'] != 2 or g['symbols'] != 4:
        raise ValueError('Expected two states and four symbols')
    if type(g['mirror']) is not int or g['mirror'] not in (0,1):
        raise ValueError('Invalid reflection flag')
    for name in ('n','t','fuel','rounds'):
        if type(g[name]) is not int or g[name] < 0:
            raise ValueError('Invalid natural checker parameter')
    out = HEADER + 'Definition nodes:list cconf:=' + coqlist(node(c) for c in g['nodes']) + '.\n'
    branches = []
    for target, cert in sorted(row['certs'].items(), key=lambda x: int(x[0])):
        if type(cert['k']) is not int or cert['k'] < 0:
            raise ValueError('Invalid wall width')
        components = []
        for comp in cert['components']:
            kind = comp['kind']
            if kind == 'rank':
                components.append('WRank(wc_table 0%nat nodes ' + naturals(comp['rank']) + ')')
                continue
            values = comp['values']
            if any(type(x) is not int for x in values):
                raise ValueError('Integer coefficients required')
            if len(values) != len(g['nodes']) + (12 if kind == 'linear' else 16):
                raise ValueError('Coefficient vector has wrong length')
            gate = '(wc_gate nodes ' + naturals(comp['active']) + ')'
            if kind == 'linear':
                counts = []
                for part, ctor in enumerate(['MAll', 'MLeft', 'MRight']):
                    for symbol in [1, 2, 3]:
                        weight = values[4*part+symbol]
                        if type(weight) is not int or weight < 0:
                            raise ValueError('Negative/noninteger count weight')
                        if weight:
                            counts.append(f'({weight}%nat,{ctor} C{symbol})')
                components.append('WLinear ' + coqlist(counts) + ' (wc_table 0%nat nodes ' + naturals(values[12:]) + ') ' + gate)
            elif kind == 'w':
                scores = ['(wc_score ' + ' '.join('('+str(x)+')%Z' for x in values[j:j+4]) + ')' for j in [0, 4, 8, 12]]
                components.append('WBinary ' + ' '.join(scores) + ' (wc_table 0%Z nodes ' + integers(values[16:]) + ') ' + gate)
            else:
                raise ValueError('Unknown weighted component')
        target = int(target)
        if not 0 <= target < 8:
            raise ValueError('Invalid instruction target')
        name = 'target_' + str(target)
        out += f'Definition {name}:WCert:=mkWC {cert["k"]}%nat ' + coqlist(symbols(w) for w in cert['guards']) + ' ' + coqlist(node(c) for c in cert['inside']) + ' ' + coqlist(components) + '.\n'
        branches.append(f'|(St{chr(65+target//4)},S{target%4})=>Some {name}')
    out += 'Definition certificate(t:Instr):option WCert:=match t with ' + ''.join(branches) + '|_=>None end.\n'
    name = g['machine']
    if len(name) != 25 or name[12] != '_':
        raise ValueError('Invalid machine string')
    flat = name.replace('_', '')
    branches = []
    for j in range(8):
        cell = flat[3*j:3*j+3]
        if cell == '---':
            value = 'None'
        elif cell[0] in '0123' and cell[1] in 'LR' and cell[2] in 'AB':
            value = f'Some(mkTrans S{cell[0]} D{cell[1]} St{cell[2]})'
        else:
            raise ValueError('Invalid transition')
        branches.append(f'|St{chr(65+j//4)},S{j%4}=>{value}')
    out += 'Definition family:TM:=fun q s=>match q,s with ' + ''.join(branches) + ' end.\n'
    actual = '(mirror_tm family)' if g['mirror'] else 'family'
    out += f'Lemma checked: wc_graph_check 4096%N 4096%N {actual} {g["n"]}%nat {g["t"]}%nat nodes certificate=true.\nProof. vm_compute. reflexivity. Qed.\n'
    out += 'Theorem family_run: NonHalt family /\\ Bounds 4096%N 4096%N family.\nProof.\n'
    if g['mirror']:
        out += '  destruct (wc_graph_check_sound _ _ _ _ _ _ _ checked) as [Hrun Hbounds].\n  split; [apply mirror_nonhalt; exact Hrun|eapply mirror_bounds; exact Hbounds].\n'
    else:
        out += '  eapply wc_graph_check_sound; exact checked.\n'
    out += 'Qed.\nTheorem family_completions:forall tm,TM_le family tm->Bounds 4096%N 4096%N tm.\nProof. intros tm Hle; destruct family_run as[Hrun Hbounds];eapply extend_bounds;eauto. Qed.\n'
    return out
