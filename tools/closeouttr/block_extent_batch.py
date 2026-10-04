#!/usr/bin/env python3
"""Emit/replay AST147: exact capped counts and normalized tape extents.

Finder proposals are untrusted. Integer replay checks each component;
FuelExactMixTr checks the exact abstract graph and all inequalities in Coq.
Certificate payloads live only in the Coq batch. --check verifies their
hashes and byte-for-byte regeneration; --find reruns certificate search.
"""
import argparse
import hashlib
import itertools
import json
from pathlib import Path
import tempfile
import cbt

HERE = Path(__file__).resolve().parent
DATA = HERE / 'block_extent_ast.json'
BATCH = 147


class ExactContext(tuple):
    """Preserve the exact side classes for extent-delta evaluation."""
    def __new__(cls, base, fl, fr):
        obj = tuple.__new__(cls, base)
        obj.fl, obj.fr = fl, fr
        return obj

    def __hash__(self):
        return hash((tuple(self), self.fl, self.fr))

    def __eq__(self, other):
        return (type(other) is ExactContext and
                (self.fl, self.fr) == (other.fl, other.fr) and
                tuple.__eq__(self, other))

    def __lt__(self, other):
        return ((tuple(self), self.fl, self.fr) <
                (tuple(other), other.fl, other.fr))


def exact_update(count, pop_one, push_one):
    if push_one:
        return [min(count + 1, 2)]
    if not pop_one:
        return [count]
    return [] if count == 0 else ([0] if count == 1 else [1, 2])


def exact_closure(ft, table, left, right, anchor, projection, cap=400000):
    seen, todo, adjacency = set(), [(anchor, 0, 0)], {}
    while todo:
        node = todo.pop()
        if node in seen:
            continue
        seen.add(node)
        if len(seen) > cap:
            raise RuntimeError('exact closure exceeds context cap')
        base, fl, fr = node
        write, direction, _ = table[base[:2]]
        if direction == 'R':
            left_classes = exact_update(fl, False, write == 1)
            right_classes = exact_update(fr, base[3][0] == 1, False)
        else:
            left_classes = exact_update(fl, base[2][0] == 1, False)
            right_classes = exact_update(fr, False, write == 1)
        successors = []
        for target in ft.bp.succs(table, left, right, projection, base):
            for lclass, rclass in itertools.product(left_classes, right_classes):
                if min(sum(target[2]), 2) > lclass or min(sum(target[3]), 2) > rclass:
                    continue
                successor = target, lclass, rclass
                successors.append(successor)
                todo.append(successor)
        adjacency[node] = successors
    def context(node):
        base, fl, fr = node
        return ExactContext(base, fl, fr), fl, fr
    return ({context(node) for node in seen},
            {context(node): [context(target) for target in successors]
             for node, successors in adjacency.items()})


def make_delta(base_delta):
    def delta(table, n, pattern, region, node):
        if region in ('EL', 'ER', 'NEL', 'NER'):
            side = region[-1]
            write, direction, _ = table[node[:2]]
            count = node.fl if side == 'L' else node.fr
            pushing = (side == 'L') == (direction == 'R')
            change = int(count > 0 or write == 1) if pushing else -int(count > 0)
            if region.startswith('N'):
                change -= base_delta(table, n, pattern, side, node)
            return change
        return base_delta(table, n, pattern, region, node)
    return delta


def emit_certificate(ft, per_target):
    def measure(pattern, region):
        if region in ('EL', 'ER'):
            return f'XFExtent {str(region == "EL").lower()}'
        if region in ('NEL', 'NER'):
            return f'XFComplement {str(region == "NEL").lower()} {ft.gf.gb.coq_patt(pattern)}'
        return f'XFPatt {ft.gf.gb.coq_patt(pattern)} Rg{region}'
    def component(comp):
        if comp[0] == 'rank':
            return 'XFMRk\n    ' + ft.gf.emit_fphi(comp[1])
        if comp[0] == 'mix':
            _, terms, _, scale, phi, gate = comp
        else:
            _, pattern, region, scale, phi, gate = comp
            terms = [(1, pattern, region)]
        terms_text = '; '.join(f'({ft.gf.gb.fmt_nat(w)}, {measure(p, r)})'
                               for w, p, r in terms)
        return (f'XFMSum [{terms_text}] {ft.gf.gb.fmt_nat(scale)}\n'
                f'    {ft.gf.emit_fphi(phi)}\n    {ft.gf.emit_fkeys(gate)}')
    arms = []
    for target in itertools.product(range(4), range(2)):
        components, gate = per_target[target]
        body = '[' + ';\n   '.join(map(component, components)) + ']'
        q, s = target
        arms.append(f'  | (St{chr(65+q)}, S{s}) => ({body},\n   {ft.gf.emit_fkeys(gate)})')
    return 'fun target : Instr => match target with\n' + '\n'.join(arms) + '\n  end'


def find_records(records):
    import fuelcombinedtr_batch as combined
    ft = combined.ft
    previous_delta = ft.bp.pdelta
    delta = make_delta(previous_delta)
    ft.bp.pdelta = delta
    try:
        for record in records:
            n = record['n']
            assert record['t'] == 0  # exact_closure starts with empty side counts
            spec = ft.gf.mirror_mtext(record['spec']) if record['mirrored'] else record['spec']
            table = ft.bp.parse(spec)
            projection, left, right, anchor, _ = ft.bp.build_closure(table, n, 0)
            nodes, adjacency = exact_closure(ft, table, left, right, anchor, projection)
            basic = ft.pattern_candidates(n, record['max_pattern'])
            candidates = basic + [((2,), side) for side in ('EL', 'ER')]
            candidates += [(p, 'NE' + region) for p, region in basic if region in ('L', 'R')]
            certificate = {}
            for target in itertools.product(range(4), range(2)):
                result = ft.instruction_procedure(table, n, adjacency, nodes, target,
                    candidates, lambda p, r, a: delta(table, n, p, r, a))
                if result is None:
                    raise RuntimeError(f'{record["spec"]}: missing target {target}')
                assert ft.instruction_check(table, n, adjacency, nodes, target, *result)
                certificate[target] = result
            record.update(cert=emit_certificate(ft, certificate), fuel=8*len(nodes)+64,
                          rounds=len(left)+len(right)+4, contexts=len(nodes))
            record['certificate_sha256'] = hashlib.sha256(record['cert'].encode()).hexdigest()
            print('found all targets:', record['spec'], flush=True)
    finally:
        ft.bp.pdelta = previous_delta


def emit(records):
    preamble, entries = [], []
    for i, record in enumerate(records):
        name = f'cert_AST_{BATCH}_{i:04d}'
        preamble.append(f'Definition {name}:Instr->list xfmcomp*list positive :=\n{record["cert"]}.')
        proof = 'apply coversTr_nqh. '
        if record['mirrored']:
            proof += 'apply neverqhtr_mirror. '
        proof += (f'apply(ngram_check_neverqh_fuelexactmixtr_except_sound _ '
                  f'{record["n"]} {record["t"]} {record["fuel"]} {record["rounds"]} '
                  f'(fun _=>false) {name}).\n'
                  '  - intros q H;discriminate.\n  - vm_compute;reflexivity.')
        entries.append((record['spec'], proof))
    return cbt.write_batch('AST', BATCH,
        ['From BBB4.Checkers Require Import NGram FuelExactMixTr.',
         'From BBB4.CensusTr Require Import TNF_QHTr.'], entries,
        'exact capped counts, normalized extents and pattern complements',
        preamble='\n\n'.join(preamble))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    parser.add_argument('--find', action='store_true')
    args = parser.parse_args()
    assert not (args.check and args.find)
    records = json.loads(DATA.read_text())
    target = Path(cbt.batch_path('AST', BATCH))
    if args.find:
        find_records(records)
    else:
        source = target.read_text()
        for i, record in enumerate(records):
            start = f'Definition cert_AST_{BATCH}_{i:04d}:Instr->list xfmcomp*list positive :=\n'
            record['cert'] = source.split(start, 1)[1].split('\n  end.', 1)[0] + '\n  end'
            assert hashlib.sha256(record['cert'].encode()).hexdigest() == record['certificate_sha256']
    with tempfile.TemporaryDirectory() as tmp:
        cbt.CT = tmp
        generated = Path(emit(records)).read_text()
    if args.check:
        assert target.read_text() == generated
    else:
        target.write_text(generated)
    if args.find:
        DATA.write_text(json.dumps([{k: v for k, v in r.items() if k != 'cert'}
                                    for r in records], indent=2) + '\n')
    print(('checked' if args.check else 'wrote'), target)


if __name__ == '__main__':
    main()
