#!/usr/bin/env python3
"""Emit/replay AST148 using exact count parity and normalized extents.

The graph refines each side into zero, one, even >=2, and odd >=3.
All four classes retain their raw tags in certificate keys. The common
extent generator supplies the search, integer replay and source hashes;
FuelParityMixTr independently checks the proposals in Coq.
"""
from pathlib import Path
import block_extent_batch as base


def parity_update(count, pop_one, push_one):
    if push_one:
        return [[1], [2], [3], [2]][count]
    if not pop_one:
        return [count]
    return [[], [0], [1, 3], [2]][count]


def emit(records):
    preamble, entries = [], []
    for i, record in enumerate(records):
        name = f'cert_AST_148_{i:04d}'
        preamble.append(f'Definition {name}:Instr->list xfmcomp*list positive :=\n{record["cert"]}.')
        proof = 'apply coversTr_nqh. '
        if record['mirrored']:
            proof += 'apply neverqhtr_mirror. '
        proof += (f'apply(ngram_check_neverqh_fuelparitymixtr_except_sound _ '
                  f'{record["n"]} {record["t"]} {record["fuel"]} {record["rounds"]} '
                  f'(fun _=>false) {name}).\n'
                  '  - intros q H;discriminate.\n  - vm_compute;reflexivity.')
        entries.append((record['spec'], proof))
    return base.cbt.write_batch('AST', 148,
        ['From BBB4.Checkers Require Import NGram FuelExactMixTr FuelParityMixTr.',
         'From BBB4.CensusTr Require Import TNF_QHTr.'], entries,
        'exact nonblank-count parity, normalized extents and pattern complements',
        preamble='\n\n'.join(preamble))


def main():
    base.BATCH = 148
    base.DATA = Path(__file__).with_name('block_parity_ast.json')
    base.exact_update = parity_update
    base.emit = emit
    base.__doc__ = __doc__
    base.main()


if __name__ == '__main__':
    main()
