#!/usr/bin/env python3
"""Bounded, untrusted RepWL nomination; generated Coq rechecks every result.

At most 100 residual rows, 1000 abstract nodes, size cut 64, anchors <=64,
L in 1..3 and T=2. No qualitative measure certificates are accepted.
Failure records are retained in TSV. Coq replay is a separate required step.
"""
import argparse
import csv
import importlib.util
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('repwl_untrusted', ROOT / 'tools/repwl_prover.py')
rw = importlib.util.module_from_spec(spec)
spec.loader.exec_module(rw)


def probe(machine, block, anchor, cap=1000, size=64):
    tbl = rw.parse(machine)
    start = rw.seed(tbl, block, 2, anchor)
    if start is None:
        return 'halted-anchor', 0
    graph, todo = {}, [start]
    while todo:
        a = todo.pop()
        if a in graph:
            continue
        if len(graph) >= cap:
            return 'node-cap', len(graph)
        if sum(map(len, (a[1], a[2], a[4], a[5]))) > size:
            return 'size-cut', len(graph)
        sl = rw.rw_succs(tbl, block, 2, a)
        if sl is None:
            return 'open-successor', len(graph)
        graph[a] = sl
        todo.extend(sl)
    for q in sorted({a[0] for a in graph}):
        remaining = {a for a in graph if a[0] != q}
        ranked = set()
        while remaining:
            ready = {a for a in remaining if all(b[0] == q or b in ranked for b in graph[a])}
            if not ready:
                return 'avoiding-cycle', len(graph)
            remaining -= ready
            ranked |= ready
    return 'nominated', len(graph)


def coq_tm(machine):
    cases = []
    for (q, s), tr in rw.parse(machine).items():
        value = 'None' if tr is None else 'Some (mkTrans S%d D%s St%s)' % (tr[0], tr[1], chr(65+tr[2]))
        cases.append('| St%s, S%d => %s' % (chr(65+q), s, value))
    return 'fun q s => match q, s with\n' + '\n'.join(cases) + '\nend'


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--input', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--limit', type=int, default=100, choices=range(1,101))
    args = p.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    rows = list(csv.DictReader(args.input.open(), delimiter='\t'))[:args.limit]
    records, nominated = [], []
    for index, row in enumerate(rows):
        hit = None
        for anchor in (0, 16, 64):
            for block in (1, 2, 3):
                status, nodes = probe(row['machine'], block, anchor)
                records.append(dict(index=index, machine=row['machine'], block=block, anchor=anchor, status=status, nodes=nodes))
                if status == 'nominated':
                    hit = (index, row['machine'], block, anchor, nodes)
                    break
            if hit:
                break
        if hit:
            nominated.append(hit)
    with (args.output / 'attempts.tsv').open('w') as f:
        w = csv.DictWriter(f, records[0].keys(), delimiter='\t'); w.writeheader(); w.writerows(records)
    coq = ['From Coq Require Import Arith Lia.', 'From BBB4 Require Import BBB4_Statement.', 'From BBBWait42 Require Import Spec RepeatedWord.']
    for index, machine, block, anchor, nodes in nominated:
        fuel, width = 2*nodes+8, nodes+1
        coq += [f'Definition residual_{index} : TM := {coq_tm(machine)}.',
                f'Example residual_{index}_checked : repwl_ranked_search residual_{index} {block} 2 64 {anchor} {fuel} {width} = true.',
                'Proof. vm_compute. reflexivity. Qed.',
                f'Theorem residual_{index}_window : forall B, {anchor} <= B -> WindowBound residual_{index} B {width}.',
                f'Proof. intros B HB. eapply repwl_ranked_search_sound; [exact HB|exact residual_{index}_checked]. Qed.']
    (args.output / 'Replay.v').write_text('\n'.join(coq)+'\n')
    (args.output / 'summary.json').write_text(json.dumps(dict(rows=len(rows), attempts=len(records), nominations=len(nominated), limits=dict(nodes=1000,size=64,anchors=[0,16,64],blocks=[1,2,3],threshold=2), replay='required; nominations are not proofs'),indent=2)+'\n')
    print((args.output / 'summary.json').read_text())


if __name__ == '__main__':
    main()
