#!/usr/bin/env python3
"""Validate remaining per-instruction search summaries and core conjugacies.

These files are search diagnostics, not Coq certificates or coverage claims.
Use --verify-spec SPEC to rerun the recorded successful target searches for
one row with their original windows, orientations and pattern bounds.
"""
import argparse
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(HERE / 'le6'))
from conj_check import parse, render, conj


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--verify-spec')
    args = parser.parse_args()
    records = list(map(json.loads, (HERE / 'blocklists_combined_partial.jsonl').read_text().splitlines()))
    baseline = {r['spec']: r for r in map(json.loads, (HERE / 'blocklists114_partial.jsonl').read_text().splitlines())}
    remaining = set((ROOT / 'closeouttr_remaining.txt').read_text().splitlines())
    by_spec = {r['spec']: r for r in records}
    assert len(by_spec) == len(records)
    for r in records:
        assert r['spec'] in remaining
        b = baseline[r['spec']]
        assert r['base_n'] == b['n'] == 3 and r['base_mirrored'] == b['mirrored']
        assert r['base_uncertified'] == b['failed']
        base = {tuple(q) for q in b['failed']}
        found = set()
        for c in r['certified']:
            assert tuple(c['target']) in base and c['finder'] in ('ordinary', 'combined')
            assert 3 <= c['n'] <= (6 if c['finder'] == 'combined' else 7)
            assert c['t'] == 0 and isinstance(c['mirrored'], bool)
            found.add(tuple(c['target']))
        assert r['missing'] == [q for q in b['failed'] if tuple(q) not in found]
    cores = json.loads((HERE / 'blocklists_combined_cores.json').read_text())
    seen = set()
    for core in cores:
        for row in core['rows']:
            spec = row['spec']
            assert spec not in seen
            seen.add(spec)
            r = by_spec[spec]
            target = ('ABCD'.index(row['target'][0]), int(row['target'][1]))
            assert r['missing'] == [list(target)]
            p = row['to_core']
            assert sorted(p) == list(range(4))
            table = parse(spec)
            table[target] = None
            assert render(conj(table, p, row['flip'])) == core['core']
    assert seen == {r['spec'] for r in records if len(r['missing']) == 1}
    print(f'Checked {len(records)} partial summaries; {len(seen)} single-target rows in {len(cores)} cores')
    if args.verify_spec:
        r = by_spec[args.verify_spec]
        import fuelcombinedtr_batch as combined
        ft = combined.ft
        for c in r['certified']:
            chooser = combined.choose_mix if c['finder'] == 'combined' else combined.fm.choose_mix
            tbl = ft.bp.parse(ft.gf.mirror_mtext(r['spec']) if c['mirrored'] else r['spec'])
            n = c['n']
            _, ls, rs, a0, _ = ft.bp.build_closure(tbl, n, 0)
            nodes = ft.gf.build_fw_closure(tbl, ls, rs, (a0, 0, 0))
            adj = ft.gf.fw_adj(tbl, ls, rs, nodes)
            candidates = ft.pattern_candidates(n, 6 if c['finder'] == 'combined' else 8)
            target = tuple(c['target'])
            result = ft.instruction_procedure.func(tbl, n, adj, nodes, target, candidates,
                                                   ft.make_pattern_delta(tbl, n), chooser)
            assert result is not None and ft.instruction_check(tbl, n, adj, nodes, target, *result)
            print('Replayed target', c['target'], 'at window', n, 'with', c['finder'])


if __name__ == '__main__':
    main()
