#!/usr/bin/env python3
"""Render the finite A1 potential table; Coq checks its inequalities.

The certificate gives a nonnegative context bias. Adding four times the
number of 1s and three times the right-stack length strictly decreases on
every invariant-preserving step that avoids A1, apart from the empty B0
reset, which reaches A1 directly. No optimizer is needed to verify/rebuild.
"""
import argparse
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
BEGIN = "(* BEGIN GENERATED A1 RANK CERTIFICATE *)"
END = "(* END GENERATED A1 RANK CERTIFICATE *)"


def render():
    rows = json.loads(Path(__file__).with_suffix('.json').read_text())
    lines = [BEGIN,
             'Definition bmfr_bias(q:St)(h a b c:Sym)(s:bm_dfa):Z:=match q,h,a,b,c,s with']
    seen = set()
    for q, h, a, b, c, state, value in rows:
        key = q, h, a, b, c, state
        assert key not in seen
        seen.add(key)
        assert q in range(4) and state in range(19) and value >= 0
        assert all(bit in (0, 1) for bit in (h, a, b, c))
        lines.append(f'|St{"ABCD"[q]},S{h},S{a},S{b},S{c},M{state}=>{value}')
    lines += ['|_,_,_,_,_,_=>12 end.', END]
    return '\n'.join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    path = ROOT / 'theories/Counters/BlockCoreMFireRankTr.v'
    old = path.read_text()
    start, stop = old.index(BEGIN), old.index(END) + len(END)
    new = old[:start] + render() + old[stop:]
    if args.check:
        if old != new:
            raise SystemExit('M A1 rank certificate is stale')
        print('M A1 rank certificate is current')
    else:
        path.write_text(new)


if __name__ == '__main__':
    main()
