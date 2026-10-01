#!/usr/bin/env python3
"""LE4 (UNTRUSTED measurement): where a `pos_detect.py` family's FILL stops.

    python3 fill_probe.py CERTS.jsonl [SPEC...]

For widths k = 1..6, the concrete fill `pre t^k T -> pre fill_apply(k) T`
(both tails known empty): whether a chain reaches it (up to blanks) and its
step count.  `affine` = the costs grow by a constant, `exp` = they grow
geometrically (the fill runs a counter of its own: a second phase the
finder dropped as transient visits), `none` = no chain at some width (the
fill law is misread)."""
import json
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'ladder'))
import emit_ladder as E  # noqa: E402
import nest  # noqa: E402


def target(c, k):
    f = c['fill']
    w = k + f['widens_by']
    m = len(f['target_prefix']) + len(f['target_suffix'])
    if m > w:
        return None
    return f['target_prefix'] + [f['target_fill_digit']] * (w - m) + f['target_suffix']


def probe(c, kmax=6):
    f = c['family']
    tab = E.parse_tm(c['spec'])
    digs = [tuple(d) for d in f['digits']]
    b = f['base']
    pre, T = tuple(f['near_head_prefix']), tuple(f['terminator'])
    q, hs, left = ord(f['state']) - 65, f['head'], f['side'] == 'L'
    OTHER = (tuple(f['other_side_cells']), (), 0, 0, ())

    def conf(cells):
        sd = (tuple(cells), (), 0, 0, ())
        return (q, sd, hs, OTHER) if left else (q, OTHER, hs, sd)
    costs = []
    for k in range(1, kmax + 1):
        tg = target(c, k)
        if tg is None:
            costs.append(None)
            continue
        c0 = conf(pre + digs[b - 1] * k + T)
        c1 = conf(pre + tuple(x for d in tg for x in digs[d]) + T)
        ch = E.LC.derive_chain(tab, True, True, c0, c1, maxdepth=40, nmax=4000, lift=True)
        got = E.LC.srun(tab, True, True, ch, c0) if ch else None
        ok = got is not None and (got[0] == c1 or nest.ceqL(True, True, got[0], c1))
        costs.append(got[2] if ok else None)
    good = [x for x in costs if x is not None]
    if len(good) < len(costs) or len(good) < 4:
        v = 'none'
    else:
        d = [y - x for x, y in zip(good, good[1:])]
        v = 'affine' if len(set(d[1:])) <= 2 and max(d) < 3 * min(d) + 8 else 'exp'
    return v, costs


if __name__ == '__main__':
    certs = {json.loads(l)['spec']: json.loads(l) for l in open(sys.argv[1]) if l.strip()}
    for s in (sys.argv[2:] or sorted(certs)):
        v, cs = probe(certs[s])
        print(s, v, cs, flush=True)
