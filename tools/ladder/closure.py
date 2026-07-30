#!/usr/bin/env python3
"""UNTRUSTED: the closure layer -- from a recurring anchor shape, replay
with the full ladder until the anchor SHAPE recurs with an affine map on
its counts; check the map is inward; read liveness off the fired sets.

This is the meta-cycle of irules, at the LOCAL level, with the ladder
available.  A closure here + boot simulation = a never-QH / QH certificate
CANDIDATE (Stage B is the kernel checker).

Status: skeleton with the anchor search and one-cycle symbolic replay.
The counter rows need value-indexed anchor families (octave maps), which
is the next increment -- see LADDER_PLAN.md Stage-A findings.
"""

from collections import defaultdict

from engine import Expr, Replay, cfg_key, cfg_counts, cfg_with_counts


def anchor_candidates(table, top=8):
    """Most frequent GLOBAL shapes (no marker), largest occurrence lists
    first, with strictly growing total counts (a real anchor grows)."""
    out = []
    for key, occ in table.items():
        if any(w == ('#',) for w in key[2] + key[3]):
            continue
        if len(occ) < 4:
            continue
        tot = [sum(c) for _, c, _ in occ]
        if all(b >= a for a, b in zip(tot, tot[1:])):
            out.append((len(occ), key, occ))
    out.sort(reverse=True)
    return out[:top]


def fit_affine(occ):
    """Fit x_i' = a_i * x_i + b_i over consecutive occurrence pairs.
    Returns list of (a_i, b_i) or None."""
    if len(occ) < 3:
        return None
    n = len(occ[0][1])
    maps = []
    for i in range(n):
        xs = [c[i] for _, c, _ in occ]
        pairs = list(zip(xs, xs[1:]))
        (x0, y0), (x1, y1) = pairs[0], pairs[1]
        if x1 == x0:
            if y1 != y0:
                return None
            a, b = 1, y0 - x0
        else:
            if (y1 - y0) % (x1 - x0):
                return None
            a = (y1 - y0) // (x1 - x0)
            b = y0 - a * x0
        if a < 0:
            return None
        if any(y != a * x + b for x, y in pairs):
            return None
        maps.append((a, b))
    return maps


def close_cycle(tm, rules, occ, maps, budget=2000):
    """Symbolic replay from the generalized anchor C(x) to C(f(x)).
    Returns (lbs, fired) or None."""
    proto = occ[0][2]
    n = len(cfg_counts(proto))
    counts = [Expr(0, {'x%d' % i: 1}) for i in range(n)]
    start = cfg_with_counts(proto, counts)
    tgt_counts = [Expr(maps[i][1], {'x%d' % i: maps[i][0]}) for i in range(n)]
    target = cfg_with_counts(proto, tgt_counts)
    rep = Replay(tm, rules, budget=budget)
    cur = rep.step(start)
    if cur is None:
        return None
    out = rep.run(cur, target=target)
    if out is None:
        return None
    return rep.lbs, rep.fired


def inward(maps, lbs_x, x0):
    """f maps [xmin, inf) into itself and is not the identity."""
    ident = all((a, b) == (1, 0) for a, b in maps)
    if ident:
        return False
    for (a, b), xm, x in zip(maps, lbs_x, x0):
        if x < xm or a * xm + b < xm:
            return False
    return True


def try_close(tm, rules, table):
    """Attempt closure at each anchor candidate; returns a dict verdict."""
    for cnt, key, occ in anchor_candidates(table):
        maps = fit_affine(occ)
        if maps is None:
            continue
        got = close_cycle(tm, rules, occ, maps)
        if got is None:
            continue
        lbs, fired = got
        x0 = occ[0][1]
        lbs_x = [lbs.get('x%d' % i, 1) for i in range(len(maps))]
        if not inward(maps, lbs_x, x0):
            continue
        states = set('ABCD'[t[0]] for t in fired)
        return {'closed': True, 'anchor_occ': cnt,
                'anchor_t0': occ[0][0], 'maps': maps,
                'cycle_states': ''.join(sorted(states))}
    return {'closed': False}
