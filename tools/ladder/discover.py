#!/usr/bin/env python3
"""UNTRUSTED: ladder rule discovery -- mine recurring LOCAL shapes from the
trace, generalize with fresh variables, prove by symbolic replay (rung 2:
the replay may apply already-proven rules).  Local rules bind a bounded
window near the head; the abstract rest sits behind a MARKER whose pop
fails the replay, so a proven local rule is sound for every context."""

from collections import defaultdict

from engine import (Expr, MARKER, Replay, Rule, cfg_key, cfg_counts,
                    cfg_with_counts)


def local_view(cfg, m):
    q, h, L, R = cfg
    L2 = L[:m] + ((MARKER, Expr(1)),) if len(L) > m else L
    R2 = R[:m] + ((MARKER, Expr(1)),) if len(R) > m else R
    return (q, h, L2, R2)


def mine_shapes(snaps, windows=(1, 2, 3)):
    """shape key -> list of (t, counts tuple of ints, view cfg)."""
    table = defaultdict(list)
    for t, snap in snaps:
        if snap is None:
            break
        seen = set()
        for m in windows:
            v = local_view(snap, m)
            k = cfg_key(v)
            if k in seen:
                continue
            seen.add(k)
            table[k].append((t, tuple(e.c for e in cfg_counts(v)), v))
    return table


def candidates(table, min_occ=3, max_cands=2000):
    cands = []
    for key, occ in table.items():
        if len(occ) < min_occ:
            continue
        by_delta = defaultdict(list)
        for a, b in zip(occ, occ[1:]):
            d = tuple(y - x for x, y in zip(a[1], b[1]))
            if any(d):
                by_delta[d].append((a, b))
        for d, pairs in by_delta.items():
            if len(pairs) >= 2:
                cands.append((key, d, pairs))
    def order(c):
        key, d, _ = c
        words = key[2] + key[3]
        local = 0 if any(w == MARKER for w in words) else 1
        return (local, len(words), sum(abs(x) for x in d))
    cands.sort(key=order)
    return cands[:max_cands]


def generalize(key, delta, pairs):
    firsts = [a[1] for a, _ in pairs]
    n = len(delta)
    counts_l, counts_r, varmap = [], [], {}
    vi = 0
    for i in range(n):
        vals = set(f[i] for f in firsts)
        if delta[i] != 0 or len(vals) > 1:
            v = 'u%d' % vi
            vi += 1
            varmap[v] = i
            counts_l.append(Expr(0, {v: 1}))
            counts_r.append(Expr(delta[i], {v: 1}))
        else:
            counts_l.append(Expr(firsts[0][i]))
            counts_r.append(Expr(firsts[0][i] + delta[i]))
    proto = pairs[0][0][2]
    lhs = cfg_with_counts(proto, counts_l)
    rhs = cfg_with_counts(proto, counts_r)
    return lhs, rhs, varmap


def prove(tm, rules, lhs, rhs, budget=200):
    """->+ replay.  Forced first concrete step guarantees progress; the rest
    may use chains and earlier rules.  Returns (lbs, fired) or None."""
    rep = Replay(tm, rules, budget=budget)
    cur = rep.step(lhs)
    if cur is None:
        return None
    out = rep.run(cur, target=rhs)
    if out is None:
        return None
    return rep.lbs, rep.fired


def redundant(tm, rules, lhs, rhs):
    """A SINGLE application of an existing rule maps lhs to rhs?  Then the
    candidate is a specialization and adds nothing.  (Step/chain
    derivability must NOT count: that is just provability, which is the
    point of the candidate.)"""
    for ru in rules:
        rep = Replay(tm, [], budget=4, raise_ok=False)
        out = rep.apply_rule(ru, lhs, bulk=False)
        if out is not None and out == rhs:
            return True
    return False


def build_ladder(tm, table, max_rules=60, rounds=5, verbose=False,
                 time_cap=300.0):
    import time
    t0 = time.time()
    cands = candidates(table)
    rules = []
    done = set()
    for rnd in range(rounds):
        new = 0
        for key, delta, pairs in cands:
            if time.time() - t0 > time_cap:
                if verbose:
                    print('  [time cap hit, partial ladder]')
                return _prune(tm, rules)
            sig = (key, delta)
            if sig in done or len(rules) >= max_rules:
                continue
            lhs, rhs, varmap = generalize(key, delta, pairs)
            if redundant(tm, rules, lhs, rhs):
                done.add(sig)
                continue
            got = prove(tm, rules, lhs, rhs)
            if got is None:
                continue
            lbs, fired = got
            dec = None
            negs = [i for i, d in enumerate(delta) if d < 0]
            if len(negs) == 1 and delta[negs[0]] == -1:
                if not cfg_counts(lhs)[negs[0]].is_const():
                    dec = negs[0]
            rule = Rule('r%d' % len(rules), lhs, rhs, lbs, dec, fired,
                        level=rnd)
            rules.append(rule)
            done.add(sig)
            new += 1
            if verbose:
                print('  proved %r' % rule)
        if new == 0:
            break
    return _prune(tm, rules)


def _prune(tm, rules):
    """Drop rules that are pure specializations of the survivors."""
    kept = []
    for ru in rules:
        if redundant(tm, kept, ru.lhs, ru.rhs):
            continue
        kept.append(ru)
    return kept


def coverage(rules, snaps, windows=(1, 2, 3), tail=2000):
    """Fraction of trailing snapshots matched by some rule lhs -- a proxy
    for closure of the rule system over the late run."""
    from engine import match_rule
    hits = 0
    tot = 0
    for t, snap in snaps[-tail:]:
        if snap is None:
            break
        tot += 1
        ok = False
        for m in windows:
            v = local_view(snap, m)
            for ru in rules:
                if match_rule(ru, v) is not None:
                    ok = True
                    break
            if ok:
                break
        if ok:
            hits += 1
    return hits, tot
