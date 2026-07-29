"""Shadow classification for the closeout (UNTRUSTED, like everything here).

A SHADOW is an unproven frozen row whose start transition writes the blank
(A0 = 0??), so the machine runs an all-blank prefix and then IS its re-root
[TM_swap StA q*] started fresh -- and whose re-root lies in the orbit
(state swaps of non-start states, mirror, completion) of another unproven
CORE row.  Such a row is an open problem's shadow, not a new problem: the
generated SH stage proves it satisfies the [skipped] disjunct
(Closeout/ShadowKit.v), and it resolves automatically when its core row is
boarded.

classify(remaining) -> (core_rows, shadows) where each shadow is a dict:
  spec     the row text
  qs, t    the first 1-writing state and the blank-prefix length
  partner  the core row text its re-root reduces to
  ops      constructor ops, application order: [('mirror',)] / [('swap',u,v)]
The emitted ops are re-verified here (partner <= ops(swap(row))) and, of
course, by the kernel when the stage compiles.
"""
import itertools

STATES = 'ABCD'


def parse(s):
    slots = []
    for pair in s.split('_'):
        for t in (pair[:3], pair[3:]):
            slots.append(None if t == '---' else (t[0], t[1], t[2]))
    return tuple(slots)


def swap_uv(m, u, v):
    p = {st: st for st in STATES}
    p[u], p[v] = v, u
    out = [None] * 8
    for i in range(8):
        st, s = STATES[i // 2], i % 2
        src = m[STATES.index(p[st]) * 2 + s]
        out[i] = None if src is None else (src[0], src[1], p[src[2]])
    return tuple(out)


def mirror(m):
    return tuple(None if t is None else
                 (t[0], 'L' if t[1] == 'R' else 'R', t[2]) for t in m)


def le(row, m):
    return all(r is None or r == m[i] for i, r in enumerate(row))


def qstar(m):
    """(q*, t): first 1-writing state on the blank prefix, or None."""
    q, n, seen = 'A', 0, set()
    while True:
        tr = m[STATES.index(q) * 2]
        if tr is None or q in seen:
            return None
        if tr[0] == '1':
            return q, n
        seen.add(q)
        q = tr[2]
        n += 1


def apply_ops(m, ops):
    for op in ops:
        if op[0] == 'mirror':
            m = mirror(m)
        else:
            m = swap_uv(m, op[1], op[2])
    return m


# every orbit path we try: 0-2 transpositions of {B,C,D}, then optional mirror
_PAIRS = [('B', 'C'), ('B', 'D'), ('C', 'D')]
_OPS_CHOICES = [[]]
_OPS_CHOICES += [[('swap',) + p] for p in _PAIRS]
_OPS_CHOICES += [[('swap',) + p, ('swap',) + q] for p in _PAIRS for q in _PAIRS
                 if p != q]
_OPS_CHOICES = _OPS_CHOICES + [ops + [('mirror',)] for ops in _OPS_CHOICES]


def classify(remaining):
    rem_parsed = {s: parse(s) for s in remaining}
    shadows = []
    shadow_specs = set()
    for spec in remaining:
        m = rem_parsed[spec]
        if m[0] is None or m[0][0] != '0':
            continue
        qt = qstar(m)
        if qt is None or qt[0] == 'A':
            continue
        qs, t = qt
        base = swap_uv(m, 'A', qs)
        hit = None
        for ops in _OPS_CHOICES:
            v = apply_ops(base, ops)
            for pspec, prow in rem_parsed.items():
                if pspec == spec or pspec in shadow_specs:
                    continue
                # the partner must itself not be a 0RB row (no shadow chains)
                if prow[0] is not None and prow[0][0] == '0':
                    continue
                if le(prow, v):
                    hit = dict(spec=spec, qs=qs, t=t, partner=pspec, ops=ops)
                    break
            if hit:
                break
        if hit:
            assert le(rem_parsed[hit['partner']],
                      apply_ops(swap_uv(m, 'A', hit['qs']), hit['ops']))
            shadows.append(hit)
            shadow_specs.add(spec)
    core = [s for s in remaining if s not in shadow_specs]
    # partners must all be core rows
    for sh in shadows:
        assert sh['partner'] in core, sh
    return core, shadows
