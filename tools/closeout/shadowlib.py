"""Shadow classification for the closeout (UNTRUSTED, like everything here).

A SHADOW is an unproven frozen row whose start transition writes the blank
(A0 = 0??), so the machine runs an all-blank prefix and then IS its re-root
[TM_swap StA q*] started fresh -- and whose re-root lies in the orbit
(state swaps of non-start states, mirror, completion) of another unproven
CORE row.  Such a row is an open problem's shadow, not a new problem: the
generated SH stage proves it satisfies the [skipped] disjunct
(Closeout/ShadowKit.v), and it resolves automatically when its core row is
boarded.

classify(remaining, boarded) -> (core_rows, shadows, freed).  A shadow dict is:
  spec     the row text
  qs, t    the first 1-writing state and the blank-prefix length
  partner  the row text its re-root reduces to
  ops      constructor ops, application order: [('mirror',)] / [('swap',u,v)]
The emitted ops are re-verified here (partner <= ops(swap(row))) and, of
course, by the kernel when the stage compiles.

THE PARTNER POOL IS THE POINT.  A shadow satisfies the [skipped] disjunct
only while its partner is still DEFERRED, so the moment the partner boards
this row stops being a shadow and needs a board of its own -- which is
exactly when the transport becomes buildable.  Searching only `remaining`
therefore loses the link at the one moment it is worth something: the row
falls out of `shadow_rows.tsv` into `core_rows.txt` carrying none of the
(qs, t, partner, ops) needed to board it, and someone has to dig them out of
the previous revision of the table by hand.  #104 did exactly that, twice.

So the pool is `remaining` PLUS `boarded`, and the split is three ways:
  shadows  partner still deferred  -> rides the skipped disjunct, no board
  freed    partner already boarded -> ACTIONABLE: gen_shadow.py --harvest
  core     everything else
A freed row is still unproven, so it is also in `core_rows.txt` -- `freed` is
an annotation on part of the core, not a fourth table, and the audit's
partition invariant is untouched.  Harvesting one boards it and it leaves
both lists on the next inventory pass.

A boarded partner is preferred over a deferred one: both are true, but only
the first settles the row instead of deferring it.
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


def _search(m, qs, pool, exclude):
    """First (ops, partner) in `pool` whose row the re-root completes to.

    `pool` is a list of (spec, parsed).  Ops are tried shortest-first, so a
    row that matches with no relabelling at all is reported that way.
    """
    base = swap_uv(m, 'A', qs)
    for ops in _OPS_CHOICES:
        v = apply_ops(base, ops)
        for pspec, prow in pool:
            if pspec in exclude:
                continue
            # the partner must itself not be a 0RB row (no shadow chains)
            if prow[0] is not None and prow[0][0] == '0':
                continue
            if le(prow, v):
                return ops, pspec
    return None


def classify(remaining, boarded=None):
    """Split `remaining` into core rows, live shadows, and freed shadows.

    `boarded` maps an already-settled row's spec to its board kind
    ('nqh' / 'iqh' / 'iqhle:<B>'), as `frozen_map.tsv` records it; pass None
    or {} for the pre-#105 behaviour of searching deferred partners only.
    """
    boarded = boarded or {}
    rem_parsed = {s: parse(s) for s in remaining}
    brd_parsed = [(s, parse(s)) for s in sorted(boarded)]
    rem_pool = sorted(rem_parsed.items())

    shadows, freed = [], []
    shadow_specs = set()
    for spec in remaining:
        m = rem_parsed[spec]
        if m[0] is None or m[0][0] != '0':
            continue
        qt = qstar(m)
        if qt is None or qt[0] == 'A':
            continue
        qs, t = qt
        # A boarded partner is preferred: it settles the row rather than
        # deferring it.  A shadow may never be another shadow's partner, and
        # never itself.
        exclude = shadow_specs | {spec}
        hit, where = None, None
        for pool, tag in ((brd_parsed, 'freed'), (rem_pool, 'shadow')):
            r = _search(m, qs, pool, exclude)
            if r:
                ops, pspec = r
                hit = dict(spec=spec, qs=qs, t=t, partner=pspec, ops=ops)
                where = tag
                break
        if not hit:
            continue
        assert le(parse(hit['partner']),
                  apply_ops(swap_uv(m, 'A', hit['qs']), hit['ops'])), hit
        if where == 'shadow':
            shadows.append(hit)
            shadow_specs.add(spec)
        else:
            hit['partner_kind'] = boarded[hit['partner']]
            freed.append(hit)
    core = [s for s in remaining if s not in shadow_specs]
    # a live shadow's partner must be an undecided core row; a freed one's
    # must NOT be -- that is what makes it freed
    for sh in shadows:
        assert sh['partner'] in core, sh
    for fr in freed:
        assert fr['partner'] not in remaining, fr
        assert fr['spec'] in core, fr
    return core, shadows, freed
