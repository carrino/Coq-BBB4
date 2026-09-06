#!/usr/bin/env python3
"""UNTRUSTED: the symbolic lap engine behind theories/Checkers/LapDecider.v.

This is a faithful Python mirror of [sstep]/[srun] plus a SEARCH that derives
a certificate chain for a machine.  Nothing here is trusted -- the Coq kernel
re-runs [srun] on every emitted certificate, and a wrong chain makes [srun]
return [None] (the board then fails to compile) rather than a wrong theorem.

Why a mirror and not a re-implementation: the emitted chain must be accepted
by the Coq [sstep] verbatim, so every guard here (which side must have an
empty prefix, where a deposit lands, how [firstn]/[skipn] split a window) is
transcribed from LapDecider.v rather than re-derived.

Representation
  side  = (pre, u, a, b, post)   denoting  pre ++ rep u (a*j+b) ++ post ++ X
  conf  = (st, side_l, h, side_r)
  X     = the opaque tail; [el]/[er] say it is known empty on that side.
"""


class Halt(Exception):
    """The machine has no transition here -- not a lap."""


# --------------------------------------------------------------- windowing ---

def wstep(tab, bl, br, cfg):
    """CTape/WTape.wstep: chd [] = S0, ctl [] = []."""
    q, l, h, r = cfg
    tr = tab.get((q, h))
    if tr is None:
        raise Halt
    w, d, nq = tr
    if d > 0:                                   # DR
        if not r and br:
            return None
        return (nq, (w,) + l, r[0] if r else 0, r[1:])
    else:                                       # DL
        if not l and bl:
            return None
        return (nq, l[1:], l[0] if l else 0, (w,) + r)


def wsteps(tab, bl, br, n, cfg):
    for _ in range(n):
        cfg = wstep(tab, bl, br, cfg)
        if cfg is None:
            return None
    return cfg


def wtrace(tab, bl, br, cfg, cap):
    """Every window configuration reachable without leaving the window,
    [cfg] first.  Stops at the wall or at [cap]."""
    out = [cfg]
    for _ in range(cap):
        try:
            nxt = wstep(tab, bl, br, cfg)
        except Halt:
            break
        if nxt is None:
            break
        cfg = nxt
        out.append(cfg)
    return out


# ------------------------------------------------------------ side algebra ---

def sden_parts(side, openX):
    """Canonical (P, U, rest, openX) with denotation P ++ rep U j ++ rest ++ X:
    fold the constant part [b] of the count into the prefix and the multiplier
    [a] into the unit, then unrotate maximally so the form is unique."""
    pre, u, a, b, post = side
    P = pre + u * b
    U = u * a
    rest = post
    while U and P and P[-1] == U[-1]:
        P, U, rest = P[:-1], (U[-1],) + U[:-1], (U[-1],) + rest
    if not U:
        return (P + rest, (), (), openX)
    return (P, U, rest, openX)


def rstrip0(t):
    i = len(t)
    while i and t[i - 1] == 0:
        i -= 1
    return t[:i]


def side_eq(sa, oa, sb, ob, lift=False):
    """Do the two sides denote the same half-tape for every j?  With an empty
    opaque tail, trailing blanks are invisible ([lift]).

    [lift=False] is the SYNTACTIC test the emitted board's exact anchor glue
    needs ([gei_*] closes by [reflexivity]).  Note it only strips [rest]: when
    the side carries no rep, [sden_parts] folds everything into [P] and the
    leniency never fires -- which is exactly the end of a lap, where the
    machine has just written a blank beside the head.

    [lift=True] is the test the THEOREM needs ([LapDecider.lap_of_run] and
    [LapGlue]'s [Hlap] both ask only for [lift] equality, and
    [CTape.lift_side l = fun n => nth n l S0] cannot see a trailing blank).
    A chain accepted only under [lift=True] has to be rendered through the
    [lift] route -- see [emit_lapcert.GLUE_ONE_LIFT]."""
    Pa, Ua, Ra, _ = sden_parts(sa, oa)
    Pb, Ub, Rb, _ = sden_parts(sb, ob)
    if lift and not Ua and not Ub and not oa and not ob:
        return rstrip0(Pa + Ra) == rstrip0(Pb + Rb)
    if (Pa, Ua) != (Pb, Ub):
        return False
    if oa or ob:
        return Ra == Rb
    return rstrip0(Ra) == rstrip0(Rb)


# ------------------------------------------------- the symbolic step, mirrored ---

def _setpre(s, w):
    return (w,) + s[1:]


def _sflat(w):
    return (w, (), 0, 0, ())


def srot(m, s):
    pre, u, a, b, post = s
    v, w = u[:m], u[m:]
    if post[:len(v)] != v:
        return None
    return (pre + v, w + v, a, b, post[len(v):])


def sfold(m, s):
    """Absorb m copies of u sitting at the END of pre into the count."""
    pre, u, a, b, post = s
    blk = u * m
    if not blk or pre[len(pre) - len(blk):] != blk:
        return None
    return (pre[:len(pre) - len(blk)], u, a, b + m, post)


def sunrot(m, s):
    pre, u, a, b, post = s
    k = len(u) - m
    if k < 0:
        k = 0
    v, w = u[k:], u[:k]
    if not v or pre[len(pre) - len(v):] != v:
        return None
    return (pre[:len(pre) - len(v)], v + w, a, b, v + post)


def sstep(tab, el, er, st, c):
    """Mirror of LapDecider.sstep.  Returns (conf, ca, cb) or None."""
    q, L, h, R = c
    kind = st[0]

    if kind == 'SWin':
        n = st[1]
        res = wsteps(tab, True, True, n, (q, L[0], h, R[0]))
        if res is None:
            return None
        q2, xl, xh, xr = res
        return ((q2, _setpre(L, xl), xh, _setpre(R, xr)), 0, n)

    if kind == 'SWinL':
        n = st[1]
        if not el or L[1] or L[4]:
            return None
        res = wsteps(tab, False, True, n, (q, L[0], h, R[0]))
        if res is None:
            return None
        q2, xl, xh, xr = res
        return ((q2, _sflat(xl), xh, _setpre(R, xr)), 0, n)

    if kind == 'SWinR':
        n = st[1]
        if not er or R[1] or R[4]:
            return None
        res = wsteps(tab, True, False, n, (q, L[0], h, R[0]))
        if res is None:
            return None
        q2, xl, xh, xr = res
        return ((q2, _setpre(L, xl), xh, _sflat(xr)), 0, n)

    if kind == 'SCycL':
        n, m = st[1], st[2]
        if L[0] or R[1]:
            return None
        rw, rest = R[0][:m], R[0][m:]
        res = wsteps(tab, True, True, n, (q, L[1], h, rw))
        if res is None:
            return None
        q2, l2, h2, r2 = res
        if l2 or q2 != q or h2 != h or r2[:len(rw)] != rw:
            return None
        w = r2[len(rw):]
        return ((q, _sflat(L[4]), h, (rw, w, L[2], L[3], rest + R[4])),
                n * L[2], n * L[3])

    if kind == 'SCycR':
        n = st[1]
        if R[0] or L[1]:
            return None
        res = wsteps(tab, True, True, n, (q, (), h, R[1]))
        if res is None:
            return None
        q2, w, h2, r2 = res
        if r2 or q2 != q or h2 != h:
            return None
        return ((q, ((), w, R[2], R[3], L[0] + L[4]), h, _sflat(R[4])),
                n * R[2], n * R[3])

    if kind in ('SRotL', 'SRotR', 'SUnrotL', 'SUnrotR', 'SFoldL', 'SFoldR'):
        m = st[1]
        f = (srot if kind.startswith('SRot')
             else sfold if kind.startswith('SFold') else sunrot)
        if kind.endswith('L'):
            s = f(m, L)
            return None if s is None else ((q, s, h, R), 0, 0)
        s = f(m, R)
        return None if s is None else ((q, L, h, s), 0, 0)

    raise ValueError(kind)


def srun(tab, el, er, chain, c):
    ca = cb = 0
    for st in chain:
        r = sstep(tab, el, er, st, c)
        if r is None:
            return None
        c, a, b = r
        ca += a
        cb += b
    return c, ca, cb


# ------------------------------------------------------------------ search ---

def _cyc_candidates(tab, el, er, c, nmax):
    """Cycle steps that close: scan the unit run for a return to the same
    (state, head) with the block consumed."""
    out = []
    q, L, h, R = c
    if not L[0] and not R[1] and L[1]:
        for m in range(len(R[0]) + 1):
            rw = R[0][:m]
            cfg = (q, L[1], h, rw)
            for n in range(1, nmax + 1):
                try:
                    cfg = wstep(tab, True, True, cfg)
                except Halt:
                    break
                if cfg is None:
                    break
                q2, l2, h2, r2 = cfg
                if not l2 and q2 == q and h2 == h and r2[:len(rw)] == rw:
                    out.append(('SCycL', n, m))
                    break
    if not R[0] and not L[1] and R[1]:
        cfg = (q, (), h, R[1])
        for n in range(1, nmax + 1):
            try:
                cfg = wstep(tab, True, True, cfg)
            except Halt:
                break
            if cfg is None:
                break
            q2, w, h2, r2 = cfg
            if not r2 and q2 == q and h2 == h:
                out.append(('SCycR', n))
                break
    return out


def _rot_candidates(c):
    out = []
    q, L, h, R = c
    for m in range(1, len(L[1]) + 1):
        if srot(m, L) is not None:
            out.append(('SRotL', m))
        if sunrot(m, L) is not None:
            out.append(('SUnrotL', m))
    for m in range(1, len(R[1]) + 1):
        if srot(m, R) is not None:
            out.append(('SRotR', m))
        if sunrot(m, R) is not None:
            out.append(('SUnrotR', m))
    for m in (1, 2):
        if sfold(m, L) is not None:
            out.append(('SFoldL', m))
        if sfold(m, R) is not None:
            out.append(('SFoldR', m))
    return out


def _match(c, target, el, er, lift=False):
    q, L, h, R = c
    tq, tL, th, tR = target
    return (q == tq and h == th
            and side_eq(L, not el, tL, not el, lift)
            and side_eq(R, not er, tR, not er, lift))


def _win_candidates(tab, el, er, c, nmax, target=None, lift=False):
    """A walled window is FORCED forward, so most cuts are uninteresting.
    The ones that matter are: the MAXIMAL cut (the wall, where only a cycle
    or a rotation can make progress), any cut that lands on the target, and
    any cut at which a cycle becomes available -- a block must be consumed
    before the machine deposits fresh cells on top of it."""
    q, L, h, R = c
    out = []
    for kind, bl, br in (('SWin', True, True),
                         ('SWinL', False, True),
                         ('SWinR', True, False)):
        if kind == 'SWinL' and (not el or L[1] or L[4]):
            continue
        if kind == 'SWinR' and (not er or R[1] or R[4]):
            continue
        tr = wtrace(tab, bl, br, (q, L[0], h, R[0]), nmax)
        if len(tr) < 2:
            continue
        hit, cyc = [], []
        for k in range(1, len(tr)):
            q2, xl, xh, xr = tr[k]
            nl = _sflat(xl) if kind == 'SWinL' else _setpre(L, xl)
            nr = _sflat(xr) if kind == 'SWinR' else _setpre(R, xr)
            c2 = (q2, nl, xh, nr)
            if target is not None and _match(c2, target, el, er, lift):
                hit.append(k)
            elif k < len(tr) - 1 and _cyc_candidates(tab, el, er, c2, nmax):
                cyc.append(k)
        for k in hit + cyc + [len(tr) - 1]:
            if (kind, k) not in out:
                out.append((kind, k))
    return out


def _shape_to(c, target, el, er, budget=8, lift=False):
    """Rotate the reached configuration onto the TARGET's syntactic shape
    (same pre/u/a/b on both sides; [post] may still differ by trailing
    blanks, which [lift] absorbs).  BFS over the four rotation steps.

    The acceptance test is PER SIDE, because the two sides fail differently:
    a side whose unit run is misaligned is fixed by rotating, but no rotation
    can delete a trailing blank.  Under [lift] we therefore SCORE each config
    by how many sides reach the target's syntactic shape and take the best --
    accepting slack only where rotating cannot help.  Scoring rather than
    accepting the first denotational match matters: the reached config
    usually already DENOTES the target (that is why the chain got here at
    all), so a first-match test returns the empty rotation and leaves the rep
    side misaligned, which the board's glue cannot render."""
    def sshape(s):
        return (s[0], s[1], s[2], s[3])

    def score(cur):
        """2 = both sides in the target's shape (the exact route); 1 = one
        side, the other merely denoting it; None = not the target at all."""
        n = 0
        for i, open_ in ((1, not el), (3, not er)):
            if sshape(cur[i]) == sshape(target[i]):
                n += 1
            elif not (lift and side_eq(cur[i], open_, target[i], open_, True)):
                return None
        return n

    best = (None, None)                                   # (score, path)
    seen = {(c[1], c[3])}
    frontier = [(c, [])]
    for _ in range(budget + 1):
        if not frontier:
            break
        nxt = []
        for cur, path in frontier:
            s = score(cur)
            if s == 2:
                return path
            if s is not None and (best[0] is None or s > best[0]):
                best = (s, path)
            for st in _rot_candidates(cur):
                r = sstep(None, el, er, st, cur)
                if r is None:
                    continue
                c2 = r[0]
                key = (c2[1], c2[3])
                if key in seen:
                    continue
                seen.add(key)
                nxt.append((c2, path + [st]))
        frontier = nxt
    return best[1]


def chain_is_exact(tab, el, er, chain, c0, target):
    """Does [chain] land on [target] SYNTACTICALLY (the exact anchor glue), or
    only up to [lift] (trailing blanks)?  [None] if it lands on neither."""
    r = srun(tab, el, er, chain, c0)
    if r is None:
        return None
    if _match(r[0], target, el, er, False):
        return True
    if _match(r[0], target, el, er, True):
        return False
    return None


def derive_chain(tab, el, er, c0, target, maxdepth=24, nmax=64, lift=False):
    """Depth-first search for a chain c0 -> target.  The branching factor is
    tiny: a walled window runs until it is blocked, and at a wall only a
    cycle or a rotation can make progress."""
    best = [None]
    seen = set()

    def key(c):
        return (c[0], c[1], c[2], c[3])

    def go(c, chain, depth):
        if best[0] is not None:
            return
        if _match(c, target, el, er, lift):
            fix = _shape_to(c, target, el, er, 8, lift)
            if fix is not None:
                cand = chain + fix
                c2 = c
                for st in fix:
                    c2 = sstep(tab, el, er, st, c2)[0]
                if _match(c2, target, el, er, lift):
                    best[0] = cand
                    return
        if depth >= maxdepth:
            return
        k = key(c)
        if k in seen:
            return
        seen.add(k)
        cands = (_win_candidates(tab, el, er, c, nmax, target, lift)
                 + _cyc_candidates(tab, el, er, c, nmax)
                 + _rot_candidates(c))
        for st in cands:
            try:
                r = sstep(tab, el, er, st, c)
            except Halt:
                continue
            if r is None:
                continue
            go(r[0], chain + [st], depth + 1)
            if best[0] is not None:
                return

    try:
        go(c0, [], 0)
    except RecursionError:
        return None
    return best[0]


def _hit_in_win(tab, c, st, want):
    """The shortest cut of a window step that lands in state [want]."""
    bl = st[0] != 'SWinL'
    br = st[0] != 'SWinR'
    tr = wtrace(tab, bl, br, (c[0], c[1][0], c[2], c[3][0]), st[1])
    for k in range(1, min(st[1], len(tr) - 1) + 1):
        if tr[k][0] == want:
            return (st[0], k)
    return None


def reach_state(tab, el, er, c0, chain, want, extra=24, nmax=64):
    """A chain from [c0] landing in state [want] -- the [Hvis] witness.

    First try prefixes of the lap chain (cutting its last window short if
    need be).  A state that fires only AFTER the lap closes is still visited
    from the anchor, so if that fails, keep running the machine forward
    symbolically past the end of the lap.  Soundness does not care that the
    continuation belongs to the next lap: [vis_of_run] accepts any chain."""
    c, out = c0, []
    for st in chain:
        if c[0] == want:
            return out
        if st[0].startswith('SWin'):
            cut = _hit_in_win(tab, c, st, want)
            if cut is not None:
                return out + [cut]
        r = sstep(tab, el, er, st, c)
        if r is None:
            return None
        c = r[0]
        out.append(st)
    for _ in range(extra):
        if c[0] == want:
            return out
        cands = (_win_candidates(tab, el, er, c, nmax)
                 + _cyc_candidates(tab, el, er, c, nmax)
                 + _rot_candidates(c))
        step = None
        for st in cands:
            if st[0].startswith('SWin'):
                cut = _hit_in_win(tab, c, st, want)
                if cut is not None:
                    return out + [cut]
            if step is None:
                step = st
        if step is None:
            return None
        r = sstep(tab, el, er, step, c)
        if r is None:
            return None
        c = r[0]
        out.append(step)
    return out if c[0] == want else None


def _hit_instr_in_win(tab, c, st, want):
    """The shortest cut of a window step that lands on INSTRUCTION [want]
    (a (state, head-symbol) pair) -- the transition-level twin of
    [_hit_in_win]."""
    bl = st[0] != 'SWinL'
    br = st[0] != 'SWinR'
    tr = wtrace(tab, bl, br, (c[0], c[1][0], c[2], c[3][0]), st[1])
    for k in range(1, min(st[1], len(tr) - 1) + 1):
        if (tr[k][0], tr[k][2]) == want:
            return (st[0], k)
    return None


def reach_instr(tab, el, er, c0, chain, want, extra=24, nmax=64):
    """A chain from [c0] landing on instruction [want] = (state, head) -- the
    per-instruction [Hfire] witness of LapGlueTr.  Same search as
    [reach_state]: lap-chain prefixes (cutting the last window short), then a
    bounded symbolic continuation past the lap's end."""
    c, out = c0, []
    for st in chain:
        if (c[0], c[2]) == want:
            return out
        if st[0].startswith('SWin'):
            cut = _hit_instr_in_win(tab, c, st, want)
            if cut is not None:
                return out + [cut]
        r = sstep(tab, el, er, st, c)
        if r is None:
            return None
        c = r[0]
        out.append(st)
    for _ in range(extra):
        if (c[0], c[2]) == want:
            return out
        cands = (_win_candidates(tab, el, er, c, nmax)
                 + _cyc_candidates(tab, el, er, c, nmax)
                 + _rot_candidates(c))
        step = None
        for st in cands:
            if st[0].startswith('SWin'):
                cut = _hit_instr_in_win(tab, c, st, want)
                if cut is not None:
                    return out + [cut]
            if step is None:
                step = st
        if step is None:
            return None
        r = sstep(tab, el, er, step, c)
        if r is None:
            return None
        c = r[0]
        out.append(step)
    return out if (c[0], c[2]) == want else None
