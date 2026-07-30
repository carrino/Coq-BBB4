#!/usr/bin/env python3
"""UNTRUSTED: turn a valfam ARM into the shape Checkers/LadderKernel.v checks.

An arm is emitted by `valfam.close` as a pair of configuration reprs plus an
affine step count:

    B[0] L<10^1+y0 1^2+y1 10^1+y2> R<>  ==>  B[0] L<1^3+2*y0 0^1 1^y1 10^1+y2> R<>

[LapDecider.sconf] denotes a side as `pre ++ rep u (a*j+b) ++ post ++ X`, one
repeated block and one opaque tail.  An arm with several variable runs still
fits that shape, because the arm is LOCAL: every variable run the arm does not
TOUCH is part of the tail.  So the normalisation here is

  1. strip the longest common suffix of the two run lists -- that is X (a run
     shared up to a constant difference is split, the shared part joining X);
  2. in what is left, exactly one run may carry a variable, and it is the same
     variable on both sides -- that run is `rep u (a*j+b)`;
  3. everything before it is `pre`, everything after it is `post`, both
     concrete.

Nothing here is trusted: the Coq kernel re-runs [check_arm] on the emitted
chain, and a wrong normalisation makes [rrun] return [None] -- the board then
fails to compile -- rather than a wrong theorem.
"""
import re
import sys

MARKER = '#'


# ------------------------------------------------------------------ parsing --

def parse_expr(s):
    """'3+2*y0' -> (const, {var: coeff}).  Also '-1+u0', '0', '1'."""
    const, var = 0, {}
    for part in s.split('+'):
        part = part.strip()
        if not part:
            continue
        if '*' in part:
            c, v = part.split('*', 1)
            var[v] = var.get(v, 0) + int(c)
        elif re.fullmatch(r'-?\d+', part):
            const += int(part)
        else:
            var[part] = var.get(part, 0) + 1
    return const, var


def parse_side(s):
    """'10^1+y0 1^2+y1' -> [(word, const, vars), ...]; word is a tuple of ints
    or the string '#'."""
    out = []
    for tok in s.split():
        w, _, e = tok.partition('^')
        c, v = parse_expr(e)
        out.append((MARKER if w == MARKER else tuple(int(x) for x in w), c, v))
    return out


CFG_RE = re.compile(r'^([A-Z])\[(\d)\] L<([^>]*)> R<([^>]*)>$')


def parse_cfg(s):
    m = CFG_RE.match(s.strip())
    if not m:
        raise ValueError('unparsable config %r' % s)
    return (ord(m.group(1)) - 65, int(m.group(2)),
            parse_side(m.group(3)), parse_side(m.group(4)))


# ------------------------------------------------------- the sside normal form


class ArmShape(Exception):
    """The arm does not fit `pre ++ rep u (a*j+b) ++ post ++ X`."""


def _split_marker(runs):
    """(runs before the wall, open?).  A '#' run means the rest of the side is
    the opaque tail, so the side is OPEN and its tail is not known empty."""
    for i, (w, _, _) in enumerate(runs):
        if w == MARKER:
            return runs[:i], True
    return runs, False


def _common_suffix(a, b):
    """Longest common suffix of two run lists, allowing the last shared run to
    be SPLIT when the words and the variable parts agree and only the constants
    differ.  Returns the two HEADS; what was dropped is the opaque tail, and
    the leftover constants of a split run stay in the heads."""
    i, j = len(a), len(b)
    while i > 0 and j > 0:
        wa, ca, va = a[i - 1]
        wb, cb, vb = b[j - 1]
        if wa != wb:
            break
        if va == vb and ca == cb:
            i, j = i - 1, j - 1
            continue
        if va == vb and va:
            # same word, same variable part, different constants: the variable
            # part joins the tail, the leftover constants stay in the heads.
            lo = min(ca, cb)
            ha = a[:i - 1] + ([(wa, ca - lo, {})] if ca - lo else [])
            hb = b[:j - 1] + ([(wb, cb - lo, {})] if cb - lo else [])
            return ha, hb
        break
    return a[:i], b[:j]


def _cells(runs):
    """Expand constant-count runs to a flat cell list; raise if any is
    variable."""
    out = []
    for w, c, v in runs:
        if v:
            raise ArmShape('variable run where concrete cells are needed')
        if c < 0:
            raise ArmShape('negative run count')
        out.extend(list(w) * c)
    return out


def to_sside(runs, jvar):
    """[(word, const, vars)] -> (pre, u, a, b, post) with at most one variable
    run, whose variable must be `jvar` (or None if the side is constant).

    The GUARANTEED copies of the repeated block are materialised into `pre`:
    [rep u (a*j + b) = rep u b ++ rep u (a*j)] as lists, so the denotation is
    unchanged, but the engine can then step INTO those copies with an ordinary
    window.  Without this the two arms that must see the end of the counter --
    the fill and the string just after it -- have no chain at all, because a
    symbolic block count cannot have one copy peeled off its front."""
    vi = [i for i, (_, _, v) in enumerate(runs) if v]
    if not vi:
        return (_cells(runs), [], 0, 0, [])
    if len(vi) > 1:
        raise ArmShape('two variable runs outside the tail')
    i = vi[0]
    w, c, v = runs[i]
    if list(v) != [jvar]:
        raise ArmShape('run varies in %r, not the arm variable %r'
                       % (list(v), jvar))
    if c < 0:
        raise ArmShape('negative constant on the repeated block')
    return (_cells(runs[:i]) + list(w) * c, list(w), v[jvar], 0,
            _cells(runs[i + 1:]))


def arm_variable(lhs, rhs):
    """The single variable the arm's step count and blocks are affine in."""
    vs = set()
    for _, _, v in lhs[2] + lhs[3] + rhs[2] + rhs[3]:
        vs |= set(v)
    return vs


def _nvar(runs):
    return sum(1 for _, _, v in runs if v)


def normalize(lhs_s, rhs_s, steps_s, lbs=None):
    """(sconf_lhs, sconf_rhs, ca, cb, el, er) for the Coq kernel.

    A side is kept EXACT when it already fits one repeated block -- that is
    what the fill arm needs, since it must see the end of the counter, and
    keeping it exact is what lets [el] be true.  A side that carries several
    variable runs is one the arm does not touch past the first: its common
    suffix with the other side becomes the opaque tail, and the arm is then
    proved for an ARBITRARY tail, which is strictly stronger."""
    ql, hl, Ll, Rl = parse_cfg(lhs_s)
    qr, hr, Lr, Rr = parse_cfg(rhs_s)
    cb, cvars = parse_expr(steps_s)
    if len(cvars) > 1:
        raise ArmShape('step count in %d variables' % len(cvars))
    jvar = next(iter(cvars), None)
    ca = cvars.get(jvar, 0) if jvar else 0

    lbs = lbs or {}

    def shift(runs, v, m):
        out = []
        for w, c, vs in runs:
            if v in vs:
                out.append((w, c + vs[v] * m, vs))
            else:
                out.append((w, c, vs))
        return out

    if jvar is None:
        vs = set()
        for _, _, v in Ll + Lr + Rl + Rr:
            vs |= set(v)
        if len(vs) == 1:
            jvar = next(iter(vs))
    if jvar is not None:
        m = lbs.get(jvar, 0)
        if m:
            Ll, Lr = shift(Ll, jvar, m), shift(Lr, jvar, m)
            Rl, Rr = shift(Rl, jvar, m), shift(Rr, jvar, m)
            cb += ca * m

    Ll, openL = _split_marker(Ll)
    Rl, openR = _split_marker(Rl)
    Lr, openLr = _split_marker(Lr)
    Rr, openRr = _split_marker(Rr)
    if openL != openLr or openR != openRr:
        raise ArmShape('the wall marker moved between lhs and rhs')

    def do(A, B, isopen):
        if not isopen and _nvar(A) <= 1 and _nvar(B) <= 1:
            return A, B, True          # exact: the tail is known empty
        Ah, Bh = _common_suffix(A, B)
        return Ah, Bh, False

    Lh, Lrh, elc = do(Ll, Lr, openL)
    Rh, Rrh, erc = do(Rl, Rr, openR)

    if jvar is None:
        vs = set()
        for _, _, v in Lh + Lrh + Rh + Rrh:
            vs |= set(v)
        if len(vs) > 1:
            raise ArmShape('constant step count but several block variables')
        jvar = next(iter(vs), None)

    return ((ql, hl, to_sside(Lh, jvar), to_sside(Rh, jvar)),
            (qr, hr, to_sside(Lrh, jvar), to_sside(Rrh, jvar)),
            ca, cb, elc, erc)


# ------------------------------------------------------------------- machines

def parse_tm(spec):
    """spec -> {(state, sym): (write, dir, next)} with dir > 0 for RIGHT,
    matching tools/counters/lapcert.py's table convention."""
    tab = {}
    for q, part in enumerate(spec.strip().split('_')):
        for s in range(len(part) // 3):
            e = part[3 * s:3 * s + 3]
            if e[0] == '-' or e[2] in 'ZH-':
                continue
            tab[(q, s)] = (int(e[0]), 1 if e[1] == 'R' else -1,
                           ord(e[2]) - 65)
    return tab


if __name__ == '__main__':
    import json
    cert = json.load(open(sys.argv[1]))
    if isinstance(cert, list):
        cert = cert[0]
    ok = 0
    for a in cert['arms']:
        try:
            L, R, ca, cb, el, er = normalize(a['lhs'], a['rhs'], a['steps'])
            print('%-8s ca=%-3d cb=%-3d el=%-5s er=%-5s' % (a['name'], ca, cb,
                                                            el, er))
            print('         lhs', L)
            print('         rhs', R)
            ok += 1
        except (ArmShape, ValueError) as e:
            print('%-8s SHAPE: %s' % (a['name'], e))
    print('%d/%d arms normalized' % (ok, len(cert['arms'])))
