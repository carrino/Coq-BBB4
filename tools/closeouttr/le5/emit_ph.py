#!/usr/bin/env python3
"""UNTRUSTED emitter: a counter with phases, a run and an anchor per phase ->
a Coq board closed by [LadderCheckPhRunTr] (SCOPING_INSTR 7.4.LE5).

The input is a phase MODEL (`model_phrun` from a `phrun2.py` reading,
`model_alt` from an `alt_detect.py` one):

    spec, l, D = [D0, D1], pre, T,
    phases = [{key: [q, s, side, other-side word], W, V}],
    mvT = {p: ('TC', q, dw, dm) | ('TN', q, dm)}   (absent: x is always empty)
    mvE = {p: ('EC', q, dw, dm) | ('ER', a, q, c)} (absent: x is never empty)
    boot = (t, x, p, m)

From it: the flags (runless, empty-only, never-empty), a linear rank over
every move but the refills and the fire carries (a carry is made a fire
carry only when no rank exists without it), the arms (`emit_step.Arms`),
the fires from every refill and fire-carry arm, and the Coq.

    python3 emit_ph.py SPEC DETECT.jsonl -o OUT.v [--qh] [--alt]
"""
import argparse
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'le3'))
sys.path.insert(0, HERE)
import emit_step as S  # noqa: E402
from emit_step import (E, NoClosure, blk, ARM_GRID, coq_conf, coq_chain_l,  # noqa: E402
                       coq_seg, clist, ST, SYM, _splits, Arms, prog_coq, inner_coq, ARM)
import emit_phrun as EP  # noqa: E402

LC = E.LC
nest = E.nest


def bits(w):
    return tuple(int(ch) for ch in w)


# ---------------------------------------------------------------- models

def model_phrun(spec, det, lastf):
    names, idx, mvT, mvE, xe, nm = EP.table_moves(det, fill_missing=False)
    # only the empty-x moves the reader saw: a phase without one never
    # holds an empty x
    seen = set(idx[nm[k[2:]][0]] for k in det['table'] if k.startswith('E|'))
    mvE = {p: t for p, t in mvE.items() if p in seen}
    seq = EP.visits(spec, det)
    bt = EP.find_boot(seq, det, idx, nm, mvT, mvE, xe, lastf)
    if bt is None:
        raise NoClosure('no boot past %d' % lastf)
    t0, (x, p, m) = bt
    q, s, side = det['anchor']
    return dict(spec=spec, l=det['l'], D=det['D'], pre=det['pre'], T=det['T'],
                phases=[dict(key=[q, s, side, ''], W=w.split('|')[0], V=w.split('|')[1])
                        for w in names],
                mvT=mvT, mvE=mvE, boot=(t0, tuple(x), p, m))


def alt_visits(spec, keys, steps=600000):
    """[(t, key, counter-side string)] at the given anchor keys"""
    tm = EP.TD.parse(spec)
    tape, h, q = {}, 0, 0
    lo, hi = 0, -1
    out = []
    ks = set(tuple(k) for k in keys)
    for t in range(steps):
        s = tape.get(h, 0)
        tr = tm[(q, s)]
        if tr is None:
            break
        while lo <= hi and not tape.get(lo, 0):
            lo += 1
        while hi >= lo and not tape.get(hi, 0):
            hi -= 1
        if hi >= lo:
            o = ''.join(str(tape.get(i, 0)) for i in range(h - 1, lo - 1, -1)) if lo < h else ''
            if lo >= h - 3 and (q, s, 'R', o) in ks:
                out.append((t, (q, s, 'R', o), ''.join(str(tape.get(i, 0)) for i in range(h + 1, hi + 1))))
            o = ''.join(str(tape.get(i, 0)) for i in range(h + 1, hi + 1)) if hi > h else ''
            if hi <= h + 3 and (q, s, 'L', o) in ks:
                out.append((t, (q, s, 'L', o), ''.join(str(tape.get(i, 0)) for i in range(h - 1, lo - 1, -1))))
        w, d, nq = tr
        tape[h] = w
        if w:
            if hi < lo:
                lo = hi = h
            else:
                lo, hi = min(lo, h), max(hi, h)
        h += d
        q = nq
    return out


def model_alt(spec, det, lastf):
    import alt_detect as AD
    keys = [tuple(k) for k in det['keys']]
    idx = {k: i for i, k in enumerate(keys)}
    terms = {tuple(json.loads(k)): v for k, v in det['terms'].items()}
    mvT = {}
    for k, (dw, k2) in det['table'].items():
        k = tuple(json.loads(k))
        if dw < 0:
            raise NoClosure('an alternating anchor that narrows')
        mvT[idx[k]] = ('TC', idx[tuple(k2)], dw, 0)
    if len(mvT) != len(keys):
        raise NoClosure('a phase with no move seen')
    seq = alt_visits(spec, keys)
    Ds = tuple(det['D'])
    boot = None
    for i in range(len(seq) - 1):
        t, k, s = seq[i]
        if t <= lastf:
            continue
        x, tl = AD.parse(s, det['l'], Ds)
        if tl != terms[k] or not x:
            continue
        nx = AD.inc(x)
        if nx is None:
            continue
        t2, k2, s2 = seq[i + 1]
        if k2 == k and AD.parse(s2, det['l'], Ds) == (nx, terms[k]):
            boot = (t, tuple(x), idx[k], 0)
            break
    if boot is None:
        raise NoClosure('no boot past %d' % lastf)
    return dict(spec=spec, l=det['l'], D=det['D'], pre='', T='',
                phases=[dict(key=list(k), W=terms[k], V='') for k in keys],
                mvT=mvT, mvE={}, boot=boot)


# ---------------------------------------------------------------- flags, rank

def flags(md):
    NP = len(md['phases'])
    mvT, mvE = md['mvT'], md['mvE']
    xe = {p: p not in mvT for p in range(NP)}
    xn = {p: p not in mvE for p in range(NP)}
    for p in range(NP):
        if xe[p] and xn[p]:
            raise NoClosure('phase %d has no move at all' % p)
    _t, x0, p0, m0 = md['boot']
    if xe[p0] and x0:
        raise NoClosure('boot: x nonempty in an empty-only phase')
    if xn[p0] and not x0:
        raise NoClosure('boot: x empty in a never-empty phase')
    for p in range(NP):
        for t in (mvT.get(p), mvE.get(p)):
            if t is None:
                continue
            q = t[2] if t[0] == 'ER' else t[1]
            if xe[q] and not (t[0] == 'EC' and t[2] == 0):
                raise NoClosure('phase %d holds only an empty x, but a move fills it' % q)
            if xn[q] and ((t[0] == 'TN') or (t[0] == 'EC' and t[2] == 0) or
                          (t[0] == 'ER' and t[1] == 0)):
                raise NoClosure('phase %d never holds an empty x, but a move empties it' % q)
    nr = {p: True for p in range(NP)}
    if m0:
        nr[p0] = False
    ch = True
    while ch:
        ch = False
        for p in range(NP):
            outs = []
            for t in (mvT.get(p), mvE.get(p)):
                if t is None:
                    continue
                if t[0] in ('TC', 'EC'):
                    outs.append((t[1], t[3], nr[p]))
                elif t[0] == 'TN':
                    outs.append((t[1], t[2], nr[p]))
                else:
                    outs.append((t[2], t[3], True))
            for q, dm, srcnr in outs:
                if nr[q] and (dm > 0 or not srcnr):
                    nr[q] = False
                    ch = True
    for p in range(NP):
        if nr[p]:
            continue
        for t in (mvT.get(p), mvE.get(p)):
            if t is None or t[0] == 'ER':
                continue
            if md['phases'][t[1]]['V'] != md['phases'][p]['V']:
                raise NoClosure('phase %d has a run but its move rewrites V' % p)
    return xe, xn, nr


def rank(md, fT):
    NP = len(md['phases'])
    for A in range(1, 9):
        for B in range(0, 5):
            edges = []
            for p in range(NP):
                for t in (md['mvT'].get(p), md['mvE'].get(p)):
                    if t is None or t[0] == 'ER':
                        continue
                    if t[0] == 'TC' and fT[p]:
                        continue
                    if t[0] in ('TC', 'EC'):
                        edges.append((p, t[1], A * t[2] + B * t[3] + 1))
                    else:
                        edges.append((p, t[1], B * t[2] - A + 1))
            g = [0] * NP
            ok = True
            for it in range(NP + 1):
                chg = False
                for p, q, w in edges:
                    if g[p] < w + g[q]:
                        g[p] = w + g[q]
                        chg = True
                if not chg:
                    break
                if it == NP:
                    ok = False
            if ok:
                lo = min(g)
                return A, B, [x - lo for x in g]
    return None


def rank_fire(md):
    """(fT, A, B, g): no fire carries if a rank exists without them, else
    every widening carry a fire carry"""
    NP = len(md['phases'])
    fT = {p: False for p in range(NP)}
    r = rank(md, fT)
    if r is None:
        fT = {p: (md['mvT'].get(p) or ('',))[0] == 'TC' and md['mvT'][p][2] >= 1
              for p in range(NP)}
        r = rank(md, fT)
    if r is None:
        raise NoClosure('no linear rank, even with the widening carries as fire moves')
    return (fT,) + r


# ---------------------------------------------------------------- arms

def nvisits_f(tab, want, el, er, fl, prog):
    """`emit_step.nvisits` under the arm's own tail flags"""
    if not (isinstance(prog, tuple) and prog[:1] == ('NEST',)):
        prog = ('NEST', [('NCh', prog)], [])
    _t, segs, rules = prog
    rr = [(a, b_) for a, b_, _c in rules]
    seen = {}
    for k in range(len(segs) + 1):
        got = nest.nrun(tab, el, er, rr, segs[:k], fl)
        if got is None:
            break
        ck = got[0]
        chs = ([segs[k][1][:i] for i in range(len(segs[k][1]) + 1)]
               if k < len(segs) and segs[k][0] == 'NCh' else [[]])
        for base in chs:
            for kind in ('SWin', 'SWinL', 'SWinR'):
                for n in range(0, 600):
                    g = LC.srun(tab, el, er, base + [(kind, n)], ck)
                    if g is None:
                        break
                    seen.setdefault((g[0][0], g[0][2]),
                                    (list(segs[:k]), base + [(kind, n)]))
            if all(i in seen for i in want):
                return seen
    return seen


def closure_data(md, tab, xe, xn, nr, fT):
    T = bits(md['T'])
    pre = bits(md['pre'])
    D0, D1 = (bits(w) for w in md['D'])
    PH = md['phases']
    W = [bits(ph['W']) for ph in PH]
    V = [bits(ph['V']) for ph in PH]
    NP = len(PH)
    mvT, mvE = md['mvT'], md['mvE']
    left = PH[0]['key'][2] == 'L'
    if any((ph['key'][2] == 'L') != left for ph in PH):
        raise NoClosure('phases on both sides')

    def conf(p, sd):
        q, hs, _side, oth = PH[p]['key']
        O = (bits(oth), (), 0, 0, ())
        return (q, sd, hs, O) if left else (q, O, hs, sd)

    derive = Arms(tab).derive
    el, er = (not left), left

    def fl(p):
        return (True, True) if nr[p] else (el, er)

    def lw(p):
        return W[p] + V[p] if nr[p] else W[p]

    def rw(p, q_, dm):
        return W[q_] + T * dm + V[q_] if nr[p] else W[q_] + T * dm

    def inter_at(n0, st):
        got = []
        for p in range(NP):
            if xe[p]:
                continue
            for e in range(3):
                for r in range(n0 + st):
                    s_ = 0 if r < n0 else st
                    w = [D0, D1, lw(p)][e]
                    a_, b_ = (el, er) if e < 2 else fl(p)
                    c0 = conf(p, blk(pre + D1 * r, D1, s_, D0 + w))
                    c1 = conf(p, blk(pre + D0 * r, D0, s_, D1 + w))
                    try:
                        got.append((p, e, r, c0, c1, a_, b_,
                                    derive(a_, b_, c0, c1, 'interior p=%d e=%d r=%d' % (p, e, r))))
                    except NoClosure:
                        return None
        return got

    def tmove_at(kind, lo):
        def at(n0, st):
            got = []
            for p in range(NP):
                t = mvT.get(p)
                if t is None or t[0] != kind:
                    continue
                a_, b_ = fl(p)
                for r in range(lo, n0 + st):
                    s_ = 0 if r < n0 else st
                    c0 = conf(p, blk(pre + D1 * r, D1, s_, lw(p)))
                    if kind == 'TC':
                        c1 = conf(t[1], blk(pre + D0 * (r + t[2]), D0, s_, rw(p, t[1], t[3])))
                    else:
                        c1 = conf(t[1], blk(pre + D0 * (r - 1), D0, s_, rw(p, t[1], t[2])))
                    try:
                        got.append((p, r, c0, c1, a_, b_,
                                    derive(a_, b_, c0, c1, '%s p=%d r=%d' % (kind, p, r))))
                    except NoClosure:
                        return None
            return got
        at.__name__ = kind
        return at

    want = [(q_, s_) for q_ in range(4) for s_ in range(2)
            if (q_, s_) not in E.TR_PINS]

    ecarry = []
    for p in range(NP):
        t = mvE.get(p)
        if t is None or t[0] != 'EC':
            continue
        a_, b_ = fl(p)
        c0 = conf(p, (pre + lw(p), (), 0, 0, ()))
        c1 = conf(t[1], (pre + D0 * t[2] + rw(p, t[1], t[3]), (), 0, 0, ()))
        ecarry.append((p, c0, c1, a_, b_, derive(a_, b_, c0, c1, 'empty carry p=%d' % p)))

    def refill_at(n0, st):
        got = []
        for p in range(NP):
            t = mvE.get(p)
            if t is None or t[0] != 'ER':
                continue
            _e, a, q2, c = t
            for r in range(0, n0 + st):
                s_ = 0 if r < n0 else st
                c0 = conf(p, blk(pre + W[p] + T * r, T, s_, V[p]))
                hit = None
                for f1 in _splits(r + a):
                    c1 = conf(q2, blk(pre + D0 * f1, D0, s_, D0 * (r + a - f1) + W[q2] + T * c + V[q2]))
                    try:
                        hit = (p, r, f1, r + a - f1, c0, c1,
                               derive(True, True, c0, c1, 'refill p=%d r=%d' % (p, r)))
                        break
                    except NoClosure:
                        continue
                if hit is None:
                    return None
                got.append(hit)
        return got

    def first(fn, grid):
        for n0, st in grid:
            gg = fn(n0, st)
            if gg is not None:
                return gg, n0, st
        raise NoClosure('%s: no program at any threshold and stride' % fn.__name__)

    inter, n0i, sti = first(inter_at, ARM_GRID)
    # carries: a carry whose arms fire every instruction is a fire carry;
    # a rank must exist over the other moves
    carry = n0c = stc = cvis = rk = None
    for n0, st in ARM_GRID:
        gg = tmove_at('TC', 0)(n0, st)
        if gg is None:
            continue
        seen = {}
        fire = {p: (mvT.get(p) or ('',))[0] == 'TC' for p in range(NP)}
        for p, r, c0, _c1, a_, b_, ch in gg:
            sv = nvisits_f(tab, want, a_, b_, c0, ch)
            if all(i in sv for i in want):
                seen[(p, r)] = {i: sv[i] for i in want}
            else:
                fire[p] = False
        fT2 = {p: fire[p] for p in range(NP)}
        rk = rank(md, {p: False for p in range(NP)})
        if rk is not None:
            fT2 = {p: False for p in range(NP)}
        else:
            rk = rank(md, fT2)
        if rk is None:
            continue
        carry, n0c, stc = gg, n0, st
        cvis = {k: v for k, v in seen.items() if fT2[k[0]]}
        fT = fT2
        break
    if carry is None:
        raise NoClosure('carry: no program, or no rank over the carries that do not fire')
    grid1 = [(n0, st) for n0, st in ARM_GRID if n0 >= 1]
    narr, n0n, stn = first(tmove_at('TN', 1), grid1)
    refill = nvis = None
    for n0, st in ARM_GRID:
        gg = refill_at(n0, st)
        if gg is None:
            continue
        seen = {(p, r): nvisits_f(tab, want, True, True, c0, ch) for p, r, _f1, _f2, c0, _c1, ch in gg}
        if all(i in seen[k] for k in seen for i in want):
            refill, n0r, str_ = gg, n0, st
            nvis = {k: {i: seen[k][i] for i in want} for k in seen}
            break
    if refill is None:
        raise NoClosure('refill: no program, or an instruction some refill arm does not fire')
    return dict(nest=True, fT=fT, rank=rk, inter=inter, n0i=n0i, sti=sti, carry=carry, n0c=n0c, stc=stc,
                cvis=cvis, narr=narr, n0n=n0n, stn=stn, ecarry=ecarry, refill=refill,
                n0r=n0r, str=str_, nvis=nvis, W=W, V=V, T=T, NP=NP, fill=refill)


# ---------------------------------------------------------------- Coq

def syms(cells):
    return '[' + ';'.join('S%d' % x for x in cells) + ']'


def tcoq(t):
    if t is None:
        return 'TNone'
    if t[0] == 'TC':
        return 'TCarry %d %d %d' % t[1:]
    return 'TNarrow %d %d' % t[1:]


def ecoq(t):
    if t is None:
        return 'ECarry 0 0 0'
    if t[0] == 'EC':
        return 'ECarry %d %d %d' % t[1:]
    return 'ERefill %d %d %d' % t[1:]


def per_phase(NP, body):
    return ''.join('  destruct p as [|p].\n  {\n%s  }\n' % body(p) for p in range(NP)) + \
        '  exfalso; lia.\n'


def per_r(n, body, lo=0, ind='    '):
    return ''.join('%sdestruct r as [|r].\n%s{ %s. }\n'
                   % (ind, ind, 'exfalso; lia' if r < lo else body(r)) for r in range(n)) + \
        '%sexfalso; lia.\n' % ind


TM = os.path.join(HERE, 'emit_ph_tmpl.txt')


def emit_closure(cert, tab, mid):
    md, xe, xn, nr, fT, A, B, g = MD
    cd = S.two_pass(lambda _c, _t: closure_data(md, tab, xe, xn, nr, fT), cert, tab)
    if isinstance(cd, NoClosure):
        return E.CLOSURE_NONE % cd, None
    fT = cd['fT']
    A, B, g = cd['rank']
    NP = cd['NP']
    PH = md['phases']
    mvT, mvE = md['mvT'], md['mvE']
    n0i, sti, n0c, stc, n0n, stn, n0r, str_ = (cd[k] for k in
                                               ('n0i', 'sti', 'n0c', 'stc', 'n0n', 'stn', 'n0r', 'str'))
    ptab = ''.join('    - %d: anchor %s%s / %s, %s | %s: %s, %s%s%s%s%s\n'
                   % (p, 'ABCD'[PH[p]['key'][0]], PH[p]['key'][1], PH[p]['key'][3] or '-',
                      PH[p]['W'] or '-', PH[p]['V'] or '-',
                      tcoq(mvT.get(p)), ecoq(mvE.get(p)) if p in mvE else 'never empty',
                      ' (runless)' if nr[p] else '', ' (empty x only)' if xe[p] else '',
                      ' (fire carry)' if fT[p] else '', '')
                   for p in range(NP))
    t0, bx, p0, bm = md['boot']
    tmpl = open(TM).read().split('(* ---- ')
    T_ = {}
    for chunk in tmpl[1:]:
        name, body = chunk.split(' ---- *)\n', 1)
        T_[name] = body
    pc = dict(mid=mid, NP=NP, A=A, B=B, n0i=n0i, sti=sti, n0c=n0c, stc=stc, n0n=n0n, stn=stn,
              n0r=n0r, str=str_, T=md['T'] or '-', ptab=ptab,
              Wb=' '.join('| %d => %s' % (p, syms(cd['W'][p])) for p in range(NP)),
              Vb=' '.join('| %d => %s' % (p, syms(cd['V'][p])) for p in range(NP)),
              Tc=syms(cd['T']),
              MTb=' '.join('| %d => %s' % (p, tcoq(mvT.get(p))) for p in range(NP)),
              MEb=' '.join('| %d => %s' % (p, ecoq(mvE.get(p))) for p in range(NP)),
              Sb=' '.join('| %d => %s' % (p, ST[PH[p]['key'][0]]) for p in range(NP)),
              Hb=' '.join('| %d => %s' % (p, SYM[PH[p]['key'][1]]) for p in range(NP)),
              Ob=' '.join('| %d => %s' % (p, clist(bits(PH[p]['key'][3]), lambda c: SYM[c]))
                          for p in range(NP)),
              Nb=' '.join('| %d => %s' % (p, 'true' if nr[p] else 'false') for p in range(NP)),
              Xb=' '.join('| %d => %s' % (p, 'true' if xe[p] else 'false') for p in range(NP)),
              XNb=' '.join('| %d => %s' % (p, 'true' if xn[p] else 'false') for p in range(NP)),
              FTb=' '.join('| %d => %s' % (p, 'true' if fT[p] else 'false') for p in range(NP)),
              Gb=' '.join('| %d => %d' % (p, g[p]) for p in range(NP)),
              S0=ST[PH[0]['key'][0]], H0=SYM[PH[0]['key'][1]])
    L = [T_['HEAD'] % pc]
    inner, arms = [], []
    for p, e, r, c0, c1, a_, b_, ch in cd['inter']:
        arms.append(('iarm_%d_%d_%d' % (p, e, r), c0, c1, prog_coq(tab, inner, ch), a_, b_))
    coffs = {}
    for p, r, c0, c1, a_, b_, ch in cd['carry']:
        coffs[(p, r)] = len(inner)
        arms.append(('carm_%d_%d' % (p, r), c0, c1, prog_coq(tab, inner, ch), a_, b_))
    for p, r, c0, c1, a_, b_, ch in cd['narr']:
        arms.append(('narm_%d_%d' % (p, r), c0, c1, prog_coq(tab, inner, ch), a_, b_))
    for p, c0, c1, a_, b_, ch in cd['ecarry']:
        arms.append(('earm_%d' % p, c0, c1, prog_coq(tab, inner, ch), a_, b_))
    offs = {}
    for p, r, _f1, _f2, c0, c1, ch in cd['refill']:
        offs[(p, r)] = len(inner)
        arms.append(('rarm_%d_%d' % (p, r), c0, c1, prog_coq(tab, inner, ch), True, True))
    L.append(inner_coq(mid, inner))
    for nm_, c0, c1, segs, el_, er_ in arms:
        L.append(ARM % dict(nm=nm_, mid=mid, lhs=coq_conf(c0), rhs=coq_conf(c1),
                            segs=';\n   '.join(segs), el=str(el_).lower(),
                            er=str(er_).lower()))
    dflt = arms[0][0]

    def vtab(vis, offs_):
        vb = '\n  '.join('| %d, %d, (%s, %s) => %s' % (k[0], k[1], ST[i[0]], SYM[i[1]], coq_chain_l(v[1]))
                         for k in sorted(vis) for i, v in sorted(vis[k].items()))
        sb = '\n  '.join('| %d, %d, (%s, %s) => [%s]'
                         % (k[0], k[1], ST[i[0]], SYM[i[1]],
                            '; '.join(coq_seg(sg, offs_[k]) for sg in v[0]))
                         for k in sorted(vis) for i, v in sorted(vis[k].items()))
        return vb, sb
    vb, sb = vtab(cd['nvis'], offs)
    cvb, csb = vtab(cd['cvis'], coffs)
    L.append(T_['DEFS'] % dict(
        mid=mid, dflt=dflt,
        ib=' '.join('| %d, %d, %d => iarm_%d_%d_%d_%s' % (p, e, r, p, e, r, mid)
                    for p, e, r, *_ in cd['inter']),
        cb=' '.join('| %d, %d => carm_%d_%d_%s' % (p, r, p, r, mid) for p, r, *_ in cd['carry']),
        nb=' '.join('| %d, %d => narm_%d_%d_%s' % (p, r, p, r, mid) for p, r, *_ in cd['narr']),
        eb=' '.join('| %d => earm_%d_%s' % (p, p, mid) for p, *_ in cd['ecarry']),
        rb=' '.join('| %d, %d => rarm_%d_%d_%s' % (p, r, p, r, mid) for p, r, *_ in cd['refill']),
        b1=' '.join('| %d, %d => %d' % (p, r, f1) for p, r, f1, *_ in cd['refill']),
        b2=' '.join('| %d, %d => %d' % (p, r, f2) for p, r, _f1, f2, *_ in cd['refill']),
        vb=vb, sb=sb, cvb=cvb, csb=csb))

    def reach(nm_):
        return ('eapply narm_reach; [exact nrules_sound_%s | exact ok_%s_%s]'
                % (mid, nm_, mid))

    def kind(p, which):
        t = mvT.get(p) if which == 'T' else mvE.get(p)
        return 'TX' if t is None else t[0]

    INJ = {'TC': ' <- <- <-', 'TN': ' <- <-', 'EC': ' <- <- <-', 'ER': ' <- <- <-'}
    NOT = '    exfalso; vm_compute in Hmv; discriminate Hmv.\n'

    def ph_body(which, k, rbody, n=None, lo=0, extra=None):
        """per phase: refute the wrong move kind (or the flag premise), else
        the body per index"""
        def body(p):
            if which == 'E' and xn[p]:
                return '    exfalso; vm_compute in Hxn; discriminate Hxn.\n'
            if kind(p, which) != k:
                return NOT
            if extra is not None and not extra(p):
                return '    exfalso; vm_compute in Hf; discriminate Hf.\n'
            hd = '    vm_compute in Hmv; injection Hmv as%s.\n' % INJ[k]
            if n is None:
                return hd + '    ' + rbody(p, None) + '.\n'
            return hd + per_r(n, lambda r: rbody(p, r), lo)
        return per_phase(NP, body)

    def tx_body(p):
        if kind(p, 'T') != 'TX':
            return NOT
        return '    reflexivity.\n'

    def ibody(fmt):
        def body(p):
            if xe[p]:
                return '    exfalso; vm_compute in Hx; discriminate Hx.\n'
            out = ''
            for e in range(3):
                out += '    destruct e as [|e].\n    {\n%s    }\n' % per_r(
                    n0i + sti, lambda r, e=e: fmt(p, e, r), ind='      ')
            return out + '    exfalso; lia.\n'
        return per_phase(NP, body)

    cmp = 'vm_compute; reflexivity'
    ok = lambda p, r: 'phok'  # noqa: E731
    vk = lambda p, r: 'vm_compute; first [reflexivity | discriminate]'  # noqa: E731
    fire = ('destruct t as [q s]; destruct q, s; '
            'try (exfalso; apply Hnp; simpl; tauto); vm_compute; reflexivity')
    L.append(T_['PHL'] % dict(
        pc,
        ptc=ph_body('T', 'TC', ok), ptn=ph_body('T', 'TN', ok),
        ptx=per_phase(NP, tx_body),
        pec=ph_body('E', 'EC', ok), per=ph_body('E', 'ER', ok),
        pvtc=ph_body('T', 'TC', vk), pvtn=ph_body('T', 'TN', vk), pvec=ph_body('E', 'EC', vk),
        isound=ibody(lambda p, e, r: reach('iarm_%d_%d_%d' % (p, e, r))),
        icomp=ibody(lambda p, e, r: cmp),
        csound=ph_body('T', 'TC', lambda p, r: reach('carm_%d_%d' % (p, r)), n0c + stc),
        ccomp=ph_body('T', 'TC', lambda p, r: cmp, n0c + stc),
        cfire=ph_body('T', 'TC', lambda p, r: fire, n0c + stc, extra=lambda p: fT[p]),
        nsound=ph_body('T', 'TN', lambda p, r: reach('narm_%d_%d' % (p, r)), n0n + stn, 1),
        ncomp=ph_body('T', 'TN', lambda p, r: cmp, n0n + stn, 1),
        esound=ph_body('E', 'EC', lambda p, r: reach('earm_%d' % p)),
        ecomp=ph_body('E', 'EC', lambda p, r: cmp),
        rsound=ph_body('E', 'ER', lambda p, r: reach('rarm_%d_%d' % (p, r)), n0r + str_),
        rcomp=ph_body('E', 'ER', lambda p, r: cmp, n0r + str_),
        rlia=ph_body('E', 'ER', lambda p, r: 'vm_compute; lia', n0r + str_),
        fvis=ph_body('E', 'ER', lambda p, r: fire, n0r + str_),
        t0=t0, x0=clist(bx, str), p0=p0, m0=bm,
        tmb=('tm_%s' % mid) if E.TR_QH is not None else 'tm'))
    common = dict(pc, x0=clist(bx, str), p0=p0, m0=bm, t0=t0)
    yes, no = 'intros _; reflexivity.', 'intros Hz; discriminate Hz.'
    args = T_['ARGS'] % dict(mid=mid,
                             hm0=yes if bm == 0 else no,
                             hx0=yes if not bx else no,
                             hn0=('intros _; discriminate.' if bx else no))
    if E.TR_QH is not None:
        L.append(T_['QHT'] % dict(common, call=T_['CALL'].strip() % dict(common, board='boardP_qhtr'),
                                  args=args))
    else:
        L.append(T_['NQHT'] % dict(common, call=T_['CALL'].strip() % dict(common, board='boardP_neverqhtr'),
                                   args=args))
    return ''.join(L), cd


MD = None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('spec')
    ap.add_argument('detect')
    ap.add_argument('-o', '--out', required=True)
    ap.add_argument('--qh', action='store_true')
    ap.add_argument('--alt', action='store_true', help='an alt_detect.py reading')
    ap.add_argument('--scan', default=os.path.join(HERE, '..', '..', '..',
                                                   'censustr_v9_scan_1e8.txt'))
    args = ap.parse_args()
    det = None
    for l in open(args.detect):
        r = json.loads(l)
        if r['spec'] == args.spec and (r.get('anchor') or r.get('keys')):
            det = r
    if det is None:
        raise SystemExit('%s: no reading' % args.spec)
    spec = args.spec
    lastf = -1
    if args.qh:
        row = None
        for l in open(args.scan):
            if l.startswith(spec + ' '):
                row = l.split()[1:]
                break
        E.TR_PINS, lastf = E.quiet_pins(spec, row)
    else:
        E.TR_PINS = E.unfired(spec, 10 ** 6)
    md = (model_alt if args.alt else model_phrun)(spec, det, lastf)
    xe, xn, nr = flags(md)
    fT, A, B, g = rank_fire(md)   # a precheck; the arm search picks the fire carries
    if args.qh:
        E.TR_QH = md['boot'][0]
    global MD
    MD = (md, xe, xn, nr, fT, A, B, g)
    k0 = md['phases'][0]['key']
    d0, d1 = md['D']
    cert = dict(spec=spec, ladder=[], arms=[],
                family=dict(base=2, digits=[[int(ch) for ch in d0], [int(ch) for ch in d1]],
                            near_head_prefix=[int(ch) for ch in md['pre']],
                            terminator=[], terminators_by_phase=[[]], code='binary',
                            value_step_per_anchor_visit=1, state='ABCD'[k0[0]], head=k0[1],
                            side=k0[2], other_side_cells=[int(ch) for ch in k0[3]]),
                fill=dict(widens_by=1, target_prefix=[], target_fill_digit=0,
                          target_suffix=[1], lands_in_phase=0))
    E.emit_closure = emit_closure
    good, bad, cd = E.emit(cert, args.out)
    print('%s: closure %s' % (args.out, 'BUILT' if cd else 'not built'))
    return 0 if cd else 1


if __name__ == '__main__':
    sys.exit(main())
