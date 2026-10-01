"""BLC6: ListGlueRngTr certificates (UNTRUSTED; SCOPING_INSTR.md §7.4.BLC6).

The replica of ListGlueRngTr's unfold layer ([uleaves] and [uwalk] with the
region and the parameters carried along the path, the [URng] node), the
assembly of an X6 exploration, and the rendering to [mkLCR] / [mkLXR].
Importing this module re-points lg_batch's replica (c_fams_ok, c_lwalk) at
the versions below; everything else (leaves, folds, bounds, liveness) is
ListGlue2Tr's and stays lg_batch's / lg3's / lx5's.
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
for d in ('..', '../blc3', '../blc4', '../blc5'):
    sys.path.insert(0, os.path.join(HERE, d))
import lg3                                        # noqa: E402  (installs its c_uleaves2)
import lg_batch as G                              # noqa: E402
import lx5                                        # noqa: E402
import ti_coq as C                                # noqa: E402
import ti_batch as T                              # noqa: E402
from rng6 import shs, sps                         # noqa: E402


def tonly(k, t):
    return all(k2 == k or a == 0 for k2, a in t)


def rlow(r, k, n, m):
    """ListGlueRngTr.rlow (n - 1 truncated, as nat)"""
    return n > 0 and tonly(k, r[1]) and r[0] + C.tcoef(k, r[1]) * max(0, n - 1) < m


def shR(k, n, R):
    M, c = R[k]
    R2 = [tuple(x) for x in R]
    R2[k] = (M, c + M * n)
    return R2


def skid(k, n, pp, j):
    return (j, ()) if j < n else (j, ((k, pp),))


def sreg(k, n, pp, j, R):
    M, c = R[k]
    R2 = [tuple(x) for x in R]
    R2[k] = (0, c + M * j) if j < n else (M * pp, c + M * j)
    return R2


def sp_sub(sg, p):
    return None if p is None else (p[0], C.asubst(sg, p[1]))


def isub(sg, I):
    return [(t, C.asubst(sg, e)) for t, e in I]


def c_uleaves_r(cert, ut, fuel, u, R, pL, pR, iL, iR):
    """ListGlueRngTr.uleaves: [(l, R, pL, pR, iL, iR)] or None"""
    if fuel == 0 or u is None or u >= len(ut):
        return None
    nd = ut[u]
    if nd[0] == 'uleaf':
        return [(nd[1], [tuple(x) for x in R], pL, pR, iL, iR)]
    if nd[0] == 'void':
        left = nd[1] == 'L'
        p = pL if left else pR
        if p is None:
            return None
        s, r = p
        if G.anocoef(r) and r[0] < G.c_mget(cert, left, s):
            return []
        mx = lg3.c_maxget(cert, left, s)
        if mx is not None and mx < r[0]:
            return []
        return None
    if nd[0] == 'rng':
        _, sd, k, n, u2 = nd
        left = sd == 'L'
        p = pL if left else pR
        if p is None:
            return None
        s, r = p
        if not (k < len(R) and rlow(r, k, n, G.c_mget(cert, left, s))):
            return None
        sg = shs(k, n, len(R))
        return c_uleaves_r(cert, ut, fuel - 1, u2, shR(k, n, R), sp_sub(sg, pL), sp_sub(sg, pR),
                           isub(sg, iL), isub(sg, iR))
    if nd[0] == 'spl':
        _, k, n, pp, kids = nd
        if pp == 0 or len(kids) != n + pp or not k < len(R):
            return None
        out = []
        for j, u2 in enumerate(kids):
            sg = sps(k, skid(k, n, pp, j), len(R))
            sub = c_uleaves_r(cert, ut, fuel - 1, u2, sreg(k, n, pp, j, R), sp_sub(sg, pL),
                              sp_sub(sg, pR), isub(sg, iL), isub(sg, iR))
            if sub is None:
                return None
            out += sub
        return out
    _, sd, endk, kids = nd
    left = sd == 'L'
    p = pL if left else pR
    if p is None:
        return None
    s, r = p
    if not G.c_cover(cert, left, s, kids):
        return None
    out = []
    if G.c_accb(cert, left, s):
        if endk is None:
            return None
        sub = c_uleaves_r(cert, ut, fuel - 1, endk, R, None if left else pL,
                          pR if left else None, iL, iR)
        if sub is None:
            return None
        out += sub
    for t, e, u2 in kids:
        if t >= len(cert['trans']):
            return None
        tr = cert['trans'][t]
        if tr['left'] != left or tr['src'] != s:
            return None
        if e is None:
            if not G.c_tvoid(tr, r):
                return None
            continue
        if not G.c_relchk(tr, r, e):
            return None
        if left:
            sub = c_uleaves_r(cert, ut, fuel - 1, u2, R, (tr['dst'], e), pR, iL + [(t, e)], iR)
        else:
            sub = c_uleaves_r(cert, ut, fuel - 1, u2, R, pL, (tr['dst'], e), iL, iR + [(t, e)])
        if sub is None:
            return None
        out += sub
    return out


def c_fams_ok_r(cert, tabw):
    for fi, F in enumerate(cert['fams']):
        L = C.tleaves(F['tree'], len(F['tree']), 0, [(1, 0)] * F['n'])
        if L is None:
            return 'bad tree %d' % fi
        for u, R in L:
            sp = lambda x: None if x is None else (x[0], C.asubst(C.rsub(R), x[1]))  # noqa: E731
            Ls = c_uleaves_r(cert, F['utree'], len(F['utree']), u, R, sp(F['tL']), sp(F['tR']),
                             [], [])
            if Ls is None:
                return 'uleaves fam %d node %d' % (fi, u)
            for l, R2, pL, pR, iL, iR in Ls:
                if l >= len(cert['leaves']):
                    return 'leaf index'
                lf = cert['leaves'][l]
                if lf['f'] != fi or [tuple(x) for x in lf['reg']] != [tuple(x) for x in R2]:
                    return 'leaf %d misfiled' % l
                if [tuple(x) for x in lf['uL']] != [tuple(x) for x in iL] or \
                        [tuple(x) for x in lf['uR']] != [tuple(x) for x in iR]:
                    return 'leaf %d path' % l
                err = G.c_leaf_ok(cert, tabw, F, lf, pL, pR, iL, iR)
                if err:
                    return 'leaf %d: %s' % (l, err)
    return None


def c_uwalk_r(ut, fuel, u, R, z, TL, TR):
    R, z = [tuple(x) for x in R], list(z)
    for _ in range(fuel):
        if u is None or u >= len(ut):
            return None
        nd = ut[u]
        if nd[0] == 'uleaf':
            return nd[1], R, z, TL, TR
        if nd[0] == 'void':
            return None
        if nd[0] == 'rng':
            _, sd, k, n, u2 = nd
            zk = z[k] if k < len(z) else 0
            if zk < n:
                return None
            R = shR(k, n, R)
            if k < len(z):
                z[k] = zk - n
            u = u2
            continue
        if nd[0] == 'spl':
            _, k, n, pp, kids = nd
            zk = z[k] if k < len(z) else 0
            j = zk if zk < n else n + (zk - n) % pp
            if j >= len(kids):
                return None
            R = sreg(k, n, pp, j, R)
            if k < len(z):
                z[k] = 0 if zk < n else (zk - n) // pp
            u = kids[j]
            continue
        _, sd, endk, kids = nd
        T_ = TL if sd == 'L' else TR
        if not T_:
            u = endk
            continue
        t = T_[0][0]
        kk = next((x for x in kids if x[0] == t), None)
        if kk is None or kk[1] is None:
            return None
        u = kk[2]
        if sd == 'L':
            TL = TL[1:]
        else:
            TR = TR[1:]
    return None


def c_lwalk_r(cert, a):
    F = cert['fams'][a['f']]
    r = C.twalk(F['tree'], len(F['tree']), 0, [(1, 0)] * F['n'], a['v'])
    if r is None:
        return None
    u, R, z = r
    return c_uwalk_r(F['utree'], len(F['utree']), u, R, z, list(a['L']), list(a['R']))


G.c_fams_ok = c_fams_ok_r
G.c_lwalk = c_lwalk_r


def assemble(X, t0, pins):
    """lg3.assemble2 with the rng nodes passed through (G.assemble copies a
    'void' node verbatim, so they ride as one)"""
    saved = {}
    for f, ut in X.utrees.items():
        saved[f] = ut
        X.utrees[f] = [('void', ('RNG',) + tuple(nd)) if nd[0] in ('rng', 'spl') else nd for nd in ut]
    try:
        cert = lg3.assemble2(X, t0, pins)
    finally:
        for f, ut in saved.items():
            X.utrees[f] = ut
    for F in cert['fams']:
        F['utree'] = [tuple(nd[1][1:]) if nd[0] == 'void' and isinstance(nd[1], tuple)
                      else nd for nd in F['utree']]
    return cert


# ------------------------------------------------------------- render ----

def r_cert_r(c):
    """lg_batch.r_cert with the URng node"""
    pins = '[' + ';'.join('(%s,%s)' % (G.ST[q], G.SYM[h]) for q, h in c['pins']) + ']'
    kinds = '[' + ';'.join('(%s,%s)' % (G.r_list(pre), G.r_list(u)) for pre, u in c['kinds']) + ']'
    trans = '[' + ';'.join('(mkLT %s %d %d %d %s %d %d %d)' % (
        G.r_bool(t['left']), t['src'], t['kind'], t['dst'], G.r_bool(t['up']), t['a'], t['dp'], t['dn'])
        for t in c['trans']) + ']'
    acc = '[' + ';'.join('(%s,%d)' % (G.r_bool(l), s) for l, s in c['acc']) + ']'
    mins = '[' + ';'.join('(%s,%d,%d)' % (G.r_bool(l), s, v) for l, s, v in c['mins']) + ']'

    def r_unode(nd):
        if nd[0] == 'uleaf':
            return '(ULeaf %d)' % nd[1]
        if nd[0] == 'void':
            return '(UVoid %s)' % G.r_bool(nd[1] == 'L')
        if nd[0] == 'rng':
            return '(URng %s %d %d %d)' % (G.r_bool(nd[1] == 'L'), nd[2], nd[3], nd[4])
        if nd[0] == 'spl':
            return '(USpl %d %d %d [%s])' % (nd[1], nd[2], nd[3], ';'.join(str(x) for x in nd[4]))
        _, sd, endk, kids = nd
        ks = ';'.join('(%d,%s)' % (t, 'None' if e is None else '(Some (%s,%d))' % (G.r_aexp(e), u))
                      for t, e, u in kids)
        return '(UUnf %s %s [%s])' % (G.r_bool(sd == 'L'), G.r_opt(endk, str), ks)

    fams = '[' + ';\n      '.join('(mkLF %s %s %s %s %d [%s] [%s] %s %s)' % (
        G.ST[F['q']], G.SYM[F['h']], G.r_segs(F['L']), G.r_segs(F['R']), F['n'],
        ';'.join(T.cnode(nd) for nd in F['tree']), ';'.join(r_unode(nd) for nd in F['utree']),
        G.r_opt(F['tL'], lambda x: '(%d,%s)' % (x[0], G.r_aexp(x[1]))),
        G.r_opt(F['tR'], lambda x: '(%d,%s)' % (x[0], G.r_aexp(x[1]))))
        for F in c['fams']) + ']'
    leaves = '[' + ';\n      '.join('(mkLL %d [%s] %d [%s] (mkC %s %s %s %s) %d %s %s %d %d %s %s %s %s %s)' % (
        lf['f'], ';'.join('(%d,%d)' % tuple(x) for x in lf['reg']), lf['g'],
        ';'.join(G.r_aexp(e) for e in lf['tgt']),
        G.ST[lf['c0'][0]], T.cside(lf['c0'][1]), G.SYM[lf['c0'][2]], T.cside(lf['c0'][3]),
        lf['j'], G.r_bool(lf['el']), G.r_bool(lf['er']), lf['nL'], lf['nR'], T.cchain(lf['chain']),
        G.r_items(lf['fL']), G.r_items(lf['fR']), G.r_items(lf['uL']), G.r_items(lf['uR']))
        for lf in c['leaves']) + ']'
    S = '[' + ';'.join('(%d,[%s])' % (l, ';'.join(str(x) for x in r)) for l, r in c['S']) + ']'
    ranks = '[' + ';\n      '.join('((%s,%s), [%s])' % (
        G.ST[t[0]], G.SYM[t[1]], ';'.join('(mkRk (%d,[%s]) [] %d [] %d)' % (
            v['V'][0], ';'.join(str(x) for x in v['V'][1]), v['bL'], v['bR']) for v in V))
        for t, V in c['ranks']) + ']'
    a0 = c['a0']
    a0s = '(mkAn %d [%s] [%s] [%s])' % (a0['f'], ';'.join(str(x) for x in a0['v']),
                                        ';'.join('(%d,%d)' % tuple(x) for x in a0['L']),
                                        ';'.join('(%d,%d)' % tuple(x) for x in a0['R']))
    return '(mkLC %s\n      %s\n      %s\n      %s\n      %s\n      %s\n      %s\n      %d %s\n      %s\n      %d %s)' % (
        pins, kinds, trans, acc, mins, fams, leaves, c['P'], S, ranks, c['t0'], a0s)


def render_r(c):
    """lg3.render2 for ListGlueRngTr (mkLCR)"""
    s = r_cert_r(c)
    head = '(mkLC '
    assert s.startswith(head)
    lines = s.split('\n')
    mx = '[' + ';'.join('(%s,%d,%d)' % (G.r_bool(l), st, v) for l, st, v in c.get('maxs', [])) + ']'
    lines.insert(5, '      ' + mx)
    s = '(mkLCR ' + '\n'.join(lines)[len(head):]
    return s


def renderx_r(c):
    """the batch entry: lgr_sound when every instruction has an additive
    ranking, lgrx_sound (ListGlueRngLexTr) when one needs the lex rank"""
    base = render_r(c)
    mir = c.get('mir')
    if not c.get('lex'):
        lemma = 'lgr_sound_mirror' if mir else 'lgr_sound'
        return 'apply coversTr_nqh, (%s _\n      %s).\n  vm_cast_no_check (eq_refl true).' % (lemma, base)
    lex = '[' + ';\n      '.join('((%s,%s), (%s, [%s]))' % (
        G.ST[t[0]], G.SYM[t[1]], G.r_bool(msd), ';'.join(lx5.r_lx(x) for x in xs))
        for t, msd, xs in c.get('lex', [])) + ']'
    lemx = 'lgrx_sound_mirror' if mir else 'lgrx_sound'
    return 'apply coversTr_nqh, (%s _\n      (mkLXR %s\n      %s)).\n  vm_cast_no_check (eq_refl true).' % (
        lemx, base, lex)
