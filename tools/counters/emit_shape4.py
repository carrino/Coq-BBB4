#!/usr/bin/env python3
"""UNTRUSTED emitter for LAP-SHAPE-4 interleaved counters under [Ip].

Shape 4 (`-DA|+AB`, tools/counter_lapshapes.tsv rank 4, 25 machines): the
DIRECT-encoding sibling of the ILS1 family.  Chain (both branches affine:
interior 4j+4, overflow 4j'+11 for the exemplar):

  P1   pop the LSB marker off the anchor (1 step, deposits the blanked
       frontier cell);
  RIP  leftward 1-cell run over the set region (cycL, unit [S1] -> [S1],
       count 2j interior / 2j' overflow);
  STPI pop the stopping pair's clear bit (interior only);
  TRN  turn right through the just-deposited cell (interior only);
  STPO overflow stop through the tail wall + synthetic blank (left-open);
  RET  rightward rewrite cycle (cycR, unit [S1;S1] -> [S0;S1], count j /
       j') -- the classic Ip return;
  FIN  frontier close (interior, 1 step, exact) / FIN2 overflow close
       (right-open excursion past the frontier; closes one LEFT blank short
       of the anchor tail -> lift close, interior stays EXACT).

Anchor: Cc p = (E, (Ip p ++ tail, S0, [])) -- far side is the EMPTY LIST
(the interior lap never looks right of the frontier).

Everything here is UNTRUSTED: the Coq kernel re-checks every emitted board.

Usage
  emit_shape4.py --list FILE [--emit] [--windows] [--json OUT]
"""
import argparse
import json
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, '..', '..'))
sys.path.insert(0, HERE)

from executor import Exec, Wall                                     # noqa: E402
from emit_interleave import (Raw, strip0, LAB, ST, SYM, ENC,          # noqa: E402
                             DeriveError, derive_tail, mach_id, coq_table,
                             clist, ccons, cwin)

OUTDIR = os.path.join(REPO, 'theories', 'Machines', 'Counters')
MAXN = 16


def carry(m):
    j = 0
    while (m >> j) & 1:
        j += 1
    return j, (m == (1 << j) - 1)


def m_int(j):
    return (1 << (j + 1)) + (1 << j) - 1 if j else 2


def nrm(cfg):
    q, l, h, r = cfg
    return (q, tuple(strip0(l)), h, tuple(strip0(r)))


def lap_len(spec, E, encf, tail, m, maxsteps=200000):
    raw = Raw(spec)
    cfg = (E, encf(m) + list(tail), 0, [])
    tgt = nrm((E, encf(m + 1) + list(tail), 0, []))
    for n in range(1, maxsteps):
        cfg = raw.step(cfg)
        if cfg is None:
            return None
        if nrm(cfg) == tgt:
            return n
    return None


def affine(pts):
    js = sorted(pts)
    if len(js) < 2:
        return None
    j0, j1 = js[0], js[1]
    n0, n1 = pts[j0], pts[j1]
    if (n1 - n0) % (j1 - j0):
        return None
    b = (n1 - n0) // (j1 - j0)
    a = n0 - b * j0
    return (a, b) if all(pts[j] == a + b * j for j in js) else None


def profile(spec, E, encf, tail):
    inter, over = {}, {}
    for j in range(0, 4):
        n = lap_len(spec, E, encf, tail, m_int(j))
        if n is None:
            return None
        inter[j] = n
    for j in range(2, 5):
        n = lap_len(spec, E, encf, tail, (1 << j) - 1)
        if n is None:
            return None
        over[j] = n
    ai, ao = affine(inter), affine(over)
    return None if (ai is None or ao is None) else (ai, ao)


def conc(ex, cfg, bl, br, n, lw, rw):
    q, l, h, r = cfg
    lw = len(l) if lw is None else lw
    rw = len(r) if rw is None else rw
    if lw > len(l) or rw > len(r):
        raise Wall('window deeper than tape')
    out = ex.wsteps(bl, br, q, l[:lw], h, r[:rw], n)
    ent = (q, tuple(l[:lw]), h, tuple(r[:rw]))
    ext = (out[0], tuple(out[1]), out[2], tuple(out[3]))
    return (out[0], out[1] + l[lw:], out[2], out[3] + r[rw:]), (ent, ext)


def cycl(ex, cfg, ulen, P, k):
    q, l, h, r = cfg
    if k == 0:
        return cfg, None
    u = l[:ulen]
    out = ex.wsteps(True, True, q, u, h, [], P)
    if not (out[0] == q and out[2] == h and out[1] == []):
        raise Wall('not a cycL unit')
    w = out[3]
    if l[:ulen * k] != u * k:
        raise Wall('left is not u^k')
    return ((q, l[ulen * k:], h, w * k + r),
            ((q, tuple(u), h, ()), (q, (), h, tuple(w))))


def cycr(ex, cfg, ulen, P, k):
    q, l, h, r = cfg
    if k == 0:
        return cfg, None
    if ulen * k > len(r):
        raise Wall('cycR window')
    u = r[:ulen]
    out = ex.wsteps(True, True, q, [], h, u, P)
    if not (out[0] == q and out[2] == h and out[3] == []):
        raise Wall('not a cycR unit')
    w = out[1]
    if r[:ulen * k] != u * k:
        raise Wall('right is not u^k')
    return ((q, w * k + l, h, r[ulen * k:]),
            ((q, (), h, tuple(u)), (q, tuple(w), h, ())))


def replay_int(ex, E, encf, tail, m, j, s):
    cfg = (E, encf(m) + list(tail), 0, [])
    U = {}
    cfg, U['P1'] = conc(ex, cfg, True, True, s['nP1'], 1, 0)
    cfg, u = cycl(ex, cfg, 1, s['nRIP'], 2 * j)
    if u:
        U['RIP'] = u
    cfg, U['STPI'] = conc(ex, cfg, True, True, s['nSTP'], 1, 0)
    cfg, U['TRN'] = conc(ex, cfg, True, True, s['nTRN'], 0, 1)
    cfg, u = cycr(ex, cfg, 2, s['nRET'], j)
    if u:
        U['RET'] = u
    cfg, U['FIN'] = conc(ex, cfg, True, True, s['nFIN'], 0, None)
    return cfg, U


def replay_ov(ex, E, encf, tail, m, j, s):
    cfg = (E, encf(m) + list(tail), 0, [])
    U = {}
    cfg, U['P1b'] = conc(ex, cfg, True, True, s['nP1'], 1, 0)
    cfg, u = cycl(ex, cfg, 1, s['nRIP'], 2 * j)
    if u:
        U['RIPb'] = u
    cfg, U['STPO'] = conc(ex, cfg, False, True, s['nSTPO'], None, 0)
    cfg, u = cycr(ex, cfg, 2, s['nRET'], j)
    if u:
        U['RETb'] = u
    cfg, U['FIN2'] = conc(ex, cfg, True, False, s['nFIN2'], 0, None)
    return cfg, U


def replay_int_flip(ex, E, encf, tail, m, j, s):
    """Flip variant: P1 is a 2-step frontier flip inside the far [S0] window,
    the ripple runs THROUGH the LSB marker (count 2j+1), no separate turn
    deposit bookkeeping changes."""
    cfg = (E, encf(m) + list(tail), 0, [0])
    U = {}
    cfg, U['P1'] = conc(ex, cfg, True, True, s['nP1'], 0, 1)
    cfg, u = cycl(ex, cfg, 1, s['nRIP'], 2 * j + 1)
    if u:
        U['RIP'] = u
    cfg, U['STPI'] = conc(ex, cfg, True, True, s['nSTP'], 1, 0)
    cfg, U['TRN'] = conc(ex, cfg, True, True, s['nTRN'], 0, 1)
    cfg, u = cycr(ex, cfg, 2, s['nRET'], j)
    if u:
        U['RET'] = u
    cfg, U['FIN'] = conc(ex, cfg, True, True, s['nFIN'], 0, None)
    return cfg, U


def replay_ov_flip(ex, E, encf, tail, m, j, s):
    """Overflow: the ripple also swallows the S1 wall (count 2j'+2, so the
    tail must be [S1;S0]), the stop bounces off the synthetic blank."""
    cfg = (E, encf(m) + list(tail), 0, [0])
    U = {}
    cfg, U['P1b'] = conc(ex, cfg, True, True, s['nP1'], 0, 1)
    cfg, u = cycl(ex, cfg, 1, s['nRIP'], 2 * j + 2)
    if u:
        U['RIPb'] = u
    cfg, U['STPO'] = conc(ex, cfg, False, True, s['nSTPO'], None, 0)
    k = (len(cfg[3]) - 1) // 2 - s.get('kOFF', 0)
    if k < 0:
        raise Wall('overflow return count')
    cfg, u = cycr(ex, cfg, 2, s['nRET'], k)
    if u:
        U['RETb'] = u
    U['kov'] = k
    cfg, U['FIN2'] = conc(ex, cfg, True, False, s['nFIN2'], s.get('nFL2', 0),
                          None)
    return cfg, U


def derive_flip(spec, E, encf, tail, ai, ao):
    """interior n(j) = nP1 + nRIP*(2j+1) + nSTP + nTRN + nRET*j + nFIN
       overflow n(j')= nP1 + nRIP*(2j'+2) + nSTPO + nRET*kov + nFIN2"""
    if list(tail) != [1, 0]:
        raise DeriveError('flip template needs tail [S1;S0], got %s'
                          % list(tail))
    a, b = ai
    aoa, aob = ao
    ex = Exec(spec)
    JI, KO = 3, 4
    tgt_i = (E, encf(m_int(JI) + 1) + list(tail), 0, [0])
    t_full = (E, encf(1 << KO) + list(tail), 0, [0])
    t_lift = (E, encf(1 << KO) + list(tail[:-1]), 0, [0])
    for nP1 in range(1, 5):
        for nRIP in range(1, 5):
            for nRET in range(1, 7):
                if 2 * nRIP + nRET != b:
                    continue
                for nSTP in range(1, MAXN):
                    for nTRN in range(1, 5):
                        nFIN = a - nP1 - nRIP - nSTP - nTRN
                        if nFIN < 1:
                            continue
                        s = dict(nP1=nP1, nRIP=nRIP, nRET=nRET, nSTP=nSTP,
                                 nTRN=nTRN, nFIN=nFIN)
                        try:
                            cfg, U = replay_int_flip(ex, E, encf, tail,
                                                     m_int(JI), JI, s)
                        except (Wall, KeyError, IndexError):
                            continue
                        if cfg != tgt_i:
                            continue
                        for nSTPO in range(1, MAXN + 10):
                            for nFIN2 in range(1, MAXN + 10):
                                for nFL2 in range(0, 5):
                                    for kOFF in range(0, 2):
                                        s2 = dict(s, nSTPO=nSTPO, nFIN2=nFIN2,
                                                  nFL2=nFL2, kOFF=kOFF)
                                        try:
                                            cfg2, UO = replay_ov_flip(
                                                ex, E, encf, tail,
                                                (1 << KO) - 1, KO - 1, s2)
                                        except (Wall, KeyError, IndexError):
                                            continue
                                        if cfg2 == t_full:
                                            exact_ov = True
                                        elif cfg2 == t_lift:
                                            exact_ov = False
                                        else:
                                            continue
                                        if aoa + aob * KO != (
                                                nP1 + nRIP * (2 * (KO - 1) + 2)
                                                + nSTPO + nRET * UO['kov']
                                                + nFIN2):
                                            continue
                                        U.update(UO)
                                        return s2, U, exact_ov
    raise DeriveError('no flip skeleton fits both lap branches')


def validate_flip(spec, E, encf, tail, s, exact_ov, hi=160):
    ex = Exec(spec)
    n = 0
    for m in list(range(1, hi)) + [2**10 - 1, 2**10, 2**13 - 1, 2**13 + 5]:
        j, ov = carry(m)
        raw = lap_len(spec, E, encf, tail, m)
        if raw is None:
            raise DeriveError('raw lap does not close at m=%d' % m)
        if ov:
            tgt = (E, encf(m + 1) + list(tail if exact_ov else tail[:-1]),
                   0, [0])
            cfg, U = replay_ov_flip(ex, E, encf, tail, m, j - 1, s)
            got = (s['nP1'] + s['nRIP'] * (2 * (j - 1) + 2) + s['nSTPO']
                   + s['nRET'] * U['kov'] + s['nFIN2'])
        else:
            tgt = (E, encf(m + 1) + list(tail), 0, [0])
            cfg, U = replay_int_flip(ex, E, encf, tail, m, j, s)
            got = (s['nP1'] + s['nRIP'] * (2 * j + 1) + s['nSTP'] + s['nTRN']
                   + s['nRET'] * j + s['nFIN'])
        if cfg != tgt:
            raise DeriveError('m=%d: symbolic lap misses the next anchor' % m)
        if got != raw:
            raise DeriveError('m=%d: symbolic %d != raw %d' % (m, got, raw))
        n += 1
    return n


def derive(spec, E, encf, tail, ai, ao):
    """interior n(j) = nP1 + nRIP*2j + nSTP + nTRN + nRET*j + nFIN
       overflow n(j')= nP1 + nRIP*2j' + nSTPO + nRET*j' + nFIN2"""
    a, b = ai
    aoa, aob = ao
    ex = Exec(spec)
    JI, KO = 3, 4
    tgt_i = (E, encf(m_int(JI) + 1) + list(tail), 0, [])
    t_full = (E, encf((1 << KO)) + list(tail), 0, [])
    t_lift = (E, encf((1 << KO)) + list(tail[:-1]), 0, [])
    for nP1 in range(1, 5):
        for nRIP in range(1, 5):
            for nRET in range(1, 7):
                if nP1 is None:
                    continue
                if 2 * nRIP + nRET != b:
                    continue
                for nSTP in range(1, MAXN):
                    for nTRN in range(1, 5):
                        nFIN = a - nP1 - nSTP - nTRN
                        if nFIN < 1:
                            continue
                        s = dict(nP1=nP1, nRIP=nRIP, nRET=nRET, nSTP=nSTP,
                                 nTRN=nTRN, nFIN=nFIN)
                        try:
                            cfg, U = replay_int(ex, E, encf, tail,
                                                m_int(JI), JI, s)
                        except (Wall, KeyError, IndexError):
                            continue
                        if cfg != tgt_i:
                            continue
                        for nSTPO in range(1, MAXN + 10):
                            nFIN2 = (aoa + aob * KO) - (nP1 + nRIP * 2 * (KO - 1)
                                                        + nSTPO + nRET * (KO - 1))
                            if nFIN2 < 1:
                                continue
                            s2 = dict(s, nSTPO=nSTPO, nFIN2=nFIN2)
                            try:
                                cfg2, UO = replay_ov(ex, E, encf, tail,
                                                     (1 << KO) - 1, KO - 1, s2)
                            except (Wall, KeyError, IndexError):
                                continue
                            if cfg2 == t_full:
                                exact_ov = True
                            elif cfg2 == t_lift:
                                exact_ov = False
                            else:
                                continue
                            U.update(UO)
                            return s2, U, exact_ov
    raise DeriveError('no shape-4 skeleton fits both lap branches')


def validate(spec, E, encf, tail, s, exact_ov, hi=160):
    ex = Exec(spec)
    n = 0
    for m in list(range(1, hi)) + [2**10 - 1, 2**10, 2**13 - 1, 2**13 + 5]:
        j, ov = carry(m)
        raw = lap_len(spec, E, encf, tail, m)
        if raw is None:
            raise DeriveError('raw lap does not close at m=%d' % m)
        if ov:
            tgt = (E, encf(m + 1) + list(tail if exact_ov else tail[:-1]),
                   0, [])
            cfg, U = replay_ov(ex, E, encf, tail, m, j - 1, s)
            got = (s['nP1'] + s['nRIP'] * 2 * (j - 1) + s['nSTPO']
                   + s['nRET'] * (j - 1) + s['nFIN2'])
        else:
            tgt = (E, encf(m + 1) + list(tail), 0, [])
            cfg, U = replay_int(ex, E, encf, tail, m, j, s)
            got = (s['nP1'] + s['nRIP'] * 2 * j + s['nSTP'] + s['nTRN']
                   + s['nRET'] * j + s['nFIN'])
        if cfg != tgt:
            raise DeriveError('m=%d: symbolic lap misses the next anchor' % m)
        if got != raw:
            raise DeriveError('m=%d: symbolic %d != raw %d' % (m, got, raw))
        n += 1
    return n


def boot_probe(spec, E, encf, tail, p0, maxT=40000):
    raw = Raw(spec)
    tgt = nrm((E, encf(p0) + list(tail), 0, []))
    cfg = (0, [], 0, [])
    for t in range(maxT):
        if nrm(cfg) == tgt:
            return t
        cfg = raw.step(cfg)
        if cfg is None:
            raise DeriveError('halts during bootstrap at t=%d' % t)
    raise DeriveError('no bootstrap to Cc(%d)' % p0)


def shape_check(s, U, tail):
    """The shape-4 template needs exactly these window shapes."""
    msgs = []
    (Pe, Px) = U['P1']
    (Re, Rx) = U['RIP']
    (Se, Sx) = U['STPI']
    (Ne, Nx) = U['TRN']
    (Te, Tx) = U['RET']
    (Fe, Fx) = U['FIN']
    (Oe, Ox) = U['STPO']
    (Ge, Gx) = U['FIN2']
    E = Pe[0]
    QP = Px[0]
    QR = Tx[0]
    if Pe != (E, (1,), 0, ()) or Px != (QP, (), 1, (0,)):
        msgs.append('P1 %s -> %s is not (E,[S1],S0)->(QP,[],S1,[S0])'
                    % (Pe, Px))
    if Re != (QP, (1,), 1, ()) or Rx != (QP, (), 1, (1,)):
        msgs.append('ripple %s -> %s is not a 1-cell [S1] run' % (Re, Rx))
    if Se != (QP, (0,), 1, ()) or Sx != (QP, (), 0, (1,)):
        msgs.append('interior stop %s -> %s' % (Se, Sx))
    if Ne != (QP, (), 0, (1,)) or Nx != (QR, (1,), 1, ()):
        msgs.append('turn %s -> %s' % (Ne, Nx))
    if Te != (QR, (), 1, (1, 1)) or Tx != (QR, (0, 1), 1, ()):
        msgs.append('return %s -> %s is not [S1;S1]->[S0;S1]' % (Te, Tx))
    if Fe != (QR, (), 1, (0,)) or Fx != (E, (1,), 0, ()):
        msgs.append('close %s -> %s' % (Fe, Fx))
    if Oe != (QP, tuple(tail), 1, ()) or Ox != (QR, (1,), 1, (1,)):
        msgs.append('overflow stop %s -> %s' % (Oe, Ox))
    if Ge[0] != QR or Ge != (QR, (), 1, (1, 0)) or Gx[0] != E or Gx[2] != 0 \
            or Gx[3] != ():
        msgs.append('overflow close %s -> %s' % (Ge, Gx))
    if len({E, QP, QR}) != 3:
        msgs.append('states E/QP/QR collide (%s/%s/%s)'
                    % (LAB[E], LAB[QP], LAB[QR]))
    return msgs, E, QP, QR


def visit_probe4(spec, E, QP, QR, tail, s, U):
    """The remaining state's witness: an offset inside STPO or FIN2."""
    ex = Exec(spec)
    deep = {}
    for q in range(4):
        if q in (E, QP, QR):
            continue
        found = None
        for t in range(1, s['nSTPO']):
            out = ex.wsteps(False, True, QP, list(tail), 1, [], t)
            if out[0] == q:
                found = ('STPO', t,
                         (out[0], tuple(out[1]), out[2], tuple(out[3])))
                break
        if found is None:
            for t in range(1, s['nFIN2']):
                out = ex.wsteps(True, False, QR, [], 1, [1, 0], t)
                if out[0] == q:
                    found = ('FIN2', t,
                             (out[0], tuple(out[1]), out[2], tuple(out[3])))
                    break
        if found is None:
            raise DeriveError('state %s has no witness in STPO or FIN2'
                              % LAB[q])
        deep[q] = found
    if len(deep) != 1:
        raise DeriveError('expected exactly one deep state, got %s'
                          % [LAB[q] for q in deep])
    return deep


def shape_check_flip(s, U, tail, exact_ov):
    """The flip template needs exactly these window shapes."""
    msgs = []
    (Pe, Px) = U['P1']
    (Re, Rx) = U['RIP']
    (Se, Sx) = U['STPI']
    (Ne, Nx) = U['TRN']
    (Te, Tx) = U['RET']
    (Fe, Fx) = U['FIN']
    (Oe, Ox) = U['STPO']
    (Ge, Gx) = U['FIN2']
    E = Pe[0]
    QR = Tx[0]
    if Pe != (E, (), 0, (0,)) or Px != (E, (), 1, (0,)):
        msgs.append('P1 %s -> %s is not a same-state frontier flip' % (Pe, Px))
    if Re != (E, (1,), 1, ()) or Rx != (E, (), 1, (1,)):
        msgs.append('ripple %s -> %s' % (Re, Rx))
    if Se != (E, (0,), 1, ()) or Sx != (E, (), 0, (1,)):
        msgs.append('interior stop %s -> %s' % (Se, Sx))
    if Ne != (E, (), 0, (1,)) or Nx != (QR, (1,), 1, ()):
        msgs.append('turn %s -> %s' % (Ne, Nx))
    if Te != (QR, (), 1, (1, 1)) or Tx != (QR, (0, 1), 1, ()):
        msgs.append('return %s -> %s' % (Te, Tx))
    if Fe != (QR, (), 1, (1, 0)) or Fx != (E, (1,), 0, (0,)):
        msgs.append('close %s -> %s' % (Fe, Fx))
    if Oe != (E, (0,), 1, ()) or Ox != (QR, (1,), 1, ()):
        msgs.append('overflow stop %s -> %s' % (Oe, Ox))
    variant = None
    if s.get('kOFF') == 0 and s.get('nFL2') == 1 \
            and Ge == (QR, (0,), 1, (0,)) and Gx == (E, (1, 0), 0, (0,)):
        variant = 'A'
    elif s.get('kOFF') == 0 and s.get('nFL2') == 0 \
            and Ge == (QR, (), 1, (0,)) and Gx == (E, (1,), 0, (0,)):
        variant = 'B'
    else:
        msgs.append('overflow close %s -> %s (nFL2=%s,kOFF=%s) matches '
                    'neither templated variant'
                    % (Ge, Gx, s.get('nFL2'), s.get('kOFF')))
    if exact_ov:
        msgs.append('exact-overflow flip variant not templated -- report')
    if len({E, QR}) != 2:
        msgs.append('states collide')
    return msgs, E, QR, variant


def visit_probe_flip(spec, E, QR, s, U):
    """QD = the state one step after any (QR, S1) with a right pop; the deep
    state = the remaining one, witnessed at an offset inside FIN2."""
    ex = Exec(spec)
    from emit_interleave import parse
    tab = parse(spec)
    e = tab[(QR, 1)]
    if e is None or e[1] != 1:
        raise DeriveError('QR on S1 does not move right')
    QD = e[2]
    if QD in (E, QR):
        raise DeriveError('QD collides with E/QR')
    deep = {}
    lwin = [0] * s.get('nFL2', 0)
    for q in range(4):
        if q in (E, QR, QD):
            continue
        found = None
        for t in range(1, s['nFIN2']):
            out = ex.wsteps(True, False, QR, list(lwin), 1, [0], t)
            if out[0] == q:
                found = (t, (out[0], tuple(out[1]), out[2], tuple(out[3])))
                break
        if found is None:
            raise DeriveError('state %s has no witness in FIN2' % LAB[q])
        deep[q] = found
    if len(deep) != 1:
        raise DeriveError('expected exactly one deep state, got %s'
                          % [LAB[q] for q in deep])
    return QD, deep


# ------------------------------------------------------------- Coq emission --
HEAD_FLIP = r'''(** * ILS4F_@ID@: frontier-flip [Ip] interleaved binary counter, machine
    @SPEC@ (the affine half of the `+XY|-YX|+XY` lap-shape family).

    Auto-emitted by tools/counters/emit_shape4.py --flip (UNTRUSTED emitter;
    the Coq kernel re-checks every line below).  Left-growth counter under
    the DIRECT interleave encoding [Ip] (ILCounter.v), anchored at

      Cc p = (@EDGE@, (Ip p ++ @TAIL@, S0, @FAR@))

    -- a blank head at the frontier and a blank far-side CELL.  One lap:

      P1   flip the frontier cell inside the far window (@NP1@ steps,
           returning to @EDGE@);
      RIP  leftward 1-cell run (cycL, @NRIP@ step per cell, THROUGH the LSB
           marker: 2j+1 cells interior, 2j'+2 incl the wall on overflow);
      STPI/TRN  pop the clear bit, turn right (interior, @NSTP@+@NTRN@);
      STPO bounce off the synthetic deep blank (@NSTPO@ steps, overflow);
      RET  rightward rewrite cycle [S1;S1] -> [S0;S1] (cycR, @NRET@ steps
           per pair; j pairs interior, S j' on overflow);
      FIN  frontier close (@NFIN@ steps, interior, EXACT) / FIN2 overflow
           close (@NFIN2@ steps, open-right past the far cell, eating the
           last return pair's S0; closes one LEFT blank short -> lift).

    Derived by exact symbolic replay; differentially validated against the
    raw simulator on BOTH cview branches (counts AND exact configurations,
    p = 1..160 plus sparse p to 2^13).  Axiom footprint:
    [functional_extensionality_dep] (via CTape.lift). *)
From Coq Require Import Arith Lia Bool List PArith Wellfounded.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape LapGlue MonoCounter ILCounter JpCounter.
Import ListNotations.

Definition mk_@ID@ (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_@ID@.

(** @SPEC@ *)
Definition tm_@ID@ : TM := fun q s => match q, s with
@TABLE@ end.
Local Notation tm := tm_@ID@.

Definition Cc_@ID@ (p : positive) : cconf := (@EDGE@, (Ip p ++ @TAIL@, S0, @FAR@)).
Local Notation Cc := Cc_@ID@.

(** ** The lap unit windows (each closed by [reflexivity]) *)
Lemma U_P1_@ID@ : wsteps true true tm @NP1@ (@EDGE@,([],S0,[S0])) = Some (@EDGE@,([],S1,[S0])). Proof. reflexivity. Qed.
Lemma U_RIP_@ID@ : wsteps true true tm @NRIP@ (@EDGE@,([S1],S1,[])) = Some (@EDGE@,([],S1,[S1])). Proof. reflexivity. Qed.
Lemma U_STPI_@ID@ : wsteps true true tm @NSTP@ (@EDGE@,([S0],S1,[])) = Some (@EDGE@,([],S0,[S1])). Proof. reflexivity. Qed.
Lemma U_TRN_@ID@ : wsteps true true tm @NTRN@ (@EDGE@,([],S0,[S1])) = Some (@QR@,([S1],S1,[])). Proof. reflexivity. Qed.
Lemma U_RET_@ID@ : wsteps true true tm @NRET@ (@QR@,([],S1,[S1;S1])) = Some (@QR@,([S0;S1],S1,[])). Proof. reflexivity. Qed.
Lemma U_FIN_@ID@ : wsteps true true tm @NFIN@ (@QR@,([],S1,[S1;S0])) = Some (@EDGE@,([S1],S0,[S0])). Proof. reflexivity. Qed.
Lemma U_STPO_@ID@ : wsteps false true tm @NSTPO@ (@EDGE@,([S0],S1,[])) = Some (@QR@,([S1],S1,[])). Proof. reflexivity. Qed.
Lemma U_FIN2_@ID@ : wsteps true false tm @NFIN2@ (@QR@,([S0],S1,[S0])) = Some (@EDGE@,([S1;S0],S0,[S0])). Proof. reflexivity. Qed.
@UVDEEP@
(** ** Transported phases (framing = each unit's bl/br) *)
Lemma phP1_@ID@ : forall L R, csteps tm @NP1@ (@EDGE@,(L,S0,S0::R)) = Some (@EDGE@,(L,S1,S0::R)).
Proof. intros. pose proof (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_P1_@ID@) as H; cbn [app] in H; exact H. Qed.
Lemma phRIP_@ID@ : forall k L R, csteps tm (@NRIP@*k) (@EDGE@,(rep [S1] k ++ L,S1,R)) = Some (@EDGE@,(L,S1,rep [S1] k ++ R)).
Proof. intros. pose proof (cycL _ _ _ _ _ _ _ U_RIP_@ID@ k L R) as H; cbn [app] in H; exact H. Qed.
Lemma phSTPI_@ID@ : forall L R, csteps tm @NSTP@ (@EDGE@,(S0::L,S1,R)) = Some (@EDGE@,(L,S0,S1::R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_STPI_@ID@). Qed.
Lemma phTRN_@ID@ : forall L R, csteps tm @NTRN@ (@EDGE@,(L,S0,S1::R)) = Some (@QR@,(S1::L,S1,R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_TRN_@ID@). Qed.
Lemma phRET_@ID@ : forall k L R, csteps tm (@NRET@*k) (@QR@,(L,S1,rep [S1;S1] k ++ R)) = Some (@QR@,(rep [S0;S1] k ++ L,S1,R)).
Proof. intros. exact (cycR _ _ _ _ _ _ U_RET_@ID@ k L R). Qed.
Lemma phFIN_@ID@ : forall L R, csteps tm @NFIN@ (@QR@,(L,S1,S1::S0::R)) = Some (@EDGE@,(S1::L,S0,S0::R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_FIN_@ID@). Qed.
Lemma phSTPO_@ID@ : forall R, csteps tm @NSTPO@ (@EDGE@,([S0],S1,R)) = Some (@QR@,([S1],S1,R)).
Proof. intros. exact (wsteps_frame_l _ _ _ _ _ _ _ _ _ _ R U_STPO_@ID@). Qed.
Lemma phFIN2_@ID@ : forall L, csteps tm @NFIN2@ (@QR@,(S0::L,S1,[S0])) = Some (@EDGE@,(S1::S0::L,S0,[S0])).
Proof. intros. exact (wsteps_frame_r _ _ _ _ _ _ _ _ _ _ L U_FIN2_@ID@). Qed.
Lemma phVD_@ID@ : forall x L R, csteps tm 1 (@QR@,(L,S1,x::R)) = Some (@QD@,(S1::L,x,R)).
Proof. intros. reflexivity. Qed.
@PHVDEEP@
(** ** The lap

    Interior branch: EXACT (the next anchor on the nose) -- the deep-visit
    induction below chains on this equality. *)
Lemma lap_int_@ID@ : forall p j q0, cview p = (j, Some q0) ->
  exists n c', csteps tm n (Cc p) = Some c' /\ c' = Cc (Pos.succ p) /\ 0 < n.
Proof.
  intros p j q0 Ecv. unfold Cc_@ID@.
  destruct (cview_some_I p j q0 Ecv) as (HIp & HIs).
  do 2 eexists. split; [|split].
  + rewrite HIp, <- app_assoc. cbn [app].
    rewrite rep_dbl, <- rep_slide.
    eapply csteps_chain. { apply phP1_@ID@. }
    eapply csteps_chain. { apply (phRIP_@ID@ (S (2*j))). }
    eapply csteps_chain. { apply phSTPI_@ID@. }
    eapply csteps_chain. { apply phTRN_@ID@. }
    change (rep [S1] (S (2*j)) ++ @FAR@) with (S1 :: rep [S1] (2*j) ++ @FAR@).
    rewrite rep_slide, <- rep_dbl.
    eapply csteps_chain. { apply (phRET_@ID@ j). }
    apply phFIN_@ID@.
  + rewrite HIs, <- app_assoc. cbn [app].
    change (rep [S1;S0] j ++ S1 :: S1 :: (Ip q0 ++ @TAIL@))
      with (rep [S1;S0] j ++ [S1] ++ (S1 :: (Ip q0 ++ @TAIL@))).
    rewrite app_assoc, pair_rot. reflexivity.
  + lia.
Qed.

Lemma lift_lblank_@ID@ : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.

(** Wall-overflow close: the overflow rebuilds the wall one cell deeper and
    consumes the anchor's synthetic deep blank; the two agree under [lift]. *)
Lemma closeO_@ID@ : forall (l : list Sym) q h r,
  lift (q,(l ++ @TOV@,h,r)) = lift (q,(l ++ @TAIL@,h,r)).
Proof.
  intros.
  replace (l ++ @TAIL@) with ((l ++ @TOV@) ++ [S0])
    by (rewrite <- app_assoc; reflexivity).
  rewrite lift_lblank_@ID@. reflexivity.
Qed.

Lemma lap_ov_@ID@ : forall p j', cview p = (S j', None) ->
  exists n c', csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p j' Ecv. unfold Cc_@ID@.
  destruct (cview_none_I p j' Ecv) as (HIp & HIs).
  do 2 eexists. split; [|split].
  + rewrite HIp, <- app_assoc. cbn [app].
    rewrite rep_dbl, <- !rep_slide.
    eapply csteps_chain. { apply phP1_@ID@. }
    eapply csteps_chain. { apply (phRIP_@ID@ (S (S (2*j')))). }
    eapply csteps_chain. { apply phSTPO_@ID@. }
    change (rep [S1] (S (S (2*j'))) ++ @FAR@)
      with (S1 :: S1 :: rep [S1] (2*j') ++ @FAR@).
    rewrite <- rep_dbl.
    change (S1 :: S1 :: rep [S1;S1] j' ++ @FAR@)
      with (rep [S1;S1] (S j') ++ @FAR@).
    eapply csteps_chain. { apply (phRET_@ID@ (S j')). }
    change (rep [S0;S1] (S j') ++ [S1]) with (S0 :: S1 :: rep [S0;S1] j' ++ [S1]).
    apply phFIN2_@ID@.
  + rewrite HIs, <- app_assoc. cbn [app].
    change (rep [S1;S0] (S j') ++ S1 :: @TAILC@)
      with (rep [S1;S0] (S j') ++ [S1] ++ @TAIL@).
    rewrite app_assoc, pair_rot.
    apply (closeO_@ID@ (S1 :: S0 :: S1 :: rep [S0;S1] j')).
  + lia.
Qed.

Lemma lap_@ID@ : forall p, exists n c', csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:Ecv. destruct oq as [q0|].
  - destruct (lap_int_@ID@ p j q0 Ecv) as (n & c' & H1 & H2 & H3).
    exists n, c'. split; [exact H1|split; [rewrite H2; reflexivity|exact H3]].
  - destruct j as [|j'].
    { exfalso. destruct p; simpl in Ecv; [destruct (cview p); discriminate|discriminate|discriminate]. }
    exact (lap_ov_@ID@ p j' Ecv).
Qed.

Lemma boot_@ID@ : exists t0, stepn tm t0 InitES = Some (lift (Cc @P0@)).
Proof.
  exists @BOOT@.
  assert (H : match csteps tm @BOOT@ c0 with Some c => ceqb c (Cc @P0@) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm @BOOT@ c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** ** Visits *)

@VISDEEP@
(** @QR@ is entered by TRN (interior) and the overflow stop; @QD@ one step
    later (the return partner never branches on the popped cell). *)
Lemma vis_R_@ID@ : forall p, exists k c, csteps tm k (Cc p) = Some c /\ fst c = @QR@.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:Ecv. destruct oq as [q0|].
  - destruct (cview_some_I p j q0 Ecv) as (HIp & _).
    unfold Cc_@ID@. eexists. eexists. split.
    + rewrite HIp, <- app_assoc. cbn [app].
      rewrite rep_dbl, <- rep_slide.
      eapply csteps_chain. { apply phP1_@ID@. }
      eapply csteps_chain. { apply (phRIP_@ID@ (S (2*j))). }
      eapply csteps_chain. { apply phSTPI_@ID@. }
      apply phTRN_@ID@.
    + reflexivity.
  - destruct j as [|j'].
    { exfalso. destruct p; simpl in Ecv; [destruct (cview p); discriminate|discriminate|discriminate]. }
    destruct (cview_none_I p j' Ecv) as (HIp & _).
    unfold Cc_@ID@. eexists. eexists. split.
    + rewrite HIp, <- app_assoc. cbn [app].
      rewrite rep_dbl, <- !rep_slide.
      eapply csteps_chain. { apply phP1_@ID@. }
      eapply csteps_chain. { apply (phRIP_@ID@ (S (S (2*j')))). }
      apply phSTPO_@ID@.
    + reflexivity.
Qed.

Lemma vis_D_@ID@ : forall p, exists k c, csteps tm k (Cc p) = Some c /\ fst c = @QD@.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:Ecv. destruct oq as [q0|].
  - destruct (cview_some_I p j q0 Ecv) as (HIp & _).
    unfold Cc_@ID@. eexists. eexists. split.
    + rewrite HIp, <- app_assoc. cbn [app].
      rewrite rep_dbl, <- rep_slide.
      eapply csteps_chain. { apply phP1_@ID@. }
      eapply csteps_chain. { apply (phRIP_@ID@ (S (2*j))). }
      eapply csteps_chain. { apply phSTPI_@ID@. }
      eapply csteps_chain. { apply phTRN_@ID@. }
      change (rep [S1] (S (2*j)) ++ @FAR@) with (S1 :: rep [S1] (2*j) ++ @FAR@).
      apply phVD_@ID@.
    + reflexivity.
  - destruct j as [|j'].
    { exfalso. destruct p; simpl in Ecv; [destruct (cview p); discriminate|discriminate|discriminate]. }
    destruct (cview_none_I p j' Ecv) as (HIp & _).
    unfold Cc_@ID@. eexists. eexists. split.
    + rewrite HIp, <- app_assoc. cbn [app].
      rewrite rep_dbl, <- !rep_slide.
      eapply csteps_chain. { apply phP1_@ID@. }
      eapply csteps_chain. { apply (phRIP_@ID@ (S (S (2*j')))). }
      eapply csteps_chain. { apply phSTPO_@ID@. }
      change (rep [S1] (S (S (2*j'))) ++ @FAR@)
        with (S1 :: rep [S1] (S (2*j')) ++ @FAR@).
      apply phVD_@ID@.
    + reflexivity.
Qed.

Lemma vis_@ID@ : forall p q, exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros p q. destruct q.
@VISCASES@
Qed.

Theorem nqh_@ID@ : NeverQuasiHaltsSt tm.
Proof. apply (glue_neverqh tm Cc @P0@). - exact boot_@ID@. - intros p _. apply lap_@ID@. - intros p q _. apply vis_@ID@. Qed.

Theorem nonhalt_@ID@ : NonHalt tm.
Proof. apply never_qh_nonhalt, nqh_@ID@. Qed.
'''

VISDEEP_FLIP = r'''(** @QZ@ fires only inside the overflow close; reach the close's entry
    landmark by well-founded induction on [tovf] (strictly decreasing along
    interior laps, which close EXACTLY), then run a prefix of the close. *)
Lemma reach_fin2_@ID@ : forall p, exists k L, csteps tm k (Cc p) = Some (@QR@,(S0::L,S1,@FAR@)).
Proof.
  intro p; remember (tovf p) as fuel eqn:Ef; revert p Ef.
  induction fuel as [fuel IH] using (well_founded_induction lt_wf); intros p Ef.
  destruct (cview p) as [j oq] eqn:Ecv. destruct oq as [q0|].
  - assert (Hnz : tovf p <> 0).
    { intro H0. destruct (tovf0_allones p H0) as (jj & Hjj). rewrite Hjj in Ecv; discriminate. }
    destruct (lap_int_@ID@ p j q0 Ecv) as (n & c' & Hrun & Hc' & _). subst c'.
    destruct (IH (tovf (Pos.succ p)) (ltac:(rewrite tovf_succ by lia; lia)) (Pos.succ p) eq_refl) as (k & L & Hk).
    exists (n + k), L. rewrite csteps_add, Hrun. exact Hk.
  - destruct j as [|j'].
    { exfalso. destruct p; simpl in Ecv; [destruct (cview p); discriminate|discriminate|discriminate]. }
    destruct (cview_none_I p j' Ecv) as (HIp & _).
    unfold Cc_@ID@. eexists. eexists.
    rewrite HIp, <- app_assoc. cbn [app].
    rewrite rep_dbl, <- !rep_slide.
    eapply csteps_chain. { apply phP1_@ID@. }
    eapply csteps_chain. { apply (phRIP_@ID@ (S (S (2*j')))). }
    eapply csteps_chain. { apply phSTPO_@ID@. }
    change (rep [S1] (S (S (2*j'))) ++ @FAR@)
      with (S1 :: S1 :: rep [S1] (2*j') ++ @FAR@).
    rewrite <- rep_dbl.
    change (S1 :: S1 :: rep [S1;S1] j' ++ @FAR@)
      with (rep [S1;S1] (S j') ++ @FAR@).
    apply (phRET_@ID@ (S j')).
Qed.

Lemma vis_Z_@ID@ : forall p, exists k c, csteps tm k (Cc p) = Some c /\ fst c = @QZ@.
Proof.
  intro p. destruct (reach_fin2_@ID@ p) as (k & L & Hk).
  exists (k + @OZ@). eexists. rewrite csteps_add, Hk. split.
  - apply phVZ_@ID@.
  - reflexivity.
Qed.
'''

HEAD = r'''(** * ILS4_@ID@: 2-phase [Ip] interleaved binary counter, machine
    @SPEC@ (lap-shape rank 4, `-DA|+AB`, of tools/counter_lapshapes.tsv).

    Auto-emitted by tools/counters/emit_shape4.py (UNTRUSTED emitter; the Coq
    kernel re-checks every line below).  Left-growth counter under the DIRECT
    interleave encoding [Ip] (ILCounter.v), anchored at

      Cc p = (@EDGE@, (Ip p ++ @TAIL@, S0, []))

    -- the counter on the LEFT list nearest-first, a blank head at the fixed
    right frontier, EMPTY far side (the interior lap never looks right of
    the frontier).  One lap Cc p -> Cc (p+1):

      P1   pop the LSB marker (@NP1@ step);
      RIP  leftward 1-cell run over the set region (cycL, @NRIP@ step per
           cell, 2j cells);
      STPI pop the stopping pair's clear bit / TRN turn right (interior);
      STPO run through the tail wall off the deep edge (overflow,
           @NSTPO@ steps);
      RET  rightward rewrite cycle [S1;S1] -> [S0;S1] (cycR, @NRET@ steps
           per pair, j pairs) -- the classic Ip return;
      FIN  frontier close: interior @NFIN@ step, EXACT; overflow @NFIN2@
           steps, an open-right excursion that grows the LSB pair past the
           old frontier and closes one LEFT blank short of the anchor tail
           (lift close; the interior stays exact, feeding the deep-visit
           induction).

    Step counts were derived by exact symbolic replay and the decomposition
    was differentially validated against the raw simulator on BOTH cview
    branches (step counts AND exact configurations, p = 1..160 plus sparse
    p up to 2^13).  Axiom footprint: [functional_extensionality_dep] (via
    CTape.lift). *)
From Coq Require Import Arith Lia Bool List PArith Wellfounded.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape LapGlue MonoCounter ILCounter JpCounter.
Import ListNotations.

Definition mk_@ID@ (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_@ID@.

(** @SPEC@ *)
Definition tm_@ID@ : TM := fun q s => match q, s with
@TABLE@ end.
Local Notation tm := tm_@ID@.

Definition Cc_@ID@ (p : positive) : cconf := (@EDGE@, (Ip p ++ @TAIL@, S0, [])).
Local Notation Cc := Cc_@ID@.

(** ** The lap unit windows (each closed by [reflexivity]) *)
Lemma U_P1_@ID@ : wsteps true true tm @NP1@ (@EDGE@,([S1],S0,[])) = Some (@QP@,([],S1,[S0])). Proof. reflexivity. Qed.
Lemma U_RIP_@ID@ : wsteps true true tm @NRIP@ (@QP@,([S1],S1,[])) = Some (@QP@,([],S1,[S1])). Proof. reflexivity. Qed.
Lemma U_STPI_@ID@ : wsteps true true tm @NSTP@ (@QP@,([S0],S1,[])) = Some (@QP@,([],S0,[S1])). Proof. reflexivity. Qed.
Lemma U_TRN_@ID@ : wsteps true true tm @NTRN@ (@QP@,([],S0,[S1])) = Some (@QR@,([S1],S1,[])). Proof. reflexivity. Qed.
Lemma U_RET_@ID@ : wsteps true true tm @NRET@ (@QR@,([],S1,[S1;S1])) = Some (@QR@,([S0;S1],S1,[])). Proof. reflexivity. Qed.
Lemma U_FIN_@ID@ : wsteps true true tm @NFIN@ (@QR@,([],S1,[S0])) = Some (@EDGE@,([S1],S0,[])). Proof. reflexivity. Qed.
Lemma U_STPO_@ID@ : wsteps false true tm @NSTPO@ (@QP@,(@TAIL@,S1,[])) = Some (@QR@,([S1],S1,[S1])). Proof. reflexivity. Qed.
Lemma U_FIN2_@ID@ : wsteps true false tm @NFIN2@ (@QR@,([],S1,[S1;S0])) = Some (@EDGE@,(@F2DEP@,S0,[])). Proof. reflexivity. Qed.
@UVDEEP@
(** ** Transported phases (framing = each unit's bl/br) *)
Lemma phP1_@ID@ : forall L R, csteps tm @NP1@ (@EDGE@,(S1::L,S0,R)) = Some (@QP@,(L,S1,S0::R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_P1_@ID@). Qed.
Lemma phRIP_@ID@ : forall k L R, csteps tm (@NRIP@*k) (@QP@,(rep [S1] k ++ L,S1,R)) = Some (@QP@,(L,S1,rep [S1] k ++ R)).
Proof. intros. pose proof (cycL _ _ _ _ _ _ _ U_RIP_@ID@ k L R) as H; cbn [app] in H; exact H. Qed.
Lemma phSTPI_@ID@ : forall L R, csteps tm @NSTP@ (@QP@,(S0::L,S1,R)) = Some (@QP@,(L,S0,S1::R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_STPI_@ID@). Qed.
Lemma phTRN_@ID@ : forall L R, csteps tm @NTRN@ (@QP@,(L,S0,S1::R)) = Some (@QR@,(S1::L,S1,R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_TRN_@ID@). Qed.
Lemma phRET_@ID@ : forall k L R, csteps tm (@NRET@*k) (@QR@,(L,S1,rep [S1;S1] k ++ R)) = Some (@QR@,(rep [S0;S1] k ++ L,S1,R)).
Proof. intros. exact (cycR _ _ _ _ _ _ U_RET_@ID@ k L R). Qed.
Lemma phFIN_@ID@ : forall L R, csteps tm @NFIN@ (@QR@,(L,S1,S0::R)) = Some (@EDGE@,(S1::L,S0,R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_FIN_@ID@). Qed.
Lemma phSTPO_@ID@ : forall R, csteps tm @NSTPO@ (@QP@,(@TAIL@,S1,R)) = Some (@QR@,([S1],S1,S1::R)).
Proof. intros. exact (wsteps_frame_l _ _ _ _ _ _ _ _ _ _ R U_STPO_@ID@). Qed.
Lemma phFIN2_@ID@ : forall L, csteps tm @NFIN2@ (@QR@,(L,S1,[S1;S0])) = Some (@EDGE@,(@F2DEPC@L,S0,[])).
Proof. intros. exact (wsteps_frame_r _ _ _ _ _ _ _ _ _ _ L U_FIN2_@ID@). Qed.
@PHVDEEP@
(** ** The lap

    Interior branch: EXACT (the next anchor on the nose) -- the deep-visit
    induction below chains on this equality. *)
Lemma lap_int_@ID@ : forall p j q0, cview p = (j, Some q0) ->
  exists n c', csteps tm n (Cc p) = Some c' /\ c' = Cc (Pos.succ p) /\ 0 < n.
Proof.
  intros p j q0 Ecv. unfold Cc_@ID@.
  destruct (cview_some_I p j q0 Ecv) as (HIp & HIs).
  do 2 eexists. split; [|split].
  + rewrite HIp, <- app_assoc. cbn [app].
    rewrite rep_dbl, <- rep_slide.
    eapply csteps_chain. { apply phP1_@ID@. }
    eapply csteps_chain. { apply phRIP_@ID@. }
    eapply csteps_chain. { apply phSTPI_@ID@. }
    eapply csteps_chain. { apply phTRN_@ID@. }
    rewrite <- rep_dbl.
    eapply csteps_chain. { apply (phRET_@ID@ j). }
    apply phFIN_@ID@.
  + rewrite HIs, <- app_assoc. cbn [app].
    change (rep [S1;S0] j ++ S1 :: S1 :: (Ip q0 ++ @TAIL@))
      with (rep [S1;S0] j ++ [S1] ++ (S1 :: (Ip q0 ++ @TAIL@))).
    rewrite app_assoc, pair_rot. reflexivity.
  + lia.
Qed.

Lemma lift_lblank_@ID@ : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.

(** Wall-overflow close: the overflow rebuilds the wall one cell deeper and
    consumes the anchor's synthetic deep blank; the two agree under [lift]. *)
Lemma closeO_@ID@ : forall (l : list Sym) q h r,
  lift (q,(l ++ @TOV@,h,r)) = lift (q,(l ++ @TAIL@,h,r)).
Proof.
  intros.
  replace (l ++ @TAIL@) with ((l ++ @TOV@) ++ [S0])
    by (rewrite <- app_assoc; reflexivity).
  rewrite lift_lblank_@ID@. reflexivity.
Qed.

Lemma lap_ov_@ID@ : forall p j', cview p = (S j', None) ->
  exists n c', csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p j' Ecv. unfold Cc_@ID@.
  destruct (cview_none_I p j' Ecv) as (HIp & HIs).
  do 2 eexists. split; [|split].
  + rewrite HIp, <- app_assoc. cbn [app].
    rewrite rep_dbl, <- rep_slide.
    eapply csteps_chain. { apply phP1_@ID@. }
    eapply csteps_chain. { apply phRIP_@ID@. }
    eapply csteps_chain. { apply phSTPO_@ID@. }
    rewrite rep_slide, <- rep_dbl.
    eapply csteps_chain. { apply (phRET_@ID@ j'). }
    apply phFIN2_@ID@.
  + rewrite HIs, <- app_assoc. cbn [app].
    change (rep [S1;S0] (S j') ++ S1 :: @TAILC@)
      with (rep [S1;S0] (S j') ++ [S1] ++ @TAIL@).
    rewrite app_assoc, pair_rot.
    apply (closeO_@ID@ (@F2DEPC@rep [S0;S1] j')).
  + lia.
Qed.

Lemma lap_@ID@ : forall p, exists n c', csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:Ecv. destruct oq as [q0|].
  - destruct (lap_int_@ID@ p j q0 Ecv) as (n & c' & H1 & H2 & H3).
    exists n, c'. split; [exact H1|split; [rewrite H2; reflexivity|exact H3]].
  - destruct j as [|j'].
    { exfalso. destruct p; simpl in Ecv; [destruct (cview p); discriminate|discriminate|discriminate]. }
    exact (lap_ov_@ID@ p j' Ecv).
Qed.

Lemma boot_@ID@ : exists t0, stepn tm t0 InitES = Some (lift (Cc @P0@)).
Proof.
  exists @BOOT@.
  assert (H : match csteps tm @BOOT@ c0 with Some c => ceqb c (Cc @P0@) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm @BOOT@ c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** ** Visits *)

@VISDEEP@
(** @QR@ is entered by TRN (interior) and by the overflow stop, so every
    lap visits it. *)
Lemma vis_R_@ID@ : forall p, exists k c, csteps tm k (Cc p) = Some c /\ fst c = @QR@.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:Ecv. destruct oq as [q0|].
  - destruct (cview_some_I p j q0 Ecv) as (HIp & _).
    unfold Cc_@ID@. eexists. eexists. split.
    + rewrite HIp, <- app_assoc. cbn [app].
      rewrite rep_dbl, <- rep_slide.
      eapply csteps_chain. { apply phP1_@ID@. }
      eapply csteps_chain. { apply phRIP_@ID@. }
      eapply csteps_chain. { apply phSTPI_@ID@. }
      apply phTRN_@ID@.
    + reflexivity.
  - destruct j as [|j'].
    { exfalso. destruct p; simpl in Ecv; [destruct (cview p); discriminate|discriminate|discriminate]. }
    destruct (cview_none_I p j' Ecv) as (HIp & _).
    unfold Cc_@ID@. eexists. eexists. split.
    + rewrite HIp, <- app_assoc. cbn [app].
      rewrite rep_dbl, <- rep_slide.
      eapply csteps_chain. { apply phP1_@ID@. }
      eapply csteps_chain. { apply phRIP_@ID@. }
      apply phSTPO_@ID@.
    + reflexivity.
Qed.

Lemma vis_@ID@ : forall p q, exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros p q. destruct q.
@VISCASES@
Qed.

Theorem nqh_@ID@ : NeverQuasiHaltsSt tm.
Proof. apply (glue_neverqh tm Cc @P0@). - exact boot_@ID@. - intros p _. apply lap_@ID@. - intros p q _. apply vis_@ID@. Qed.

Theorem nonhalt_@ID@ : NonHalt tm.
Proof. apply never_qh_nonhalt, nqh_@ID@. Qed.
'''

VISDEEP4 = r'''(** @QZ@ fires only inside the overflow close; reach the close's entry
    landmark by well-founded induction on [tovf] (strictly decreasing along
    interior laps, which close EXACTLY), then run a prefix of the close. *)
Lemma reach_fin2_@ID@ : forall p, exists k L, csteps tm k (Cc p) = Some (@QR@,(L,S1,[S1;S0])).
Proof.
  intro p; remember (tovf p) as fuel eqn:Ef; revert p Ef.
  induction fuel as [fuel IH] using (well_founded_induction lt_wf); intros p Ef.
  destruct (cview p) as [j oq] eqn:Ecv. destruct oq as [q0|].
  - assert (Hnz : tovf p <> 0).
    { intro H0. destruct (tovf0_allones p H0) as (jj & Hjj). rewrite Hjj in Ecv; discriminate. }
    destruct (lap_int_@ID@ p j q0 Ecv) as (n & c' & Hrun & Hc' & _). subst c'.
    destruct (IH (tovf (Pos.succ p)) (ltac:(rewrite tovf_succ by lia; lia)) (Pos.succ p) eq_refl) as (k & L & Hk).
    exists (n + k), L. rewrite csteps_add, Hrun. exact Hk.
  - destruct j as [|j'].
    { exfalso. destruct p; simpl in Ecv; [destruct (cview p); discriminate|discriminate|discriminate]. }
    destruct (cview_none_I p j' Ecv) as (HIp & _).
    unfold Cc_@ID@. eexists. eexists.
    rewrite HIp, <- app_assoc. cbn [app].
    rewrite rep_dbl, <- rep_slide.
    eapply csteps_chain. { apply phP1_@ID@. }
    eapply csteps_chain. { apply phRIP_@ID@. }
    eapply csteps_chain. { apply phSTPO_@ID@. }
    rewrite rep_slide, <- rep_dbl.
    apply (phRET_@ID@ j').
Qed.

Lemma vis_Z_@ID@ : forall p, exists k c, csteps tm k (Cc p) = Some c /\ fst c = @QZ@.
Proof.
  intro p. destruct (reach_fin2_@ID@ p) as (k & L & Hk).
  exists (k + @OZ@). eexists. rewrite csteps_add, Hk. split.
  - apply phVZ_@ID@.
  - reflexivity.
Qed.
'''


def emit_source(spec, E, QP, QR, tail, p0, boot, s, U, deep):
    ID = mach_id(spec)
    (Ge, Gx) = U['FIN2']
    qz = list(deep.keys())[0]
    where, tz, ext = deep[qz]
    if where != 'FIN2':
        raise DeriveError('deep state %s is in %s; only the FIN2 route is '
                          'templated -- report' % (LAB[qz], where))
    t_ov = list(tail[:-1])
    sub = {
        '@ID@': ID, '@SPEC@': spec, '@TABLE@': coq_table(spec),
        '@EDGE@': ST[E], '@QP@': ST[QP], '@QR@': ST[QR], '@QZ@': ST[qz],
        '@TAIL@': clist(tail), '@TAILC@': ccons(tail, '[]'),
        '@TOV@': clist(t_ov),
        '@P0@': str(p0), '@BOOT@': str(boot),
        '@NP1@': str(s['nP1']), '@NRIP@': str(s['nRIP']),
        '@NSTP@': str(s['nSTP']), '@NTRN@': str(s['nTRN']),
        '@NRET@': str(s['nRET']), '@NFIN@': str(s['nFIN']),
        '@NSTPO@': str(s['nSTPO']), '@NFIN2@': str(s['nFIN2']),
        '@F2DEP@': clist(Gx[1]), '@F2DEPC@': ccons(Gx[1], ''),
        '@OZ@': str(tz),
    }
    sub['@UVDEEP@'] = (
        'Lemma U_VZ_@ID@ : wsteps true false tm %d (@QR@,([],S1,[S1;S0])) '
        '= Some %s. Proof. reflexivity. Qed.\n' % (tz, cwin(ext)))
    sub['@PHVDEEP@'] = (
        'Lemma phVZ_@ID@ : forall L, csteps tm %d (@QR@,(L,S1,[S1;S0])) '
        '= Some (%s,(%s,%s,%s)).\n'
        'Proof. intros. exact (wsteps_frame_r _ _ _ _ _ _ _ _ _ _ L '
        'U_VZ_@ID@). Qed.\n'
        % (tz, ST[ext[0]], ccons(ext[1], 'L'), SYM[ext[2]], clist(ext[3])))
    sub['@VISDEEP@'] = VISDEEP4
    cases = []
    for q in range(4):
        if q == E:
            cases.append('  - (* %s : the anchor state *)\n'
                         '    exists 0. eexists. split; reflexivity.' % ST[q])
        elif q == QP:
            cases.append(
                '  - (* %s : 1 step from the anchor (P1) *)\n'
                '    destruct (Ip_head p) as (w & Hw). unfold Cc_@ID@.\n'
                '    rewrite Hw. cbn [app]. exists @NP1@. eexists. split.\n'
                '    + apply phP1_@ID@.\n'
                '    + reflexivity.' % ST[q])
        elif q == QR:
            cases.append('  - apply vis_R_@ID@.')
        elif q == qz:
            cases.append('  - apply vis_Z_@ID@.')
        else:
            raise DeriveError('state %s has no visit case' % LAB[q])
    sub['@VISCASES@'] = '\n'.join(cases)
    src = HEAD
    for _ in range(3):
        for k, v in sorted(sub.items(), key=lambda kv: -len(kv[0])):
            src = src.replace(k, v)
    return src


def emit_source_flip(spec, E, QR, QD, tail, p0, boot, s, U, deep,
                     variant='A'):
    ID = mach_id(spec)
    qz = list(deep.keys())[0]
    tz, ext = deep[qz]
    sub = {
        '@ID@': ID, '@SPEC@': spec, '@TABLE@': coq_table(spec),
        '@EDGE@': ST[E], '@QR@': ST[QR], '@QD@': ST[QD], '@QZ@': ST[qz],
        '@TAIL@': clist(tail), '@TAILC@': ccons(tail, '[]'),
        '@TOV@': clist(tail[:-1]), '@FAR@': '[S0]',
        '@P0@': str(p0), '@BOOT@': str(boot),
        '@NP1@': str(s['nP1']), '@NRIP@': str(s['nRIP']),
        '@NSTP@': str(s['nSTP']), '@NTRN@': str(s['nTRN']),
        '@NRET@': str(s['nRET']), '@NFIN@': str(s['nFIN']),
        '@NSTPO@': str(s['nSTPO']), '@NFIN2@': str(s['nFIN2']),
        '@OZ@': str(tz),
    }
    went = '[S0]' if variant == 'A' else '[]'
    wentc = 'S0::L' if variant == 'A' else 'L'
    sub['@UVDEEP@'] = (
        'Lemma U_VZ_@ID@ : wsteps true false tm %d (@QR@,(%s,S1,[S0])) '
        '= Some %s. Proof. reflexivity. Qed.\n' % (tz, went, cwin(ext)))
    sub['@PHVDEEP@'] = (
        'Lemma phVZ_@ID@ : forall L, csteps tm %d (@QR@,(%s,S1,[S0])) '
        '= Some (%s,(%s,%s,%s)).\n'
        'Proof. intros. exact (wsteps_frame_r _ _ _ _ _ _ _ _ _ _ L '
        'U_VZ_@ID@). Qed.\n'
        % (tz, wentc, ST[ext[0]], ccons(ext[1], 'L'), SYM[ext[2]],
           clist(ext[3])))
    sub['@VISDEEP@'] = VISDEEP_FLIP
    cases = []
    for q in range(4):
        if q == E:
            cases.append('  - (* %s : the anchor state *)\n'
                         '    exists 0. eexists. split; reflexivity.' % ST[q])
        elif q == QR:
            cases.append('  - apply vis_R_@ID@.')
        elif q == QD:
            cases.append('  - apply vis_D_@ID@.')
        elif q == qz:
            cases.append('  - apply vis_Z_@ID@.')
        else:
            raise DeriveError('state %s has no visit case' % LAB[q])
    sub['@VISCASES@'] = '\n'.join(cases)
    src = HEAD_FLIP
    if variant == 'B':
        # the +AB-family close: no left window, deposit [S1] -- simpler
        src = src.replace(
            'Lemma U_FIN2_@ID@ : wsteps true false tm @NFIN2@ '
            '(@QR@,([S0],S1,[S0])) = Some (@EDGE@,([S1;S0],S0,[S0])).',
            'Lemma U_FIN2_@ID@ : wsteps true false tm @NFIN2@ '
            '(@QR@,([],S1,[S0])) = Some (@EDGE@,([S1],S0,[S0])).')
        src = src.replace(
            'Lemma phFIN2_@ID@ : forall L, csteps tm @NFIN2@ '
            '(@QR@,(S0::L,S1,[S0])) = Some (@EDGE@,(S1::S0::L,S0,[S0])).',
            'Lemma phFIN2_@ID@ : forall L, csteps tm @NFIN2@ '
            '(@QR@,(L,S1,[S0])) = Some (@EDGE@,(S1::L,S0,[S0])).')
        src = src.replace(
            "    change (rep [S0;S1] (S j') ++ [S1]) with "
            "(S0 :: S1 :: rep [S0;S1] j' ++ [S1]).\n"
            '    apply phFIN2_@ID@.',
            '    apply phFIN2_@ID@.')
        src = src.replace(
            "    apply (closeO_@ID@ (S1 :: S0 :: S1 :: rep [S0;S1] j')).",
            "    apply (closeO_@ID@ (S1 :: rep [S0;S1] (S j'))).")
        src = src.replace(
            'Lemma reach_fin2_@ID@ : forall p, exists k L, '
            'csteps tm k (Cc p) = Some (@QR@,(S0::L,S1,@FAR@)).',
            'Lemma reach_fin2_@ID@ : forall p, exists k L, '
            'csteps tm k (Cc p) = Some (@QR@,(L,S1,@FAR@)).')
    for _ in range(3):
        for k, v in sorted(sub.items(), key=lambda kv: -len(kv[0])):
            src = src.replace(k, v)
    return src


def coqc(path):
    p = subprocess.run(
        ['bash', '-lc', 'cd %s && coqc -native-compiler no -Q theories BBB4 %s'
         % (REPO, path)], capture_output=True, text=True, timeout=1800)
    return p.returncode, p.stdout + p.stderr


def print_assumptions(ID, scratch, pref='ILS4'):
    chk = os.path.join(scratch, 'pa4_%s.v' % ID)
    with open(chk, 'w') as f:
        f.write('From BBB4.Machines.Counters Require Import %s_%s.\n'
                'Print Assumptions nqh_%s.\n' % (pref, ID, ID))
    return coqc(chk)


def process(spec, do_emit, scratch, force=False, windows=False):
    res = {'spec': spec, 'ok': False}
    try:
        edge, tail, p0 = derive_tail(spec, 'A', encname='Ip')
        E = LAB.index(edge)
        encf = ENC['Ip']
        pr = profile(spec, E, encf, tail)
        if pr is None:
            raise DeriveError('laps not affine on both branches')
        flip = False
        try:
            s, U, exact_ov = derive(spec, E, encf, tail, *pr)
        except DeriveError:
            flip = True
            s, U, exact_ov = derive_flip(spec, E, encf, tail, *pr)
        if flip:
            msgs, E2, QR, fvariant = shape_check_flip(s, U, tail, exact_ov)
            if msgs:
                raise DeriveError('flip shape: ' + '; '.join(msgs))
            QD, deep = visit_probe_flip(spec, E, QR, s, U)
            QP = QD
            nchk = validate_flip(spec, E, encf, tail, s, exact_ov)
        else:
            if exact_ov:
                raise DeriveError('exact-overflow variant not templated '
                                  '-- report')
            msgs, E2, QP, QR = shape_check(s, U, tail)
            if msgs:
                raise DeriveError('shape: ' + '; '.join(msgs))
            deep = visit_probe4(spec, E, QP, QR, tail, s, U)
            nchk = validate(spec, E, encf, tail, s, exact_ov)
        boot = boot_probe(spec, E, encf, tail, p0)
    except (DeriveError, Wall, AssertionError, KeyError, IndexError) as e:
        res['why'] = str(e)
        return res
    res.update({'edge': edge, 'tail': list(tail), 'p0': p0, 'boot': boot,
                'skel': s, 'exact_ov': exact_ov, 'nchecked': nchk,
                'flip': flip, 'QP': LAB[QP], 'QR': LAB[QR],
                'deep': {LAB[q]: v[:-1] for q, v in deep.items()}})
    if windows:
        res['U'] = {k: repr(v) for k, v in U.items()}
    if not do_emit:
        res['ok'] = True
        res['why'] = 'derived+validated (not emitted)'
        return res
    ID = mach_id(spec)
    pref = 'ILS4F' if flip else 'ILS4'
    path = os.path.join(OUTDIR, '%s_%s.v' % (pref, ID))
    if os.path.exists(path) and not force:
        res['ok'] = True
        res['why'] = 'file exists -- skipped emission'
        return res
    try:
        if flip:
            src = emit_source_flip(spec, E, QR, QP, tail, p0, boot, s, U,
                                   deep, fvariant)
        else:
            src = emit_source(spec, E, QP, QR, tail, p0, boot, s, U, deep)
    except DeriveError as e:
        res['why'] = 'emit: %s' % e
        return res
    with open(path, 'w') as f:
        f.write(src)
    res['file'] = path
    rc, out = coqc(path)
    if rc != 0:
        res['why'] = 'coqc failed'
        res['log'] = out[-2500:]
        os.remove(path)
        return res
    rc, out = print_assumptions(ID, scratch, pref)
    names = set()
    inax = False
    for ln in out.splitlines():
        if ln.startswith('Axioms:'):
            inax = True
            continue
        if not inax or not ln.strip() or ln[:1].isspace():
            continue
        nm = ln.strip().split(':')[0].strip()
        if re.match(r"^[A-Za-z_][A-Za-z_0-9.']*$", nm):
            names.add(nm.split('.')[-1])
    res['axioms'] = sorted(names)
    res['ok'] = (res['axioms'] == ['functional_extensionality_dep'])
    if not res['ok']:
        res['why'] = 'unexpected axioms: %s' % res['axioms']
        os.remove(path)
    return res


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('specs', nargs='*')
    ap.add_argument('--list')
    ap.add_argument('--emit', action='store_true')
    ap.add_argument('--windows', action='store_true')
    ap.add_argument('--force', action='store_true')
    ap.add_argument('--json')
    ap.add_argument('--scratch', default='/tmp')
    a = ap.parse_args()
    specs = list(a.specs)
    if a.list:
        specs += [x.strip() for x in open(a.list) if x.strip()]
    out = []
    for spec in specs:
        r = process(spec, a.emit, a.scratch, a.force, a.windows)
        out.append(r)
        extra = ''
        if 'skel' in r:
            extra = ' skel=%s exact_ov=%s boot=%d p0=%d tail=%s' % (
                r['skel'], r['exact_ov'], r['boot'], r['p0'], r['tail'])
        print('%s %s %s%s' % ('PASS' if r['ok'] else 'FAIL', spec,
                              r.get('why', ''), extra))
        if r.get('U') and a.windows:
            for k, v in r['U'].items():
                print('   %-5s %s' % (k, v))
        sys.stdout.flush()
    if a.json:
        with open(a.json, 'w') as f:
            json.dump(out, f, indent=1, default=str)
    print('== %d/%d passed' % (sum(1 for r in out if r['ok']), len(out)))


if __name__ == '__main__':
    main()
