#!/usr/bin/env python3
"""UNTRUSTED emitter for the EXPONENTIAL-OVERFLOW (inner-counter) family.

Clones the hand-authored, kernel-verified reference board
theories/Machines/Counters/IXP_1RB1LA_0LA1RC_0LD0RB_0LA1RD.v across the
family (WAVE11_MIRROR.md section 3): flip-anchored [Ip] counters whose
interior laps are the affine ILS4F chain but whose overflow lap
2^K-1 -> 2^K costs ~c*2^K steps because the machine runs an INNER
interleaved counter from 2^(K-1) up to the all-ones fill.

Per machine the emitter derives SIX chains and validates each against the
raw simulator (the replay layer is a fork of tools/counters/validate_ixp.py,
the differential validator that pinned the reference's chains):

  interior : P1 RIP^(2j+1) STPI TRN RET^j FIN            [exact]
  inner    : P1i RIP^(2j+1) STPI TRN RET^j FINi          [exact; reuses the
             outer RIP/STPI/TRN/RET units verbatim]
  boot     : P1 RIP^(2j'+2) STPO RET^(j'+1) FINx         [-> Cin(2^j')]
  exit     : P1i RIP^(2K) STPOe RET^K FINe               [-> Cc(2^K), up to
             one left blank + far-blank (lift close)]

  outer anchor : Cc p  = (E,   Ip p ++ [1,0], 0, [0])
  inner anchor : Cin v = (Ein, Ip v ++ [1],   0, Ff)

with per-machine state roles (E, QR, Ein), inner far word Ff, and step
counts.  The composed overflow (boot ; inner laps to fill ; exit) is checked
STEP-EXACTLY against the raw simulator for K = 1..7 before emission, plus
interior p = 2..199, inner v = 2..299, boot j' = 0..7, exit K = 1..8.

Everything here is UNTRUSTED: the Coq kernel re-checks every emitted board.

Usage
  emit_ixp.py --list FILE [--emit] [--mirror] [--json OUT]
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

from executor import Exec, Wall                                    # noqa: E402
from emit_interleave import (Raw, strip0, LAB, ST, SYM, ENC, parse,  # noqa: E402
                             DeriveError, derive_tail, mach_id, coq_table,
                             clist, ccons, cwin)
from emit_shape4 import conc, cycl, cycr, carry, m_int, nrm          # noqa: E402
from mirror_common import mirror_spec, mirrorize                     # noqa: E402

Ip = ENC['Ip']
OUTDIR = os.path.join(REPO, 'theories', 'Machines', 'Counters')

TAIL = [1, 0]          # the outer flip anchor tail
FAR = [0]              # the outer far cell
TIN = [1]              # the inner anchor's word tail


def j_of(v):
    j = 0
    while (v >> j) & 1:
        j += 1
    return j


def cc(E, p):
    return (E, Ip(p) + TAIL, 0, list(FAR))


def cin(Ein, v, Ff):
    return (Ein, Ip(v) + TIN, 0, list(Ff))


# ------------------------------------------------------------ raw measures ---
def raw_to(raw, cfg, tgt, maxs=400000):
    """Steps from cfg to the target config, matched up to blank padding
    (the raw tape may carry invisible trailing blanks); None if missed."""
    tn = nrm(tgt)
    for t in range(1, maxs):
        cfg = raw.step(cfg)
        if cfg is None:
            return None
        if nrm(cfg) == tn:
            return t
    return None


def raw_exit_landing(raw, E, Ein, Ff, K, maxs=400000):
    """Steps from Cin(2^K-1) to the exit landing (E, Ip(2^K)+[1], 0, blanks);
    returns (steps, far_word)."""
    cfg = cin(Ein, (1 << K) - 1, Ff)
    want_l = Ip(1 << K) + [1]
    for t in range(1, maxs):
        cfg = raw.step(cfg)
        if cfg is None:
            return None, None
        if (cfg[0] == E and cfg[2] == 0 and strip0(cfg[1]) == want_l
                and not strip0(cfg[3])):
            return t, list(cfg[3])
    return None, None


# ---------------------------------------------------------- chain replays ----
def replay_int(ex, E, m, j, s):
    cfg = cc(E, m)[0:1] + (Ip(m) + TAIL, 0, list(FAR))
    cfg = (E, Ip(m) + TAIL, 0, list(FAR))
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
    n = (s['nP1'] + s['nRIP'] * (2 * j + 1) + s['nSTP'] + s['nTRN']
         + s['nRET'] * j + s['nFIN'])
    return cfg, n, U


def replay_inner(ex, E, Ein, Ff, v, j, s):
    cfg = (Ein, Ip(v) + TIN, 0, list(Ff))
    U = {}
    cfg, U['P1i'] = conc(ex, cfg, True, True, s['nP1i'], 0, len(Ff))
    cfg, u = cycl(ex, cfg, 1, s['nRIP'], 2 * j + 1)
    cfg, U['STPI2'] = conc(ex, cfg, True, True, s['nSTP'], 1, 0)
    cfg, U['TRN2'] = conc(ex, cfg, True, True, s['nTRN'], 0, 1)
    cfg, u = cycr(ex, cfg, 2, s['nRET'], j)
    cfg, U['FINi'] = conc(ex, cfg, True, True, s['nFINi'], 0, None)
    n = (s['nP1i'] + s['nRIP'] * (2 * j + 1) + s['nSTP'] + s['nTRN']
         + s['nRET'] * j + s['nFINi'])
    return cfg, n, U


def replay_boot(ex, E, jp, s):
    p = (1 << (jp + 1)) - 1
    cfg = (E, Ip(p) + TAIL, 0, list(FAR))
    U = {}
    cfg, _ = conc(ex, cfg, True, True, s['nP1'], 0, 1)
    cfg, _ = cycl(ex, cfg, 1, s['nRIP'], 2 * jp + 2)
    cfg, U['STPO'] = conc(ex, cfg, False, True, s['nSTPO'], None, 0)
    cfg, _ = cycr(ex, cfg, 2, s['nRET'], jp + 1)
    cfg, U['FINx'] = conc(ex, cfg, True, False, s['nFINX'], 1, None)
    n = (s['nP1'] + s['nRIP'] * (2 * jp + 2) + s['nSTPO']
         + s['nRET'] * (jp + 1) + s['nFINX'])
    return cfg, n, U


def replay_exit(ex, E, Ein, Ff, K, s):
    u0 = (1 << K) - 1
    cfg = (Ein, Ip(u0) + TIN, 0, list(Ff))
    U = {}
    cfg, _ = conc(ex, cfg, True, True, s['nP1i'], 0, len(Ff))
    cfg, _ = cycl(ex, cfg, 1, s['nRIP'], 2 * K)
    cfg, U['STPOe'] = conc(ex, cfg, False, True, s['nSTPOE'], None, 0)
    cfg, _ = cycr(ex, cfg, 2, s['nRET'], K)
    cfg, U['FINe'] = conc(ex, cfg, True, True, s['nFINE'], 0, len(Ff))
    n = (s['nP1i'] + s['nRIP'] * 2 * K + s['nSTPOE'] + s['nRET'] * K
         + s['nFINE'])
    return cfg, n, U


# ----------------------------------------------- V2 (pop-P1) chain replays ---
def replay_int_v2(ex, E, m, j, s):
    cfg = (E, Ip(m) + TAIL, 0, list(FAR))
    U = {}
    cfg, U['P1'] = conc(ex, cfg, True, True, s['nP1'], 1, 1)
    cfg, u = cycl(ex, cfg, 1, s['nRIP'], 2 * j)
    if u:
        U['RIP'] = u
    cfg, U['STPI'] = conc(ex, cfg, True, True, s['nSTP'], 1, 0)
    cfg, U['TRN'] = conc(ex, cfg, True, True, s['nTRN'], 0, 1)
    cfg, u = cycr(ex, cfg, 2, s['nRET'], j)
    if u:
        U['RET'] = u
    cfg, U['FIN'] = conc(ex, cfg, True, True, s['nFIN'], 0, None)
    n = (s['nP1'] + s['nRIP'] * 2 * j + s['nSTP'] + s['nTRN']
         + s['nRET'] * j + s['nFIN'])
    return cfg, n, U


def replay_inner_v2(ex, E, Ein, Ff, v, j, s):
    cfg = (Ein, Ip(v) + TIN, 0, list(Ff))
    U = {}
    cfg, U['P1i'] = conc(ex, cfg, True, True, s['nP1i'], 1, len(Ff))
    cfg, u = cycl(ex, cfg, 1, s['nRIP'], 2 * j)
    cfg, U['STPI2'] = conc(ex, cfg, True, True, s['nSTP'], 1, 0)
    cfg, U['TRN2'] = conc(ex, cfg, True, True, s['nTRN'], 0, 1)
    cfg, u = cycr(ex, cfg, 2, s['nRET'], j)
    cfg, U['FINi'] = conc(ex, cfg, True, True, s['nFINi'], 0, None)
    n = (s['nP1i'] + s['nRIP'] * 2 * j + s['nSTP'] + s['nTRN']
         + s['nRET'] * j + s['nFINi'])
    return cfg, n, U


def replay_boot_v2(ex, E, jp, s):
    p = (1 << (jp + 1)) - 1
    cfg = (E, Ip(p) + TAIL, 0, list(FAR))
    U = {}
    cfg, _ = conc(ex, cfg, True, True, s['nP1'], 1, 1)
    cfg, _ = cycl(ex, cfg, 1, s['nRIP'], 2 * jp + 1)
    cfg, U['STPO'] = conc(ex, cfg, False, True, s['nSTPO'], None, 0)
    cfg, _ = cycr(ex, cfg, 2, s['nRET'], jp)
    cfg, U['FINx'] = conc(ex, cfg, True, True, s['nFINX'], 0, None)
    n = (s['nP1'] + s['nRIP'] * (2 * jp + 1) + s['nSTPO']
         + s['nRET'] * jp + s['nFINX'])
    return cfg, n, U


def replay_exit_v2(ex, E, Ein, Ff, K, s):
    u0 = (1 << K) - 1
    cfg = (Ein, Ip(u0) + TIN, 0, list(Ff))
    U = {}
    cfg, U['P1ie'] = conc(ex, cfg, True, True, s['nP1i'], 1, len(Ff))
    cfg, _ = cycl(ex, cfg, 1, s['nRIP'], 2 * K - 1)
    cfg, U['STPOe'] = conc(ex, cfg, False, True, s['nSTPOE'], None, 0)
    cfg, _ = cycr(ex, cfg, 2, s['nRET'], K)
    cfg, U['FINe'] = conc(ex, cfg, True, True, s['nFINE'], 0, len(Ff))
    n = (s['nP1i'] + s['nRIP'] * (2 * K - 1) + s['nSTPOE'] + s['nRET'] * K
         + s['nFINE'])
    return cfg, n, U


REPLAYS = {
    'v1': dict(int=replay_int, inner=replay_inner, boot=replay_boot,
               exit=replay_exit),
    'v2': dict(int=replay_int_v2, inner=replay_inner_v2, boot=replay_boot_v2,
               exit=replay_exit_v2),
}


# ------------------------------------------------------------- derivation ----
def affine2(pts):
    js = sorted(pts)
    if len(js) < 2:
        return None
    b = (pts[js[1]] - pts[js[0]]) // (js[1] - js[0]) \
        if (pts[js[1]] - pts[js[0]]) % (js[1] - js[0]) == 0 else None
    if b is None:
        return None
    a = pts[js[0]] - b * js[0]
    return (a, b) if all(pts[j] == a + b * j for j in js) else None


def derive_interior(spec, E):
    """The affine flip interior chain; returns (s, U)."""
    raw = Raw(spec)
    ints = {}
    for j in range(0, 4):
        m = m_int(j)
        n = raw_to(raw, cc(E, m), cc(E, m + 1))
        if n is None:
            raise DeriveError('interior lap does not close exactly (j=%d)' % j)
        ints[j] = n
    ab = affine2(ints)
    if ab is None:
        raise DeriveError('interior laps not affine: %s' % ints)
    a, b = ab
    ex = Exec(spec)
    JI = 3
    tgt = cc(E, m_int(JI) + 1)
    for nP1 in range(1, 9):
        for nRIP in range(1, 4):
            nRET = b - 2 * nRIP
            if nRET < 1:
                continue
            for nSTP in range(1, 15):
                for nTRN in range(1, 6):
                    nFIN = a - nP1 - nRIP - nSTP - nTRN
                    if nFIN < 1:
                        continue
                    s = dict(nP1=nP1, nRIP=nRIP, nRET=nRET, nSTP=nSTP,
                             nTRN=nTRN, nFIN=nFIN)
                    try:
                        cfg, n, U = replay_int(ex, E, m_int(JI), JI, s)
                    except (Wall, KeyError, IndexError):
                        continue
                    if n != ints[JI] or cfg != tgt:
                        continue
                    return 'v1', s, U
    # V2: P1 pops the head-adjacent S1 (intercept has no nRIP term)
    for nP1 in range(1, 13):
        for nRIP in range(1, 4):
            nRET = b - 2 * nRIP
            if nRET < 1:
                continue
            for nSTP in range(1, 15):
                for nTRN in range(1, 6):
                    nFIN = a - nP1 - nSTP - nTRN
                    if nFIN < 1:
                        continue
                    s = dict(nP1=nP1, nRIP=nRIP, nRET=nRET, nSTP=nSTP,
                             nTRN=nTRN, nFIN=nFIN)
                    try:
                        cfg, n, U = replay_int_v2(ex, E, m_int(JI), JI, s)
                    except (Wall, KeyError, IndexError):
                        continue
                    if n != ints[JI] or cfg != tgt:
                        continue
                    return 'v2', s, U
    raise DeriveError('no interior skeleton fits (a=%d b=%d)' % (a, b))


def check_interior_shapes(E, U):
    msgs = []
    (Pe, Px) = U['P1']
    (Re, Rx) = U['RIP']
    (Se, Sx) = U['STPI']
    (Ne, Nx) = U['TRN']
    (Te, Tx) = U['RET']
    (Fe, Fx) = U['FIN']
    Erip = Px[0]
    QR = Nx[0]
    if Pe != (E, (), 0, (0,)) or Px != (Erip, (), 1, (0,)):
        msgs.append('P1 %s -> %s not a frontier flip' % (Pe, Px))
    if Re != (Erip, (1,), 1, ()) or Rx != (Erip, (), 1, (1,)):
        msgs.append('ripple %s -> %s' % (Re, Rx))
    if Se != (Erip, (0,), 1, ()) or Sx != (Erip, (), 0, (1,)):
        msgs.append('interior stop %s -> %s' % (Se, Sx))
    if Ne != (Erip, (), 0, (1,)) or Nx != (QR, (1,), 1, ()):
        msgs.append('turn %s -> %s' % (Ne, Nx))
    if Te != (QR, (), 1, (1, 1)) or Tx != (QR, (0, 1), 1, ()):
        msgs.append('return %s -> %s not [1;1]->[0;1]' % (Te, Tx))
    if Fe != (QR, (), 1, (1, 0)) or Fx != (E, (1,), 0, (0,)):
        msgs.append('close %s -> %s' % (Fe, Fx))
    if QR == Erip:
        msgs.append('QR collides with Erip')
    return msgs, Erip, QR


def check_interior_shapes_v2(E, U):
    msgs = []
    (Pe, Px) = U['P1']
    (Re, Rx) = U['RIP']
    (Se, Sx) = U['STPI']
    (Ne, Nx) = U['TRN']
    (Te, Tx) = U['RET']
    (Fe, Fx) = U['FIN']
    Erip = Px[0]
    QR = Nx[0]
    PD = Px[3]
    if Pe != (E, (1,), 0, (0,)) or Px[:3] != (Erip, (), 1) or len(PD) != 2:
        msgs.append('P1 %s -> %s not a pop-prologue' % (Pe, Px))
    if Re != (Erip, (1,), 1, ()) or Rx != (Erip, (), 1, (1,)):
        msgs.append('ripple %s -> %s' % (Re, Rx))
    if Se != (Erip, (0,), 1, ()) or Sx != (Erip, (), 0, (1,)):
        msgs.append('interior stop %s -> %s' % (Se, Sx))
    if Ne != (Erip, (), 0, (1,)) or Nx != (QR, (1,), 1, ()):
        msgs.append('turn %s -> %s' % (Ne, Nx))
    if Te != (QR, (), 1, (1, 1)) or Tx != (QR, (0, 1), 1, ()):
        msgs.append('return %s -> %s not [1;1]->[0;1]' % (Te, Tx))
    if Fe != (QR, (), 1, tuple(PD)) or Fx != (E, (1,), 0, (0,)):
        msgs.append('close %s -> %s (need entry over the P1 deposit %s)'
                    % (Fe, Fx, PD))
    if QR == Erip:
        msgs.append('QR collides with Erip')
    return msgs, Erip, QR


def find_inner_anchor(spec, E, K=5):
    """Detect the inner anchor family inside the K=5 overflow lap: blank-head
    snapshots reading Ip v ++ [1] with a fixed far word, v marching
    2^(K-1)..2^K-1.  Returns candidate list [(Ein, Ff, times)]."""
    raw = Raw(spec)
    dec = {}
    for m in range(1, 1 << (K + 2)):
        dec[tuple(Ip(m) + TIN)] = m
    lo, hi = 1 << (K - 1), (1 << K) - 1
    cfg = cc(E, hi)
    tgt = None  # run bounded by lap closure
    snaps = []
    for t in range(1, 400000):
        cfg = raw.step(cfg)
        if cfg is None:
            break
        if cfg[2] == 0:
            snaps.append((t, cfg[0], tuple(cfg[1]), tuple(strip0(cfg[3]))))
        if (cfg[0] == E and cfg[2] == 0 and cfg[1] == Ip(hi + 1) + [1]
                and not strip0(cfg[3])):
            break
    groups = {}
    for t, q, l, far in snaps:
        v = dec.get(l)
        if v is not None and lo <= v <= hi:
            groups.setdefault((q, far), {}).setdefault(v, []).append(t)
    out = []
    for (q, far), vm in groups.items():
        if set(vm) != set(range(lo, hi + 1)):
            continue
        # greedy increasing-time selection
        prev, ok, times = -1, True, []
        for v in range(lo, hi + 1):
            cand = [t for t in vm[v] if t > prev]
            if not cand:
                ok = False
                break
            prev = min(cand)
            times.append(prev)
        if ok:
            out.append((q, list(far), times))
    out.sort(key=lambda c: (len(c[1]), c[2][0]))
    return out


def derive_inner(spec, variant, E, Ein, Ff, s):
    """nP1i / nFINi for the inner lap (reusing RIP/STPI/TRN/RET)."""
    raw = Raw(spec)
    ex = Exec(spec)
    rp = REPLAYS[variant]['inner']
    JI = 3
    v = m_int(JI)
    n_raw = raw_to(raw, cin(Ein, v, Ff), cin(Ein, v + 1, Ff))
    if n_raw is None:
        raise DeriveError('inner lap does not close (v=%d)' % v)
    ripn = 2 * JI + 1 if variant == 'v1' else 2 * JI
    rem = n_raw - (s['nRIP'] * ripn + s['nSTP'] + s['nTRN'] + s['nRET'] * JI)
    tgt = cin(Ein, v + 1, Ff)
    for nP1i in range(1, rem):
        s2 = dict(s, nP1i=nP1i, nFINi=rem - nP1i)
        try:
            cfg, n, U = rp(ex, E, Ein, Ff, v, JI, s2)
        except (Wall, KeyError, IndexError):
            continue
        if cfg == tgt and n == n_raw:
            return s2, U
    raise DeriveError('no inner P1i/FINi split fits (rem=%d)' % rem)


def check_inner_shapes(variant, Erip, QR, Ein, Ff, U):
    msgs = []
    (Pe, Px) = U['P1i']
    (Fe, Fx) = U['FINi']
    if variant == 'v1':
        if Pe != (Ein, (), 0, tuple(Ff)) or Px != (Erip, (), 1, tuple(Ff)):
            msgs.append('P1i %s -> %s (need (Ein,[],0,Ff)->(Erip,[],1,Ff))'
                        % (Pe, Px))
        if Fe != (QR, (), 1, tuple([1] + list(Ff))):
            msgs.append('FINi entry %s (need (QR,[],1,[1]++Ff))' % (Fe,))
    else:
        PI = Px[3]
        if Pe != (Ein, (1,), 0, tuple(Ff)) or Px[:3] != (Erip, (), 1) \
                or len(PI) != 1 + len(Ff) or PI[:1] != (1,):
            msgs.append('P1i %s -> %s (need (Ein,[1],0,Ff)->(Erip,[],1,'
                        'S1::w))' % (Pe, Px))
        elif Fe != (QR, (), 1, tuple(PI)):
            msgs.append('FINi entry %s (need the P1i deposit %s)'
                        % (Fe, PI))
    if Fx != (Ein, (1,), 0, tuple(Ff)):
        msgs.append('FINi exit %s (need (Ein,[1],0,Ff))' % (Fx,))
    return msgs


def derive_boot(spec, variant, E, Ein, sfar, s):
    """STPO/FINx split; the exact landing far word becomes Ff."""
    raw = Raw(spec)
    ex = Exec(spec)
    rp = REPLAYS[variant]['boot']
    jp = 3
    n_raw = raw_to(raw, cc(E, (1 << (jp + 1)) - 1),
                   cin(Ein, 1 << jp, list(sfar) + [0]))
    if n_raw is None:
        raise DeriveError('boot does not reach Cin(2^jp)')
    if variant == 'v1':
        fixed = s['nP1'] + s['nRIP'] * (2 * jp + 2) + s['nRET'] * (jp + 1)
    else:
        fixed = s['nP1'] + s['nRIP'] * (2 * jp + 1) + s['nRET'] * jp
    rem = n_raw - fixed
    want_l = Ip(1 << jp) + TIN
    for nSTPO in range(1, rem):
        s2 = dict(s, nSTPO=nSTPO, nFINX=rem - nSTPO)
        try:
            cfg, n, U = rp(ex, E, jp, s2)
        except (Wall, KeyError, IndexError):
            continue
        if (n == n_raw and cfg[0] == Ein and cfg[1] == want_l
                and cfg[2] == 0 and strip0(cfg[3]) == list(sfar)):
            return s2, U, list(cfg[3])
    raise DeriveError('no boot STPO/FINx split fits (rem=%d)' % rem)


def check_boot_shapes(variant, Erip, Ein, QR, Ff, PD, U):
    msgs = []
    (Oe, Ox) = U['STPO']
    (Xe, Xx) = U['FINx']
    if Oe != (Erip, (0,), 1, ()) or Ox != (QR, (1,), 1, ()):
        msgs.append('STPO %s -> %s (need (Erip,[0],1,[])->(QR,[1],1,[]))'
                    % (Oe, Ox))
    if variant == 'v1':
        if Xe != (QR, (0,), 1, (0,)) or Xx != (Ein, (), 0, tuple(Ff)):
            msgs.append('FINx %s -> %s (need (QR,[0],1,[0])->(Ein,[],0,Ff))'
                        % (Xe, Xx))
    else:
        if Xe != (QR, (), 1, tuple([1] + list(PD))) \
                or Xx != (Ein, (1,), 0, tuple(Ff)):
            msgs.append('FINx %s -> %s (need (QR,[],1,[1]++PD)->'
                        '(Ein,[1],0,Ff))' % (Xe, Xx))
    return msgs


def derive_exit(spec, variant, E, Ein, Ff, s):
    raw = Raw(spec)
    ex = Exec(spec)
    rp = REPLAYS[variant]['exit']
    K = 4
    n_raw, fx = raw_exit_landing(raw, E, Ein, Ff, K)
    if n_raw is None:
        raise DeriveError('exit does not land on Cc(2^K) shape')
    ripn = 2 * K if variant == 'v1' else 2 * K - 1
    rem = n_raw - (s['nP1i'] + s['nRIP'] * ripn + s['nRET'] * K)
    for nSTPOE in range(1, rem):
        s2 = dict(s, nSTPOE=nSTPOE, nFINE=rem - nSTPOE)
        try:
            cfg, n, U = rp(ex, E, Ein, Ff, K, s2)
        except (Wall, KeyError, IndexError):
            continue
        if n != n_raw:
            continue
        if (cfg[0] == E and cfg[1] == Ip(1 << K) + [1] and cfg[2] == 0
                and not strip0(cfg[3])):
            return s2, U, list(cfg[3])
    raise DeriveError('no exit STPOe/FINe split fits (rem=%d)' % rem)


def check_exit_shapes(variant, E, Erip, Ein, QR, Ff, PI, Fx, U):
    msgs = []
    (Oe, Ox) = U['STPOe']
    (Ge, Gx) = U['FINe']
    if Oe != (Erip, (), 1, ()) or Ox != (QR, (1,), 1, ()):
        msgs.append('STPOe %s -> %s (need (Erip,[],1,[])->(QR,[1],1,[]))'
                    % (Oe, Ox))
    want = tuple(Ff) if variant == 'v1' else tuple(PI[1:])
    if Ge != (QR, (), 1, want) or Gx != (E, (1,), 0, tuple(Fx)):
        msgs.append('FINe %s -> %s (need (QR,[],1,%s)->(E,[1],0,Fx))'
                    % (Ge, Gx, want))
    if list(Fx) not in ([], [0], [0, 0]):
        msgs.append('exit far %s not an understood blank pad' % (Fx,))
    return msgs


# -------------------------------------------------------------- validation ---
def validate_all(spec, variant, E, Ein, Ff, s):
    raw = Raw(spec)
    ex = Exec(spec)
    rint = REPLAYS[variant]['int']
    rinn = REPLAYS[variant]['inner']
    rboot = REPLAYS[variant]['boot']
    rexit = REPLAYS[variant]['exit']
    for p in range(2, 200):
        j = j_of(p)
        if p == (1 << j) - 1:
            continue
        cfg, n, _ = rint(ex, E, p, j, s)
        if cfg != cc(E, p + 1):
            raise DeriveError('interior p=%d: symbolic misses anchor' % p)
        if raw_to(raw, cc(E, p), cc(E, p + 1)) != n:
            raise DeriveError('interior p=%d: step count mismatch' % p)
    for v in range(2, 300):
        j = j_of(v)
        if v == (1 << j) - 1:
            continue
        cfg, n, _ = rinn(ex, E, Ein, Ff, v, j, s)
        if cfg != cin(Ein, v + 1, Ff):
            raise DeriveError('inner v=%d: symbolic misses anchor' % v)
    for jp in range(0, 8):
        cfg, n, _ = rboot(ex, E, jp, s)
        if cfg != cin(Ein, 1 << jp, Ff):
            raise DeriveError('boot jp=%d: misses Cin(2^jp)' % jp)
    fx0 = None
    for K in range(1, 9):
        cfg, n, _ = rexit(ex, E, Ein, Ff, K, s)
        if not (cfg[0] == E and cfg[1] == Ip(1 << K) + [1] and cfg[2] == 0
                and not strip0(cfg[3])):
            raise DeriveError('exit K=%d: misses landing' % K)
        if fx0 is None:
            fx0 = list(cfg[3])
        elif list(cfg[3]) != fx0:
            raise DeriveError('exit far varies with K')
    for K in range(1, 8):
        n = rboot(ex, E, K - 1, s)[1]
        for v in range(1 << (K - 1), (1 << K) - 1):
            n += rinn(ex, E, Ein, Ff, v, j_of(v), s)[1]
        n += rexit(ex, E, Ein, Ff, K, s)[1]
        r = raw_ov(raw, E, K)
        if r != n:
            raise DeriveError('composed overflow K=%d: sym %s != raw %s'
                              % (K, n, r))
    return fx0


def raw_ov(raw, E, K, maxs=800000):
    """Raw steps of the outer overflow lap Cc(2^K-1) -> exit landing."""
    cfg = cc(E, (1 << K) - 1)
    want_l = Ip(1 << K) + [1]
    for t in range(1, maxs):
        cfg = raw.step(cfg)
        if cfg is None:
            return None
        if (cfg[0] == E and cfg[2] == 0 and strip0(cfg[1]) == want_l
                and not strip0(cfg[3])):
            return t
    return None


# ------------------------------------------------------------------- boot ----
def boot_probe(spec, E, p0, maxT=100000):
    """First hit of an anchor Cc(p), p in [p0, p0+8], up to blank padding
    (the Coq side compares with [ceqb]).  Returns (p_start, t0)."""
    raw = Raw(spec)
    tgts = {p: nrm(cc(E, p)) for p in range(max(p0, 1), max(p0, 1) + 9)}
    cfg = (0, [], 0, [])
    for t in range(maxT):
        c = nrm(cfg)
        for p, tgt in tgts.items():
            if c == tgt:
                return p, t
        cfg = raw.step(cfg)
        if cfg is None:
            raise DeriveError('halts during bootstrap at t=%d' % t)
    raise DeriveError('no bootstrap to Cc(%d..%d)' % (p0, p0 + 8))


# ------------------------------------------------------------------ visits ---
def visit_plan(spec, variant, E, Erip, QR, Ein, Ff, PD, s):
    """Per-state witness routes.  Returns {q: route-tuple}."""
    ex = Exec(spec)
    tab = parse(spec)
    plan = {E: ('anchor',)}
    p1win = ([], [0]) if variant == 'v1' else ([1], [0])
    p1iwin = ([], list(Ff)) if variant == 'v1' else ([1], list(Ff))
    for q in range(4):
        if q in plan:
            continue
        found = None
        for t in range(1, s['nP1']):
            try:
                o = ex.wsteps(True, True, E, list(p1win[0]), 0,
                              list(p1win[1]), t)
            except Wall:
                break
            if o[0] == q:
                found = ('prefa', t, (o[0], tuple(o[1]), o[2], tuple(o[3])))
                break
        if found is None and q == QR:
            found = ('qr',)
        if found is None:
            e = tab.get((QR, 1))
            if e is not None and e[1] > 0 and e[2] == q:
                found = ('vc', e[0])
        if found is None:
            for t in range(1, s['nSTPO']):
                try:
                    o = ex.wsteps(False, True, Erip, [0], 1, [], t)
                except Wall:
                    break
                if o[0] == q:
                    found = ('stpo', t,
                             (o[0], tuple(o[1]), o[2], tuple(o[3])))
                    break
        if found is None:
            for t in range(1, s['nFINX'] + 1):
                try:
                    if variant == 'v1':
                        o = ex.wsteps(True, False, QR, [0], 1, [0], t)
                    else:
                        o = ex.wsteps(True, True, QR, [], 1,
                                      [1] + list(PD), t)
                except Wall:
                    break
                if o[0] == q:
                    found = ('finx', t,
                             (o[0], tuple(o[1]), o[2], tuple(o[3])))
                    break
        if found is None:
            for t in range(1, s['nP1i']):
                try:
                    o = ex.wsteps(True, True, Ein, list(p1iwin[0]), 0,
                                  list(p1iwin[1]), t)
                except Wall:
                    break
                if o[0] == q:
                    found = ('p1i', t,
                             (o[0], tuple(o[1]), o[2], tuple(o[3])))
                    break
        if found is None:
            raise DeriveError('no visit witness for state %s' % LAB[q])
        plan[q] = found
    return plan


# ------------------------------------------------------------ Coq emission ---
HEAD = r'''(** * IXP_@ID@: exponential-overflow interleaved
    counter, machine @SPEC@.

    Auto-emitted by tools/counters/emit_ixp.py (UNTRUSTED emitter; the Coq
    kernel re-checks every line below), cloning the hand-authored reference
    board IXP_1RB1LA_0LA1RC_0LD0RB_0LA1RD.v (WAVE11_MIRROR.md section 3).
    Interior laps are the affine flip chain (ILS4F); the OVERFLOW lap
    2^K-1 -> 2^K runs an INNER interleaved counter: anchors

      Cc p  = (@EDGE@, (Ip p ++ [S1;S0], S0, [S0]))
      Cin v = (@EIN@, (Ip v ++ [S1], S0, @FF@))

    march v = 2^(K-1) .. 2^K-1 with affine interior-only inner laps (the
    same RIP/STPI/TRN/RET units as the outer chain; only the frontier
    windows P1i/FINi differ):

      boot (affine)  :  Cc (2^K-1)  ->  Cin (2^(K-1))
      inner counting :  Cin v -> Cin (v+1), composed to the all-ones fill
                        by well-founded induction on [tovf]
      exit (affine)  :  Cin (2^K-1) ->  Cc (2^K), up to a lift close

    -- a SECOND instantiation of the lap machinery nested inside the outer
    overflow branch; [glue_neverqh] never sees the difference.  The three
    positive gadgets connecting the levels ([pow2], [fill],
    [cview_none_shape]) live in BBB4.Counters.IXPGadgets.

    Every chain was differentially validated against the raw simulator
    (interior p = 2..199, inner v = 2..299, boot j' = 0..7, exit K = 1..8,
    and the composed outer overflow step-exactly for K = 1..7).
    Axiom footprint: [functional_extensionality_dep] (via CTape.lift). *)
From Coq Require Import Arith Lia Bool List PArith Wellfounded.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape LapGlue MonoCounter ILCounter JpCounter IXPGadgets.
Import ListNotations.

Definition mk_@ID@ (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_@ID@.

(** @SPEC@ *)
Definition tm_@ID@ : TM := fun q s => match q, s with
@TABLE@ end.
Local Notation tm := tm_@ID@.

(** The outer and inner anchor families. *)
Definition Cc_@ID@ (p : positive) : cconf := (@EDGE@, (Ip p ++ [S1;S0], S0, [S0])).
Local Notation Cc := Cc_@ID@.
Definition Cin_@ID@ (v : positive) : cconf := (@EIN@, (Ip v ++ [S1], S0, @FF@)).
Local Notation Cin := Cin_@ID@.

(** ** The window units (each closed by [reflexivity]) *)
Lemma U_P1_@ID@ : wsteps true true tm @NP1@ (@EDGE@,([],S0,[S0])) = Some (@ERIP@,([],S1,[S0])). Proof. reflexivity. Qed.
Lemma U_P1i_@ID@ : wsteps true true tm @NP1I@ (@EIN@,([],S0,@FF@)) = Some (@ERIP@,([],S1,@FF@)). Proof. reflexivity. Qed.
Lemma U_RIP_@ID@ : wsteps true true tm @NRIP@ (@ERIP@,([S1],S1,[])) = Some (@ERIP@,([],S1,[S1])). Proof. reflexivity. Qed.
Lemma U_STPI_@ID@ : wsteps true true tm @NSTP@ (@ERIP@,([S0],S1,[])) = Some (@ERIP@,([],S0,[S1])). Proof. reflexivity. Qed.
Lemma U_TRN_@ID@ : wsteps true true tm @NTRN@ (@ERIP@,([],S0,[S1])) = Some (@QR@,([S1],S1,[])). Proof. reflexivity. Qed.
Lemma U_RET_@ID@ : wsteps true true tm @NRET@ (@QR@,([],S1,[S1;S1])) = Some (@QR@,([S0;S1],S1,[])). Proof. reflexivity. Qed.
Lemma U_FIN_@ID@ : wsteps true true tm @NFIN@ (@QR@,([],S1,[S1;S0])) = Some (@EDGE@,([S1],S0,[S0])). Proof. reflexivity. Qed.
Lemma U_FINi_@ID@ : wsteps true true tm @NFINI@ (@QR@,([],S1,@FI@)) = Some (@EIN@,([S1],S0,@FF@)). Proof. reflexivity. Qed.
Lemma U_STPO_@ID@ : wsteps false true tm @NSTPO@ (@ERIP@,([S0],S1,[])) = Some (@QR@,([S1],S1,[])). Proof. reflexivity. Qed.
Lemma U_STPOe_@ID@ : wsteps false true tm @NSTPOE@ (@ERIP@,([],S1,[])) = Some (@QR@,([S1],S1,[])). Proof. reflexivity. Qed.
Lemma U_FINx_@ID@ : wsteps true false tm @NFINX@ (@QR@,([S0],S1,[S0])) = Some (@EIN@,([],S0,@FF@)). Proof. reflexivity. Qed.
Lemma U_FINe_@ID@ : wsteps true true tm @NFINE@ (@QR@,([],S1,@FF@)) = Some (@EDGE@,([S1],S0,@FX@)). Proof. reflexivity. Qed.
@UVIS@
(** ** Transported phases *)
Lemma phP1_@ID@ : forall L R, csteps tm @NP1@ (@EDGE@,(L,S0,S0::R)) = Some (@ERIP@,(L,S1,S0::R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_P1_@ID@). Qed.
Lemma phP1i_@ID@ : forall L R, csteps tm @NP1I@ (@EIN@,(L,S0,@FFC@R)) = Some (@ERIP@,(L,S1,@FFC@R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_P1i_@ID@). Qed.
Lemma phRIP_@ID@ : forall k L R, csteps tm (@NRIP@*k) (@ERIP@,(rep [S1] k ++ L,S1,R)) = Some (@ERIP@,(L,S1,rep [S1] k ++ R)).
Proof. intros. pose proof (cycL _ _ _ _ _ _ _ U_RIP_@ID@ k L R) as H; cbn [app] in H; exact H. Qed.
Lemma phSTPI_@ID@ : forall L R, csteps tm @NSTP@ (@ERIP@,(S0::L,S1,R)) = Some (@ERIP@,(L,S0,S1::R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_STPI_@ID@). Qed.
Lemma phTRN_@ID@ : forall L R, csteps tm @NTRN@ (@ERIP@,(L,S0,S1::R)) = Some (@QR@,(S1::L,S1,R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_TRN_@ID@). Qed.
Lemma phRET_@ID@ : forall k L R, csteps tm (@NRET@*k) (@QR@,(L,S1,rep [S1;S1] k ++ R)) = Some (@QR@,(rep [S0;S1] k ++ L,S1,R)).
Proof. intros. exact (cycR _ _ _ _ _ _ U_RET_@ID@ k L R). Qed.
Lemma phFIN_@ID@ : forall L R, csteps tm @NFIN@ (@QR@,(L,S1,S1::S0::R)) = Some (@EDGE@,(S1::L,S0,S0::R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_FIN_@ID@). Qed.
Lemma phFINi_@ID@ : forall L R, csteps tm @NFINI@ (@QR@,(L,S1,@FIC@R)) = Some (@EIN@,(S1::L,S0,@FFC@R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_FINi_@ID@). Qed.
Lemma phSTPO_@ID@ : forall R, csteps tm @NSTPO@ (@ERIP@,([S0],S1,R)) = Some (@QR@,([S1],S1,R)).
Proof. intros. exact (wsteps_frame_l _ _ _ _ _ _ _ _ _ _ R U_STPO_@ID@). Qed.
Lemma phSTPOe_@ID@ : forall R, csteps tm @NSTPOE@ (@ERIP@,([],S1,R)) = Some (@QR@,([S1],S1,R)).
Proof. intros. exact (wsteps_frame_l _ _ _ _ _ _ _ _ _ _ R U_STPOe_@ID@). Qed.
Lemma phFINx_@ID@ : forall L, csteps tm @NFINX@ (@QR@,(S0::L,S1,[S0])) = Some (@EIN@,(L,S0,@FF@)).
Proof. intros. exact (wsteps_frame_r _ _ _ _ _ _ _ _ _ _ L U_FINx_@ID@). Qed.
Lemma phFINe_@ID@ : forall L R, csteps tm @NFINE@ (@QR@,(L,S1,@FFC@R)) = Some (@EDGE@,(S1::L,S0,@FXC@R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_FINe_@ID@). Qed.
@PHVIS@
(** ** The OUTER interior lap: EXACT (the ILS4F flip chain) *)
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
    change (rep [S1] (S (2*j)) ++ [S0]) with (S1 :: rep [S1] (2*j) ++ [S0]).
    rewrite rep_slide, <- rep_dbl.
    eapply csteps_chain. { apply (phRET_@ID@ j). }
    apply phFIN_@ID@.
  + rewrite HIs, <- app_assoc. cbn [app].
    change (rep [S1;S0] j ++ S1 :: S1 :: (Ip q0 ++ [S1;S0]))
      with (rep [S1;S0] j ++ [S1] ++ (S1 :: (Ip q0 ++ [S1;S0]))).
    rewrite app_assoc, pair_rot. reflexivity.
  + lia.
Qed.

(** ** The INNER lap: EXACT, interior [cview] only (all the values the
    inner run visits below the all-ones fill are interior) *)
Lemma lap_inner_@ID@ : forall v j q0, cview v = (j, Some q0) ->
  exists n c', csteps tm n (Cin v) = Some c' /\ c' = Cin (Pos.succ v) /\ 0 < n.
Proof.
  intros v j q0 Ecv. unfold Cin_@ID@.
  destruct (cview_some_I v j q0 Ecv) as (HIp & HIs).
  do 2 eexists. split; [|split].
  + rewrite HIp, <- app_assoc. cbn [app].
    rewrite rep_dbl, <- rep_slide.
    eapply csteps_chain. { apply phP1i_@ID@. }
    eapply csteps_chain. { apply (phRIP_@ID@ (S (2*j))). }
    eapply csteps_chain. { apply phSTPI_@ID@. }
    eapply csteps_chain. { apply phTRN_@ID@. }
    change (rep [S1] (S (2*j)) ++ @FF@) with (S1 :: rep [S1] (2*j) ++ @FF@).
    rewrite rep_slide, <- rep_dbl.
    eapply csteps_chain. { apply (phRET_@ID@ j). }
    apply phFINi_@ID@.
  + rewrite HIs, <- app_assoc. cbn [app].
    change (rep [S1;S0] j ++ S1 :: S1 :: (Ip q0 ++ [S1]))
      with (rep [S1;S0] j ++ [S1] ++ (S1 :: (Ip q0 ++ [S1]))).
    rewrite app_assoc, pair_rot. reflexivity.
  + lia.
Qed.

(** Compose inner laps to the all-ones fill by well-founded induction on
    [tovf] (strictly decreasing along interior laps). *)
Lemma inner_to_fill_@ID@ : forall v, exists n,
  csteps tm n (Cin v) = Some (Cin (fill v)).
Proof.
  intro v; remember (tovf v) as fuel eqn:Ef; revert v Ef.
  induction fuel as [fuel IH] using (well_founded_induction lt_wf); intros v Ef.
  destruct (cview v) as [j oq] eqn:Ecv. destruct oq as [q0|].
  - assert (Hnz : tovf v <> 0).
    { intro H0. destruct (tovf0_allones v H0) as (jj & Hjj). rewrite Hjj in Ecv; discriminate. }
    destruct (lap_inner_@ID@ v j q0 Ecv) as (n & c' & Hrun & Hc' & _). subst c'.
    destruct (IH (tovf (Pos.succ v)) (ltac:(rewrite tovf_succ by lia; lia)) (Pos.succ v) eq_refl) as (k & Hk).
    exists (n + k). rewrite csteps_add, Hrun.
    rewrite (fill_succ v j q0 Ecv) in Hk. exact Hk.
  - destruct j as [|j'].
    { exfalso. destruct v; simpl in Ecv; [destruct (cview v); discriminate|discriminate|discriminate]. }
    exists 0. rewrite (fill_allones v j' Ecv). reflexivity.
Qed.

(** ** Boot: from the outer all-ones anchor into the inner family *)
Lemma boot_ov_@ID@ : forall n, exists m c',
  csteps tm m (@EDGE@, ((rep [S1;S1] n ++ [S1]) ++ [S1;S0], S0, [S0])) = Some c'
  /\ c' = Cin (pow2 n) /\ 0 < m.
Proof.
  intro n.
  do 2 eexists. split; [|split].
  + rewrite <- app_assoc. cbn [app].
    rewrite rep_dbl, <- !rep_slide.
    eapply csteps_chain. { apply phP1_@ID@. }
    eapply csteps_chain. { apply (phRIP_@ID@ (S (S (2*n)))). }
    eapply csteps_chain. { apply phSTPO_@ID@. }
    change (rep [S1] (S (S (2*n))) ++ [S0]) with (S1 :: S1 :: rep [S1] (2*n) ++ [S0]).
    rewrite <- rep_dbl.
    change (S1 :: S1 :: rep [S1;S1] n ++ [S0]) with (rep [S1;S1] (S n) ++ [S0]).
    eapply csteps_chain. { apply (phRET_@ID@ (S n)). }
    change (rep [S0;S1] (S n) ++ [S1]) with (S0 :: S1 :: rep [S0;S1] n ++ [S1]).
    apply phFINx_@ID@.
  + unfold Cin_@ID@. rewrite Ip_pow2, pair_rot. reflexivity.
  + lia.
Qed.

(** ** Exit: from the inner all-ones anchor back to the outer family,
    closing under [lift] *)
Lemma exit_ov_@ID@ : forall n, exists m c',
  csteps tm m (@EIN@, ((rep [S1;S1] n ++ [S1]) ++ [S1], S0, @FF@)) = Some c'
  /\ c' = (@EDGE@, (S1 :: rep [S0;S1] (S n) ++ [S1], S0, @FX@)) /\ 0 < m.
Proof.
  intro n.
  do 2 eexists. split; [|split].
  + rewrite <- app_assoc. cbn [app].
    rewrite pair_fold, rep_dbl.
    eapply csteps_chain. { apply phP1i_@ID@. }
    eapply csteps_chain. { apply (phRIP_@ID@ (2 * S n)). }
    eapply csteps_chain. { apply phSTPOe_@ID@. }
    rewrite <- rep_dbl.
    eapply csteps_chain. { apply (phRET_@ID@ (S n)). }
    apply phFINe_@ID@.
  + reflexivity.
  + lia.
Qed.

Lemma lift_lblank_@ID@ : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.

(** ** The OUTER overflow lap: boot ; inner counting ; exit *)
Lemma lap_ov_@ID@ : forall p j', cview p = (S j', None) ->
  exists n c', csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p j' Ecv.
  destruct (cview_none_I p j' Ecv) as (HIp & HIs).
  pose proof (cview_none_shape p j' Ecv) as Hp.
  destruct (boot_ov_@ID@ j') as (m1 & c1 & Hb & Hc1 & Hm1).
  destruct (inner_to_fill_@ID@ (pow2 j')) as (m2 & Hi).
  destruct (exit_ov_@ID@ j') as (m3 & c3 & Hx & Hc3 & _).
  exists (m1 + (m2 + m3)), c3. split; [|split].
  + unfold Cc_@ID@. rewrite HIp.
    rewrite csteps_add, Hb. subst c1.
    rewrite csteps_add, Hi.
    rewrite <- Hp.
    unfold Cin_@ID@. rewrite HIp. exact Hx.
  + subst c3. unfold Cc_@ID@. rewrite HIs.
    rewrite <- app_assoc. cbn [app].
    change (rep [S1;S0] (S j') ++ S1 :: S1 :: S0 :: nil)
      with (rep [S1;S0] (S j') ++ [S1] ++ [S1] ++ [S0]).
    rewrite !app_assoc.
    rewrite lift_lblank_@ID@.
    rewrite pair_rot.
    @FXCLOSE@
  + lia.
Qed.

Lemma lap_@ID@ : forall p, exists n c', csteps tm n (Cc p) = Some c' /\
  lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
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

@VISLEMMAS@
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

VIS_QR = r'''(** @QR@ is entered by the turn (interior) and by the overflow stop. *)
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
'''

VIS_VC = r'''(** @QVC@: one step past the turn (interior) / past the overflow stop. *)
Lemma phVC_@ID@ : forall x L R, csteps tm 1 (@QR@,(L,S1,x::R)) = Some (@QVC@,(@WVC@::L,x,R)).
Proof. intros. reflexivity. Qed.

Lemma vis_VC_@ID@ : forall p, exists k c, csteps tm k (Cc p) = Some c /\ fst c = @QVC@.
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
      change (rep [S1] (S (2*j)) ++ [S0]) with (S1 :: rep [S1] (2*j) ++ [S0]).
      apply phVC_@ID@.
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
      change (rep [S1] (S (S (2*j'))) ++ [S0]) with (S1 :: rep [S1] (S (2*j')) ++ [S0]).
      apply phVC_@ID@.
    + reflexivity.
Qed.
'''

VIS_PREFA = r'''(** @QV@: @T@ steps from the anchor, inside the P1 window (uniform in p). *)
Lemma vis_A@N@_@ID@ : forall p, exists k c, csteps tm k (Cc p) = Some c /\ fst c = @QV@.
Proof.
  intro p. unfold Cc_@ID@. exists @T@. eexists. split.
  - apply phVA@N@_@ID@.
  - reflexivity.
Qed.
'''

VIS_DEEP_HEAD = r'''(** @QV@ fires only inside the OVERFLOW machinery; reach an all-ones
    counter by well-founded induction on [tovf] (the interior laps close
    EXACTLY), then run the overflow prefix into the witness window. *)
Lemma vis_D@N@_@ID@ : forall p, exists k c, csteps tm k (Cc p) = Some c /\ fst c = @QV@.
Proof.
  intro p; remember (tovf p) as fuel eqn:Ef; revert p Ef.
  induction fuel as [fuel IH] using (well_founded_induction lt_wf); intros p Ef.
  destruct (cview p) as [j oq] eqn:Ecv. destruct oq as [q0|].
  - assert (Hnz : tovf p <> 0).
    { intro H0. destruct (tovf0_allones p H0) as (jj & Hjj). rewrite Hjj in Ecv; discriminate. }
    destruct (lap_int_@ID@ p j q0 Ecv) as (n & c' & Hrun & Hc' & _). subst c'.
    destruct (IH (tovf (Pos.succ p)) (ltac:(rewrite tovf_succ by lia; lia)) (Pos.succ p) eq_refl) as (k & c & Hk & Hq).
    exists (n + k), c. rewrite csteps_add, Hrun. exact (conj Hk Hq).
  - destruct j as [|j'].
    { exfalso. destruct p; simpl in Ecv; [destruct (cview p); discriminate|discriminate|discriminate]. }
    destruct (cview_none_I p j' Ecv) as (HIp & _).
    unfold Cc_@ID@. eexists. eexists. split.
    + rewrite HIp, <- app_assoc. cbn [app].
      rewrite rep_dbl, <- !rep_slide.
      eapply csteps_chain. { apply phP1_@ID@. }
      eapply csteps_chain. { apply (phRIP_@ID@ (S (S (2*j')))). }
@DEEPTAC@
    + reflexivity.
Qed.
'''

DEEP_STPO = r'''      apply phVS@N@_@ID@.'''

DEEP_FINX = r'''      eapply csteps_chain. { apply phSTPO_@ID@. }
      change (rep [S1] (S (S (2*j'))) ++ [S0]) with (S1 :: S1 :: rep [S1] (2*j') ++ [S0]).
      rewrite <- rep_dbl.
      change (S1 :: S1 :: rep [S1;S1] j' ++ [S0]) with (rep [S1;S1] (S j') ++ [S0]).
      eapply csteps_chain. { apply (phRET_@ID@ (S j')). }
      change (rep [S0;S1] (S j') ++ [S1]) with (S0 :: S1 :: rep [S0;S1] j' ++ [S1]).
      apply phVX@N@_@ID@.'''

DEEP_P1I = r'''      eapply csteps_chain. { apply phSTPO_@ID@. }
      change (rep [S1] (S (S (2*j'))) ++ [S0]) with (S1 :: S1 :: rep [S1] (2*j') ++ [S0]).
      rewrite <- rep_dbl.
      change (S1 :: S1 :: rep [S1;S1] j' ++ [S0]) with (rep [S1;S1] (S j') ++ [S0]).
      eapply csteps_chain. { apply (phRET_@ID@ (S j')). }
      change (rep [S0;S1] (S j') ++ [S1]) with (S0 :: S1 :: rep [S0;S1] j' ++ [S1]).
      eapply csteps_chain. { apply phFINx_@ID@. }
      apply phVI@N@_@ID@.'''


def _mk_head_v2():
    """The V2 (pop-P1) template: P1/P1i pop the head-adjacent S1, ripple
    2j / S(2j') / S(2n), FIN closes over [S0;S0], FINx is the closed FINi
    window.  Constructed from HEAD by asserted textual surgery so the two
    variants cannot drift silently."""
    h = HEAD
    U_P1_A = 'Lemma U_P1_@ID@ : wsteps true true tm @NP1@ (@EDGE@,([],S0,[S0])) = Some (@ERIP@,([],S1,[S0])).'
    U_P1_B = 'Lemma U_P1_@ID@ : wsteps true true tm @NP1@ (@EDGE@,([S1],S0,[S0])) = Some (@ERIP@,([],S1,@PD@)).'
    U_P1I_A = 'Lemma U_P1i_@ID@ : wsteps true true tm @NP1I@ (@EIN@,([],S0,@FF@)) = Some (@ERIP@,([],S1,@FF@)).'
    U_P1I_B = 'Lemma U_P1i_@ID@ : wsteps true true tm @NP1I@ (@EIN@,([S1],S0,@FF@)) = Some (@ERIP@,([],S1,@PI@)).'
    U_FIN_A = 'Lemma U_FIN_@ID@ : wsteps true true tm @NFIN@ (@QR@,([],S1,[S1;S0])) = Some (@EDGE@,([S1],S0,[S0])).'
    U_FIN_B = 'Lemma U_FIN_@ID@ : wsteps true true tm @NFIN@ (@QR@,([],S1,@PD@)) = Some (@EDGE@,([S1],S0,[S0])).'
    U_FINX_A = 'Lemma U_FINx_@ID@ : wsteps true false tm @NFINX@ (@QR@,([S0],S1,[S0])) = Some (@EIN@,([],S0,@FF@)).'
    U_FINX_B = 'Lemma U_FINx_@ID@ : wsteps true true tm @NFINX@ (@QR@,([],S1,@XW@)) = Some (@EIN@,([S1],S0,@FF@)).'
    PH_P1_A = 'Lemma phP1_@ID@ : forall L R, csteps tm @NP1@ (@EDGE@,(L,S0,S0::R)) = Some (@ERIP@,(L,S1,S0::R)).'
    PH_P1_B = 'Lemma phP1_@ID@ : forall L R, csteps tm @NP1@ (@EDGE@,(S1::L,S0,S0::R)) = Some (@ERIP@,(L,S1,@PDC@R)).'
    PH_P1I_A = 'Lemma phP1i_@ID@ : forall L R, csteps tm @NP1I@ (@EIN@,(L,S0,@FFC@R)) = Some (@ERIP@,(L,S1,@FFC@R)).'
    PH_P1I_B = 'Lemma phP1i_@ID@ : forall L R, csteps tm @NP1I@ (@EIN@,(S1::L,S0,@FFC@R)) = Some (@ERIP@,(L,S1,@PIC@R)).'
    PH_FIN_A = 'Lemma phFIN_@ID@ : forall L R, csteps tm @NFIN@ (@QR@,(L,S1,S1::S0::R)) = Some (@EDGE@,(S1::L,S0,S0::R)).'
    PH_FIN_B = 'Lemma phFIN_@ID@ : forall L R, csteps tm @NFIN@ (@QR@,(L,S1,@PDC@R)) = Some (@EDGE@,(S1::L,S0,S0::R)).'
    PH_FINX_A = ('Lemma phFINx_@ID@ : forall L, csteps tm @NFINX@ (@QR@,(S0::L,S1,[S0])) = Some (@EIN@,(L,S0,@FF@)).\n'
                 'Proof. intros. exact (wsteps_frame_r _ _ _ _ _ _ _ _ _ _ L U_FINx_@ID@). Qed.')
    PH_FINX_B = ('Lemma phFINx_@ID@ : forall L R, csteps tm @NFINX@ (@QR@,(L,S1,S1::@PDC@R)) = Some (@EIN@,(S1::L,S0,@FFC@R)).\n'
                 'Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_FINx_@ID@). Qed.')
    LAPINT_A = (
        '    rewrite rep_dbl, <- rep_slide.\n'
        '    eapply csteps_chain. { apply phP1_@ID@. }\n'
        '    eapply csteps_chain. { apply (phRIP_@ID@ (S (2*j))). }\n'
        '    eapply csteps_chain. { apply phSTPI_@ID@. }\n'
        '    eapply csteps_chain. { apply phTRN_@ID@. }\n'
        '    change (rep [S1] (S (2*j)) ++ [S0]) with (S1 :: rep [S1] (2*j) ++ [S0]).\n'
        '    rewrite rep_slide, <- rep_dbl.\n'
        '    eapply csteps_chain. { apply (phRET_@ID@ j). }\n'
        '    apply phFIN_@ID@.')
    LAPINT_B = (
        '    rewrite rep_dbl, <- rep_slide.\n'
        '    change (rep [S1] (S (2*j))) with (S1 :: rep [S1] (2*j)). cbn [app].\n'
        '    eapply csteps_chain. { apply phP1_@ID@. }\n'
        '    eapply csteps_chain. { apply (phRIP_@ID@ (2*j)). }\n'
        '    eapply csteps_chain. { apply phSTPI_@ID@. }\n'
        '    eapply csteps_chain. { apply phTRN_@ID@. }\n'
        '    rewrite <- rep_dbl.\n'
        '    eapply csteps_chain. { apply (phRET_@ID@ j). }\n'
        '    apply phFIN_@ID@.')
    LAPINN_A = (
        '    rewrite rep_dbl, <- rep_slide.\n'
        '    eapply csteps_chain. { apply phP1i_@ID@. }\n'
        '    eapply csteps_chain. { apply (phRIP_@ID@ (S (2*j))). }\n'
        '    eapply csteps_chain. { apply phSTPI_@ID@. }\n'
        '    eapply csteps_chain. { apply phTRN_@ID@. }\n'
        '    change (rep [S1] (S (2*j)) ++ @FF@) with (S1 :: rep [S1] (2*j) ++ @FF@).\n'
        '    rewrite rep_slide, <- rep_dbl.\n'
        '    eapply csteps_chain. { apply (phRET_@ID@ j). }\n'
        '    apply phFINi_@ID@.')
    LAPINN_B = (
        '    rewrite rep_dbl, <- rep_slide.\n'
        '    change (rep [S1] (S (2*j))) with (S1 :: rep [S1] (2*j)). cbn [app].\n'
        '    eapply csteps_chain. { apply phP1i_@ID@. }\n'
        '    eapply csteps_chain. { apply (phRIP_@ID@ (2*j)). }\n'
        '    eapply csteps_chain. { apply phSTPI_@ID@. }\n'
        '    eapply csteps_chain. { apply phTRN_@ID@. }\n'
        '    rewrite <- rep_dbl.\n'
        '    eapply csteps_chain. { apply (phRET_@ID@ j). }\n'
        '    apply phFINi_@ID@.')
    BOOT_A = (
        '    rewrite rep_dbl, <- !rep_slide.\n'
        '    eapply csteps_chain. { apply phP1_@ID@. }\n'
        '    eapply csteps_chain. { apply (phRIP_@ID@ (S (S (2*n)))). }\n'
        '    eapply csteps_chain. { apply phSTPO_@ID@. }\n'
        '    change (rep [S1] (S (S (2*n))) ++ [S0]) with (S1 :: S1 :: rep [S1] (2*n) ++ [S0]).\n'
        '    rewrite <- rep_dbl.\n'
        '    change (S1 :: S1 :: rep [S1;S1] n ++ [S0]) with (rep [S1;S1] (S n) ++ [S0]).\n'
        '    eapply csteps_chain. { apply (phRET_@ID@ (S n)). }\n'
        '    change (rep [S0;S1] (S n) ++ [S1]) with (S0 :: S1 :: rep [S0;S1] n ++ [S1]).\n'
        '    apply phFINx_@ID@.')
    BOOT_B = (
        '    rewrite rep_dbl, <- !rep_slide.\n'
        '    change (rep [S1] (S (S (2*n)))) with (S1 :: rep [S1] (S (2*n))). cbn [app].\n'
        '    eapply csteps_chain. { apply phP1_@ID@. }\n'
        '    eapply csteps_chain. { apply (phRIP_@ID@ (S (2*n))). }\n'
        '    eapply csteps_chain. { apply phSTPO_@ID@. }\n'
        '    change (rep [S1] (S (2*n)) ++ @PD@) with (S1 :: rep [S1] (2*n) ++ @PD@).\n'
        '    rewrite rep_slide, <- rep_dbl.\n'
        '    eapply csteps_chain. { apply (phRET_@ID@ n). }\n'
        '    apply phFINx_@ID@.')
    EXIT_A = (
        '    rewrite pair_fold, rep_dbl.\n'
        '    eapply csteps_chain. { apply phP1i_@ID@. }\n'
        '    eapply csteps_chain. { apply (phRIP_@ID@ (2 * S n)). }\n'
        '    eapply csteps_chain. { apply phSTPOe_@ID@. }\n'
        '    rewrite <- rep_dbl.\n'
        '    eapply csteps_chain. { apply (phRET_@ID@ (S n)). }\n'
        '    apply phFINe_@ID@.')
    EXIT_B = (
        '    rewrite pair_fold, rep_dbl.\n'
        '    replace (2 * S n) with (S (S (2 * n))) by lia.\n'
        '    change (rep [S1] (S (S (2 * n)))) with (S1 :: rep [S1] (S (2 * n))). cbn [app].\n'
        '    eapply csteps_chain. { apply phP1i_@ID@. }\n'
        '    eapply csteps_chain. { apply (phRIP_@ID@ (S (2 * n))). }\n'
        '    eapply csteps_chain. { apply phSTPOe_@ID@. }\n'
        '    rewrite <- rep_slide.\n'
        '    change (S1 :: rep [S1] (S (2 * n)) ++ @PITC@nil) with (rep [S1] (S (S (2 * n))) ++ @PITC@nil).\n'
        '    replace (S (S (2 * n))) with (2 * S n) by lia.\n'
        '    rewrite <- rep_dbl.\n'
        '    eapply csteps_chain. { apply (phRET_@ID@ (S n)). }\n'
        '    apply phFINe_@ID@.')
    U_FINE_A = 'Lemma U_FINe_@ID@ : wsteps true true tm @NFINE@ (@QR@,([],S1,@FF@)) = Some (@EDGE@,([S1],S0,@FX@)).'
    U_FINE_B = 'Lemma U_FINe_@ID@ : wsteps true true tm @NFINE@ (@QR@,([],S1,@PIT@)) = Some (@EDGE@,([S1],S0,@FX@)).'
    PH_FINE_A = 'Lemma phFINe_@ID@ : forall L R, csteps tm @NFINE@ (@QR@,(L,S1,@FFC@R)) = Some (@EDGE@,(S1::L,S0,@FXC@R)).'
    PH_FINE_B = 'Lemma phFINe_@ID@ : forall L R, csteps tm @NFINE@ (@QR@,(L,S1,@PITC@R)) = Some (@EDGE@,(S1::L,S0,@FXC@R)).'
    U_FINI_A = 'Lemma U_FINi_@ID@ : wsteps true true tm @NFINI@ (@QR@,([],S1,@FI@)) = Some (@EIN@,([S1],S0,@FF@)).'
    U_FINI_B = 'Lemma U_FINi_@ID@ : wsteps true true tm @NFINI@ (@QR@,([],S1,@PI@)) = Some (@EIN@,([S1],S0,@FF@)).'
    PH_FINI_A = 'Lemma phFINi_@ID@ : forall L R, csteps tm @NFINI@ (@QR@,(L,S1,@FIC@R)) = Some (@EIN@,(S1::L,S0,@FFC@R)).'
    PH_FINI_B = 'Lemma phFINi_@ID@ : forall L R, csteps tm @NFINI@ (@QR@,(L,S1,@PIC@R)) = Some (@EIN@,(S1::L,S0,@FFC@R)).'
    for a, b in [(U_P1_A, U_P1_B), (U_P1I_A, U_P1I_B), (U_FIN_A, U_FIN_B),
                 (U_FINI_A, U_FINI_B), (PH_FINI_A, PH_FINI_B),
                 (U_FINE_A, U_FINE_B), (PH_FINE_A, PH_FINE_B),
                 (U_FINX_A, U_FINX_B), (PH_P1_A, PH_P1_B),
                 (PH_P1I_A, PH_P1I_B), (PH_FIN_A, PH_FIN_B),
                 (PH_FINX_A, PH_FINX_B), (LAPINT_A, LAPINT_B),
                 (LAPINN_A, LAPINN_B), (BOOT_A, BOOT_B), (EXIT_A, EXIT_B)]:
        assert a in h, 'HEAD_V2 source fragment missing: %r' % a[:70]
        h = h.replace(a, b)
    return h


HEAD_V2 = _mk_head_v2()

VIS_PREFA_V2 = (
    '(** @QV@: @T@ steps from the anchor, inside the P1 window (uniform in p). *)\n'
    'Lemma vis_A@N@_@ID@ : forall p, exists k c, csteps tm k (Cc p) = Some c /\\ fst c = @QV@.\n'
    'Proof.\n'
    '  intro p. destruct (Ip_head p) as (w & Hw). unfold Cc_@ID@.\n'
    '  rewrite Hw. cbn [app]. exists @T@. eexists. split.\n'
    '  - apply phVA@N@_@ID@.\n'
    '  - reflexivity.\n'
    'Qed.\n')

_V2_OV_PREFIX = (
    '    + rewrite HIp, <- app_assoc. cbn [app].\n'
    '      rewrite rep_dbl, <- !rep_slide.\n'
    '      change (rep [S1] (S (S (2*j\')))) with (S1 :: rep [S1] (S (2*j\'))). cbn [app].\n'
    '      eapply csteps_chain. { apply phP1_@ID@. }\n'
    '      eapply csteps_chain. { apply (phRIP_@ID@ (S (2*j\'))). }\n')

VIS_QR_V2 = (
    '(** @QR@ is entered by the turn (interior) and by the overflow stop. *)\n'
    'Lemma vis_R_@ID@ : forall p, exists k c, csteps tm k (Cc p) = Some c /\\ fst c = @QR@.\n'
    'Proof.\n'
    '  intro p. destruct (cview p) as [j oq] eqn:Ecv. destruct oq as [q0|].\n'
    '  - destruct (cview_some_I p j q0 Ecv) as (HIp & _).\n'
    '    unfold Cc_@ID@. eexists. eexists. split.\n'
    '    + rewrite HIp, <- app_assoc. cbn [app].\n'
    '      rewrite rep_dbl, <- rep_slide.\n'
    '      change (rep [S1] (S (2*j))) with (S1 :: rep [S1] (2*j)). cbn [app].\n'
    '      eapply csteps_chain. { apply phP1_@ID@. }\n'
    '      eapply csteps_chain. { apply (phRIP_@ID@ (2*j)). }\n'
    '      eapply csteps_chain. { apply phSTPI_@ID@. }\n'
    '      apply phTRN_@ID@.\n'
    '    + reflexivity.\n'
    '  - destruct j as [|j\'].\n'
    '    { exfalso. destruct p; simpl in Ecv; [destruct (cview p); discriminate|discriminate|discriminate]. }\n'
    '    destruct (cview_none_I p j\' Ecv) as (HIp & _).\n'
    '    unfold Cc_@ID@. eexists. eexists. split.\n'
    + _V2_OV_PREFIX +
    '      apply phSTPO_@ID@.\n'
    '    + reflexivity.\n'
    'Qed.\n')

_V2_DEEP_WRAP = (
    'Lemma vis_D@N@_@ID@ : forall p, exists k c, csteps tm k (Cc p) = Some c /\\ fst c = @QV@.\n'
    'Proof.\n'
    '  intro p; remember (tovf p) as fuel eqn:Ef; revert p Ef.\n'
    '  induction fuel as [fuel IH] using (well_founded_induction lt_wf); intros p Ef.\n'
    '  destruct (cview p) as [j oq] eqn:Ecv. destruct oq as [q0|].\n'
    '  - assert (Hnz : tovf p <> 0).\n'
    '    { intro H0. destruct (tovf0_allones p H0) as (jj & Hjj). rewrite Hjj in Ecv; discriminate. }\n'
    '    destruct (lap_int_@ID@ p j q0 Ecv) as (n & c\' & Hrun & Hc\' & _). subst c\'.\n'
    '    destruct (IH (tovf (Pos.succ p)) (ltac:(rewrite tovf_succ by lia; lia)) (Pos.succ p) eq_refl) as (k & c & Hk & Hq).\n'
    '    exists (n + k), c. rewrite csteps_add, Hrun. exact (conj Hk Hq).\n'
    '  - destruct j as [|j\'].\n'
    '    { exfalso. destruct p; simpl in Ecv; [destruct (cview p); discriminate|discriminate|discriminate]. }\n'
    '    destruct (cview_none_I p j\' Ecv) as (HIp & _).\n'
    '    unfold Cc_@ID@. eexists. eexists. split.\n'
    + _V2_OV_PREFIX +
    '@DEEPTAC@\n'
    '    + reflexivity.\n'
    'Qed.\n')

VIS_DEEP_HEAD_V2 = (
    '(** @QV@ fires only inside the OVERFLOW machinery; reach an all-ones\n'
    '    counter by well-founded induction on [tovf] (the interior laps close\n'
    '    EXACTLY), then run the overflow prefix into the witness window. *)\n'
    + _V2_DEEP_WRAP)

VIS_VC_V2 = (
    '(** @QVC@: one step past the overflow stop; every p reduces to an\n'
    '    overflow anchor by well-founded induction on [tovf]. *)\n'
    'Lemma phVC_@ID@ : forall x L R, csteps tm 1 (@QR@,(L,S1,x::R)) = Some (@QVC@,(@WVC@::L,x,R)).\n'
    'Proof. intros. reflexivity. Qed.\n'
    '\n'
    + _V2_DEEP_WRAP
    .replace('vis_D@N@_@ID@', 'vis_VC_@ID@')
    .replace('@QV@', '@QVC@')
    .replace('@DEEPTAC@',
             '      eapply csteps_chain. { apply phSTPO_@ID@. }\n'
             '      change (rep [S1] (S (2*j\')) ++ @PD@) with (S1 :: rep [S1] (2*j\') ++ @PD@).\n'
             '      apply phVC_@ID@.'))

DEEP_STPO_V2 = '      apply phVS@N@_@ID@.'

DEEP_FINX_V2 = (
    '      eapply csteps_chain. { apply phSTPO_@ID@. }\n'
    '      change (rep [S1] (S (2*j\')) ++ @PD@) with (S1 :: rep [S1] (2*j\') ++ @PD@).\n'
    '      rewrite rep_slide, <- rep_dbl.\n'
    '      eapply csteps_chain. { apply (phRET_@ID@ j\'). }\n'
    '      apply phVX@N@_@ID@.')

DEEP_P1I_V2 = (
    '      eapply csteps_chain. { apply phSTPO_@ID@. }\n'
    '      change (rep [S1] (S (2*j\')) ++ @PD@) with (S1 :: rep [S1] (2*j\') ++ @PD@).\n'
    '      rewrite rep_slide, <- rep_dbl.\n'
    '      eapply csteps_chain. { apply (phRET_@ID@ j\'). }\n'
    '      eapply csteps_chain. { apply phFINx_@ID@. }\n'
    '      apply phVI@N@_@ID@.')


def render_vis(variant, spec, E, QR, Ein, Ff, s, plan, ex):
    """Returns (uvis, phvis, lemmas, cases)."""
    v2 = (variant == 'v2')
    uvis, phvis, lemmas, cases = [], [], [], []
    na = nd = 0
    for q in range(4):
        kind = plan[q][0]
        if kind == 'anchor':
            cases.append('  - (* %s : the anchor state *)\n'
                         '    exists 0. eexists. split; reflexivity.' % ST[q])
        elif kind == 'qr':
            lemmas.append(VIS_QR_V2 if v2 else VIS_QR)
            cases.append('  - apply vis_R_@ID@.')
        elif kind == 'vc':
            lemmas.append((VIS_VC_V2 if v2 else VIS_VC)
                          .replace('@QVC@', ST[q])
                          .replace('@WVC@', SYM[plan[q][1]]))
            cases.append('  - apply vis_VC_@ID@.')
        elif kind == 'prefa':
            na += 1
            t, ext = plan[q][1], plan[q][2]
            if v2:
                uvis.append(
                    'Lemma U_VA%d_@ID@ : wsteps true true tm %d '
                    '(@EDGE@,([S1],S0,[S0])) = Some %s. '
                    'Proof. reflexivity. Qed.' % (na, t, cwin(ext)))
                phvis.append(
                    'Lemma phVA%d_@ID@ : forall L R, csteps tm %d '
                    '(@EDGE@,(S1::L,S0,S0::R)) = Some (%s,(%s,%s,%s)).\n'
                    'Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ '
                    'L R U_VA%d_@ID@). Qed.'
                    % (na, t, ST[ext[0]], ccons(ext[1], 'L'), SYM[ext[2]],
                       ccons(ext[3], 'R'), na))
                lemmas.append(VIS_PREFA_V2.replace('@QV@', ST[q])
                              .replace('@N@', str(na)).replace('@T@', str(t)))
            else:
                uvis.append(
                    'Lemma U_VA%d_@ID@ : wsteps true true tm %d '
                    '(@EDGE@,([],S0,[S0])) = Some %s. Proof. reflexivity. Qed.'
                    % (na, t, cwin(ext)))
                phvis.append(
                    'Lemma phVA%d_@ID@ : forall L R, csteps tm %d '
                    '(@EDGE@,(L,S0,S0::R)) = Some (%s,(%s,%s,%s)).\n'
                    'Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ '
                    'L R U_VA%d_@ID@). Qed.'
                    % (na, t, ST[ext[0]], ccons(ext[1], 'L'), SYM[ext[2]],
                       ccons(ext[3], 'R'), na))
                lemmas.append(VIS_PREFA.replace('@QV@', ST[q])
                              .replace('@N@', str(na)).replace('@T@', str(t)))
            cases.append('  - apply vis_A%d_@ID@.' % na)
        elif kind in ('stpo', 'finx', 'p1i'):
            nd += 1
            t, ext = plan[q][1], plan[q][2]
            if kind == 'stpo':
                uvis.append(
                    'Lemma U_VS%d_@ID@ : wsteps false true tm %d '
                    '(@ERIP@,([S0],S1,[])) = Some %s. '
                    'Proof. reflexivity. Qed.' % (nd, t, cwin(ext)))
                phvis.append(
                    'Lemma phVS%d_@ID@ : forall R, csteps tm %d '
                    '(@ERIP@,([S0],S1,R)) = Some (%s,(%s,%s,%s)).\n'
                    'Proof. intros. exact (wsteps_frame_l _ _ _ _ _ _ _ _ _ '
                    '_ R U_VS%d_@ID@). Qed.'
                    % (nd, t, ST[ext[0]], clist(ext[1]), SYM[ext[2]],
                       ccons(ext[3], 'R'), nd))
                tac = DEEP_STPO_V2 if v2 else DEEP_STPO
            elif kind == 'finx':
                if v2:
                    uvis.append(
                        'Lemma U_VX%d_@ID@ : wsteps true true tm %d '
                        '(@QR@,([],S1,@XW@)) = Some %s. '
                        'Proof. reflexivity. Qed.' % (nd, t, cwin(ext)))
                    phvis.append(
                        'Lemma phVX%d_@ID@ : forall L R, csteps tm %d '
                        '(@QR@,(L,S1,S1::@PDC@R)) = Some (%s,(%s,%s,%s)).\n'
                        'Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ '
                        '_ _ L R U_VX%d_@ID@). Qed.'
                        % (nd, t, ST[ext[0]], ccons(ext[1], 'L'),
                           SYM[ext[2]], ccons(ext[3], 'R'), nd))
                else:
                    uvis.append(
                        'Lemma U_VX%d_@ID@ : wsteps true false tm %d '
                        '(@QR@,([S0],S1,[S0])) = Some %s. '
                        'Proof. reflexivity. Qed.' % (nd, t, cwin(ext)))
                    phvis.append(
                        'Lemma phVX%d_@ID@ : forall L, csteps tm %d '
                        '(@QR@,(S0::L,S1,[S0])) = Some (%s,(%s,%s,%s)).\n'
                        'Proof. intros. exact (wsteps_frame_r _ _ _ _ _ _ _ '
                        '_ _ _ L U_VX%d_@ID@). Qed.'
                        % (nd, t, ST[ext[0]], ccons(ext[1], 'L'),
                           SYM[ext[2]], clist(ext[3]), nd))
                tac = DEEP_FINX_V2 if v2 else DEEP_FINX
            else:
                if v2:
                    uvis.append(
                        'Lemma U_VI%d_@ID@ : wsteps true true tm %d '
                        '(@EIN@,([S1],S0,@FF@)) = Some %s. '
                        'Proof. reflexivity. Qed.' % (nd, t, cwin(ext)))
                    phvis.append(
                        'Lemma phVI%d_@ID@ : forall L R, csteps tm %d '
                        '(@EIN@,(S1::L,S0,@FFC@R)) = Some (%s,(%s,%s,%s)).\n'
                        'Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ '
                        '_ _ L R U_VI%d_@ID@). Qed.'
                        % (nd, t, ST[ext[0]], ccons(ext[1], 'L'),
                           SYM[ext[2]], ccons(ext[3], 'R'), nd))
                else:
                    uvis.append(
                        'Lemma U_VI%d_@ID@ : wsteps true true tm %d '
                        '(@EIN@,([],S0,@FF@)) = Some %s. '
                        'Proof. reflexivity. Qed.' % (nd, t, cwin(ext)))
                    phvis.append(
                        'Lemma phVI%d_@ID@ : forall L R, csteps tm %d '
                        '(@EIN@,(L,S0,@FFC@R)) = Some (%s,(%s,%s,%s)).\n'
                        'Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ '
                        '_ _ L R U_VI%d_@ID@). Qed.'
                        % (nd, t, ST[ext[0]], ccons(ext[1], 'L'),
                           SYM[ext[2]], ccons(ext[3], 'R'), nd))
                tac = DEEP_P1I_V2 if v2 else DEEP_P1I
            lemmas.append((VIS_DEEP_HEAD_V2 if v2 else VIS_DEEP_HEAD)
                          .replace('@QV@', ST[q])
                          .replace('@N@', str(nd))
                          .replace('@DEEPTAC@', tac.replace('@N@', str(nd))))
            cases.append('  - apply vis_D%d_@ID@.' % nd)
        else:
            raise DeriveError('unknown visit kind %s' % kind)
    return uvis, phvis, lemmas, cases


def emit_source(variant, spec, E, Erip, QR, Ein, Ff, PD, PI, Fx, s, plan,
                p0, boot):
    ID = mach_id(spec)
    ex = Exec(spec)
    uvis, phvis, lemmas, cases = render_vis(variant, spec, E, QR, Ein, Ff, s,
                                            plan, ex)
    if list(Fx) == [0]:
        fxclose = 'reflexivity.'
    elif list(Fx) == []:
        fxclose = 'symmetry. apply (lift_app_blank _ _ _ []).'
    else:
        fxclose = ('change [S0;S0] with ([S0] ++ [S0]). '
                   'rewrite lift_app_blank. reflexivity.')
    sub = {
        '@ID@': ID, '@SPEC@': spec, '@TABLE@': coq_table(spec),
        '@EDGE@': ST[E], '@ERIP@': ST[Erip], '@QR@': ST[QR],
        '@EIN@': ST[Ein],
        '@FF@': clist(Ff), '@FFC@': ccons(Ff, ''),
        '@FI@': clist([1] + list(Ff)), '@FIC@': ccons([1] + list(Ff), ''),
        '@PD@': clist(PD), '@PDC@': ccons(PD, ''),
        '@PI@': clist(PI), '@PIC@': ccons(PI, ''),
        '@PIT@': clist(list(PI)[1:]), '@PITC@': ccons(list(PI)[1:], ''),
        '@XW@': clist([1] + list(PD)),
        '@FX@': clist(Fx), '@FXC@': ccons(Fx, ''),
        '@NP1@': str(s['nP1']), '@NP1I@': str(s['nP1i']),
        '@NRIP@': str(s['nRIP']), '@NSTP@': str(s['nSTP']),
        '@NTRN@': str(s['nTRN']), '@NRET@': str(s['nRET']),
        '@NFIN@': str(s['nFIN']), '@NFINI@': str(s['nFINi']),
        '@NSTPO@': str(s['nSTPO']), '@NSTPOE@': str(s['nSTPOE']),
        '@NFINX@': str(s['nFINX']), '@NFINE@': str(s['nFINE']),
        '@P0@': str(p0), '@BOOT@': str(boot),
        '@FXCLOSE@': fxclose,
        '@UVIS@': ('\n'.join(uvis) + '\n') if uvis else '',
        '@PHVIS@': ('\n'.join(phvis) + '\n') if phvis else '',
        '@VISLEMMAS@': '\n'.join(lemmas),
        '@VISCASES@': '\n'.join(cases),
    }
    src = HEAD_V2 if variant == 'v2' else HEAD
    for _ in range(3):
        for k, v in sorted(sub.items(), key=lambda kv: -len(kv[0])):
            src = src.replace(k, v)
    return src


# ---------------------------------------------------------------- pipeline ---
def coqc(path):
    p = subprocess.run(
        ['bash', '-lc', 'cd %s && coqc -native-compiler no -Q theories BBB4 %s'
         % (REPO, path)], capture_output=True, text=True, timeout=1800)
    return p.returncode, p.stdout + p.stderr


def print_assumptions(ID, scratch, pref):
    chk = os.path.join(scratch, 'pax_%s.v' % ID)
    with open(chk, 'w') as f:
        f.write('From BBB4.Machines.Counters Require Import %s_%s.\n'
                'Print Assumptions nqh_%s.\n' % (pref, ID, ID))
    return coqc(chk)


def process(spec, do_emit, scratch, force=False, mirror=False):
    res = {'spec': spec, 'ok': False, 'mirror': mirror}
    rspec = spec
    if mirror:
        spec = mirror_spec(spec)
    try:
        edge, tail, p0 = derive_tail(spec, 'A', encname='Ip')
        if list(tail) != TAIL:
            raise DeriveError('anchor tail %s is not [1,0] (not flip-shaped)'
                              % tail)
        E = LAB.index(edge)
        variant, s, U = derive_interior(spec, E)
        if variant == 'v1':
            msgs, Erip, QR = check_interior_shapes(E, U)
        else:
            msgs, Erip, QR = check_interior_shapes_v2(E, U)
        if msgs:
            raise DeriveError('interior shape: ' + '; '.join(msgs))
        PD = list(U['P1'][1][3])
        cands = find_inner_anchor(spec, E)
        if not cands:
            raise DeriveError('no inner anchor decodes in the overflow lap')
        err = None
        done = False
        for Ein, sfar, _times in cands[:4]:
            try:
                s3, U3, Ff = derive_boot(spec, variant, E, Ein, sfar, s)
                msgs = check_boot_shapes(variant, Erip, Ein, QR, Ff, PD, U3)
                if msgs:
                    raise DeriveError('boot shape: ' + '; '.join(msgs))
                s2, U2 = derive_inner(spec, variant, E, Ein, Ff, s3)
                msgs = check_inner_shapes(variant, Erip, QR, Ein, Ff, U2)
                PI = list(U2['P1i'][1][3])
                if msgs:
                    raise DeriveError('inner shape: ' + '; '.join(msgs))
                s4, U4, Fx = derive_exit(spec, variant, E, Ein, Ff, s2)
                msgs = check_exit_shapes(variant, E, Erip, Ein, QR, Ff, PI,
                                         Fx, U4)
                if msgs:
                    raise DeriveError('exit shape: ' + '; '.join(msgs))
                done = True
                break
            except DeriveError as e:
                err = e
        if not done:
            raise err or DeriveError('no inner candidate works')
        validate_all(spec, variant, E, Ein, Ff, s4)
        p0, boot = boot_probe(spec, E, p0)
        plan = visit_plan(spec, variant, E, Erip, QR, Ein, Ff, PD, s4)
    except (DeriveError, Wall, AssertionError, KeyError, IndexError) as e:
        res['why'] = str(e)
        return res
    res.update({'edge': edge, 'p0': p0, 'boot': boot, 'variant': variant,
                'Erip': LAB[Erip], 'QR': LAB[QR], 'Ein': LAB[Ein],
                'Ff': list(Ff), 'Fx': list(Fx), 'PD': PD, 'PI': PI,
                'skel': {k: v for k, v in s4.items()},
                'plan': {LAB[q]: plan[q][0] for q in plan}})
    if not do_emit:
        res['ok'] = True
        res['why'] = 'derived+validated (not emitted)'
        return res
    ID = mach_id(rspec)
    pref = 'IXPM' if mirror else 'IXP'
    path = os.path.join(OUTDIR, '%s_%s.v' % (pref, ID))
    if os.path.exists(path) and not force:
        res['ok'] = True
        res['why'] = 'file exists -- skipped emission'
        return res
    try:
        src = emit_source(variant, spec, E, Erip, QR, Ein, Ff, PD, PI, Fx,
                          s4, plan, p0, boot)
        if mirror:
            src = mirrorize(src, rspec, spec)
    except (DeriveError, RuntimeError) as e:
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
    ap.add_argument('--mirror', action='store_true')
    ap.add_argument('--force', action='store_true')
    ap.add_argument('--json')
    ap.add_argument('--limit', type=int)
    ap.add_argument('--scratch', default='/tmp')
    a = ap.parse_args()
    specs = list(a.specs)
    if a.list:
        specs += [x.strip() for x in open(a.list) if x.strip()]
    if a.limit:
        specs = specs[:a.limit]
    out = []
    for spec in specs:
        try:
            r = process(spec, a.emit, a.scratch, a.force, a.mirror)
        except Exception as e:                                # noqa: BLE001
            r = {'spec': spec, 'ok': False,
                 'why': 'CRASH %s: %s' % (type(e).__name__, e)}
        out.append(r)
        extra = ''
        if 'skel' in r:
            extra = ' %s E=%s Erip=%s QR=%s Ein=%s Ff=%s Fx=%s skel=%s plan=%s' % (
                r['variant'], r['edge'], r['Erip'], r['QR'], r['Ein'],
                r['Ff'], r['Fx'], r['skel'], r['plan'])
        print('%s %s %s%s' % ('PASS' if r['ok'] else 'FAIL', spec,
                              r.get('why', ''), extra))
        sys.stdout.flush()
    if a.json:
        with open(a.json, 'w') as f:
            json.dump(out, f, indent=1, default=str)
    print('== %d/%d passed' % (sum(1 for r in out if r['ok']), len(out)))


if __name__ == '__main__':
    main()
