#!/usr/bin/env python3
"""UNTRUSTED emitter: the REGISTER x COUNTER route -- a piecewise [Cc] with a
NESTED branch inside it (WAVE28 section 3d, the composition that did not
exist).

The `no overflow phase at K=6` bucket's readable half is a counter whose
anchor FRAME (the state and the constant cells past the head) depends on the
octave.  `tools/counters/regscan.py` chases the family forward and reads each
frame off the machine; `regprobe.py` fits the laps PER OCTAVE CLASS, which is
what makes the shape statable:

    Cc p = if virt p then VIRT p else (q, E p ++ tail, S0, frame (podd p))

with [virt p] the anchors at a power of two whose frame is the machine's own
transient one, and [podd] ([Counters/RegGlue.v]) the octave parity.  There
are four lap branches and they are NOT four ordinary chains:

    interior   (virt p = false, cview p = (j, Some q0))    affine, exact
    overflow   (cview p = (S j, None)), ONE CHAIN PER PARITY  affine, exact
    virt       (virt p = true)                             boot + inner
                                                           counter + exit

The virtual arm is the register step, and it costs [Theta(2^k)]: the machine
re-counts the whole counter to move the register mark one place.  It is
carried by [Counters/NestedLapLift.nested_overflow_lift], whose [p] and [v0]
are ordinary arguments -- so it composes with a piecewise [Cc] with nothing
new in [theories/].  The fences are [Counters/SkipGlue.v]'s
([reach_ovf_skip] / [vis_via_skip], the interior-lap hypothesis GUARDED by
"not a virtual anchor"), and the closer is [LapGlue.glue_neverqh].

Everything here is untrusted: the kernel re-runs [srun] on every chain and
the anchor glue is proved.  On top of that this module differentially
validates EVERY branch against the raw simulator -- exact step counts, exact
configurations, [lift]-equal landings, and every inner lap of every register
step -- before a board is written.

Usage
  regcert.py --json tools/counters/reg113.json [--kind KIND] [--emit]
  regcert.py --spec SPEC --enc ENC [--tail '[0]'] [--mirror] [--emit]
"""
import argparse
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, '..', '..'))
sys.path.insert(0, HERE)

import emit_lapcert as EL                                          # noqa: E402
import nestcert as NC                                              # noqa: E402
import lapcert as LC                                               # noqa: E402
import regscan as RS                                               # noqa: E402
from emit_lapcert import ENCDATA, ENC, ENCS, coqc                  # noqa: E402
from emit_interleave import (parse, LAB, ST, carry, mach_id,       # noqa: E402
                             coq_table, clist)
from mirror_common import mirror_spec, mirrorize                   # noqa: E402

PREFIX = 'REG'
OUTDIR = os.path.join(REPO, 'theories', 'Machines', 'Counters')
PMAX = 140
HI = 200                  # anchors the differential validation replays


class RegError(Exception):
    """This machine does not take the register route."""


def F(f):
    return (tuple(f), (), 0, 0, ())


def octave(p):
    return p.bit_length() - 1


# ------------------------------------------------------------------ read ---

def walk(dspec, enc, tail, pmax=PMAX):
    """The chase, keeping the CONFIGURATION at every anchor."""
    sd = RS.seeds(dspec, enc, tuple(tail))
    if not sd:
        raise RegError('no seed rest')
    v0, cfg0 = sd[0]
    tab = parse(dspec)
    encf, tl = ENC[enc], tuple(tail)
    out, cfg = {v0: cfg0}, cfg0
    for p in range(v0, pmax):
        want = tuple(encf(p + 1)) + tl
        for _ in range(RS.LAPCAP):
            cfg = LC.wstep(tab, False, False, cfg)
            if (cfg[2] == 0 and tuple(cfg[1]) == want
                    and len(LC.rstrip0(cfg[3])) <= RS.FARMAX):
                out[p + 1] = cfg
                break
        else:
            break
    return tab, out, v0


def frame_probe(dspec, enc, tail, vlo=4, vhi=320, maxT=6000000):
    """The TWO-FORM reader: per octave, the rest frames that cover EVERY
    value of that octave.

    [walk] chases forward and takes the FIRST rest whose word matches, which
    on this bucket is measured to be the wrong one: a machine that rests
    twice per value -- once with the wall at the head and once past it --
    reads as a GROWING far under the chase and as a CONSTANT period-2 far
    here (WAVE29 section 5b).  So collect every rest, key it by
    (state, far), and keep only the keys that see the whole octave.

    Returns (frames, cfgs): [frames] maps an octave to the set of frames
    covering it, [cfgs] one witnessing configuration per (value, frame)."""
    tab = parse(dspec)
    d = ENCDATA[enc]
    A, B, C = tuple(d['uD']), tuple(d['uS']), tuple(d['soD'])
    tl = tuple(tail)
    seen, wit = {}, {}
    cfg = (0, (), 0, ())
    for _ in range(maxT):
        try:
            cfg = LC.wstep(tab, False, False, cfg)
        except LC.Halt:
            break
        q, l, h, r = cfg
        if h:
            continue
        if len(l) < len(tl) or (tl and tuple(l[len(l) - len(tl):]) != tl):
            continue
        w = l[:len(l) - len(tl)] if tl else l
        v = NC.decode(w, A, B, C)
        if v is None or not vlo <= v < vhi:
            continue
        f = (q, LC.rstrip0(r))
        seen.setdefault(v.bit_length() - 1, {}).setdefault(f, set()).add(v)
        wit.setdefault((v, f), cfg)
    frames = {}
    for k, byf in seen.items():
        want = 1 << k
        if (want << 1) > vhi:
            continue
        full = {f for f, vs in byf.items() if len(vs) == want}
        if full:
            frames[k] = full
    return frames, wit


def frames_of_probe(frames):
    """Pick one frame per octave so that the choice is period 1 or 2 in the
    octave, preferring the SHORTEST far (a constant wall over a growing
    one)."""
    ks = sorted(frames)
    if len(ks) < 4:
        raise RegError('probe covers only %d octaves' % len(ks))
    ks = ks[:-1] if len(ks) > 4 else ks
    for P in (1, 2):
        pick, ok = {}, True
        for b in range(P):
            common = None
            for k in ks:
                if (k - ks[0]) % P != b:
                    continue
                common = frames[k] if common is None else common & frames[k]
            if not common:
                ok = False
                break
            pick[b] = min(common, key=lambda f: (len(f[1]), f))
        if not ok:
            continue
        return P, {k: pick[(k - ks[0]) % P] for k in ks}, ks
    raise RegError('no period-1 or -2 frame covers every octave')


def read_frames(cfgs, floor):
    """The octave frames and the VIRTUAL octaves, read off the walk.

    A power of two whose frame is the octave's own is NOT virtual: it is an
    ordinary interior anchor and the flat route already covers it.  Only the
    powers of two the machine rests at in a DIFFERENT frame are held out --
    which is the whole reason the earlier scan's `+virt` classification
    over-counted them."""
    fr = {p: (c[0], LC.rstrip0(c[3])) for p, c in cfgs.items()}
    ps = sorted(fr)
    byoct, atpow = {}, {}
    for p in ps:
        k = octave(p)
        if (1 << k) < ps[0] or (1 << (k + 1)) - 1 > ps[-1] or p < floor:
            continue
        if p == (1 << k):
            atpow[k] = fr[p]
            continue
        if k in byoct and byoct[k] != fr[p]:
            raise RegError('frame moves INSIDE octave %d' % k)
        byoct.setdefault(k, fr[p])
    ks = sorted(byoct)
    if len(ks) < 4:
        raise RegError('walk covers only %d octaves' % len(ks))
    virt = sorted(k for k in ks if k in atpow and atpow[k] != byoct[k])
    return byoct, atpow, virt, ks


def frames_by_parity(byoct, atpow, virt, ks):
    """(frame far by octave parity, VIRT far by octave parity, the [virt]
    selector, the two states).

    The octave frame is read as a function of the parity of the octave, and
    so is the VIRTUAL frame -- on two of the four `period-2+virt` rows the
    machine rests at EVERY power of two in a transient frame, and that frame
    alternates too."""
    st_f = byoct[ks[0]][0]
    if any(byoct[k][0] != st_f for k in ks):
        raise RegError('frame STATE varies by octave')
    fpar = {}
    for k in ks:
        b = k % 2
        if b in fpar and fpar[b] != byoct[k][1]:
            raise RegError('frame far is not a function of octave parity')
        fpar[b] = byoct[k][1]
    if len(fpar) < 2:
        raise RegError('walk covers only one octave parity')
    if not virt:
        raise RegError('no virtual anchor: the flat/nested route applies')
    st_v = atpow[virt[0]][0]
    if any(atpow[k][0] != st_v for k in virt):
        raise RegError('virtual frame STATE varies by octave')
    fparv = {}
    for k in virt:
        b = k % 2
        if b in fparv and fparv[b] != atpow[k][1]:
            raise RegError('virtual far is not a function of octave parity')
        fparv[b] = atpow[k][1]
    vp = sorted(fparv)
    if len(vp) == 2:
        vsel = 'true'
    elif vp == [0]:
        vsel = 'negb (podd p)'
    else:
        vsel = 'podd p'
    # every octave of a virtual parity must actually be virtual
    for k in ks:
        if (k % 2 in fparv) != (k in virt):
            raise RegError('virtuality is not a function of octave parity')
    for b in (0, 1):
        fparv.setdefault(b, fparv[vp[0]])
    return fpar, fparv, vsel, st_f, st_v


# ------------------------------------------------------------ derivation ---

def _chain(tab, el, er, a, b, lift=False):
    try:
        ch = LC.derive_chain(tab, el, er, a, b, lift=lift)
    except Exception:                                              # noqa: BLE001
        return None, None
    if ch is None:
        return None, None
    r = LC.srun(tab, el, er, ch, a)
    if r is None:
        return None, None
    return ch, r


def _nested(tab, enc, st_v, tail, src_peel, dst, mid, K):
    """boot + inner counter + exit, at the symbolic index [K].

    The inner family is ENUMERATED (nestcert's lesson: the best-scoring key
    is measured never to be the one the boot lands on), and the boot is
    stated from the PEELED source -- the register step's first move is onto
    the counter's own top block, and without the peel the head has no
    concrete cell to step onto."""
    keys = NC.families(mid, ENCDATA, ENCS, K=K)
    if not keys:
        raise RegError('no inner family at pow2 k')
    last = 'no inner family'
    for key in keys[:24]:
        CinS, CinF, AI0, AI1 = NC.endpoints(ENCDATA, enc, st_v, tail, (), key)
        chb, rb = _chain(tab, True, True, src_peel, CinS)
        if chb is None or rb[0] != CinS:
            last = 'no boot chain'
            continue
        chn, rn = _chain(tab, False, True, AI0, AI1)
        if chn is None or rn[0] != AI1 or rn[2] == 0:
            last = 'no inner interior chain'
            continue
        che, re = _chain(tab, True, True, CinF, dst)
        if che is None or re[0] != dst:
            last = 'no exit chain'
            continue
        return dict(key=key, CinS=CinS, CinF=CinF, AI0=AI0, AI1=AI1,
                    chb=chb, cb=(rb[1], rb[2]), chn=chn, cn=(rn[1], rn[2]),
                    che=che, ce=(re[1], re[2]))
    raise RegError(last)


def derive(spec, enc, tail, mirrored, pmax=PMAX):
    dspec = mirror_spec(spec) if mirrored else spec
    tab, cfgs, v0 = walk(dspec, enc, tail, pmax)
    d = ENCDATA[enc]
    if d['obS'] != 0:
        raise RegError('obS != 0 alphabets are not wired for this route')
    uS, uD = tuple(d['uS']), tuple(d['uD'])
    sS, sD = tuple(d['sS']), tuple(d['sD'])
    soS, soD = tuple(d['soS']), tuple(d['soD'])
    tail = tuple(tail)

    floor = max(8, v0)
    byoct, atpow, virt, ks = read_frames(cfgs, floor)
    fpar, fparv, vsel, st_f, st_v = frames_by_parity(byoct, atpow, virt, ks)
    vpar = sorted({k % 2 for k in virt})
    p0 = 1 << ks[0]

    # ---- the interior lap, one chain per octave parity.  The frame sits
    # in the chain's own right side (the head steps onto it on some
    # machines), so it is CONCRETE and the opaque right tail is empty.
    #
    # READ THE LANDING, NOT ITS PADDING.  The chase strips trailing blanks
    # off the far side, so a frame the machine actually leaves as [.. S0]
    # is reported one cell short -- and then the interior lap lands one
    # written blank past the anchor and closes only up to [lift], which
    # [SkipGlue.reach_ovf_skip] cannot use.  Recover the padding by trying
    # it: whichever far makes the interior chain land EXACTLY is the frame,
    # and the whole board is then stated against it.
    ints = {}
    for b in (0, 1):
        got = None
        for pad in range(3):
            far = tuple(fpar[b]) + (0,) * pad
            A0 = (st_f, ((), uS, 1, 0, sS), 0, F(far))
            A1 = (st_f, ((), uD, 1, 0, sD), 0, F(far))
            ch, r = _chain(tab, False, True, A0, A1)
            if ch is not None and r[0] == A1 and r[2] > 0:
                got = (far, A0, A1, ch, (r[1], r[2]))
                break
        if got is None:
            raise RegError('no interior chain at octave parity %d' % b)
        fpar[b] = got[0]
        ints[b] = dict(A0=got[1], A1=got[2], ch=got[3], c=got[4])

    # ---- the overflow laps, one per octave parity.  The anchor at
    # 2^(S j) is virtual exactly when (S j)'s parity is a virtual one.
    ovf = {}
    for b in (0, 1):
        B0 = (st_f, ((), uS, 1, 0, soS + tail), 0, F(fpar[b]))
        nb = 1 - b
        tgt_virt = nb in vpar
        if tgt_virt:
            B1 = (st_v, ((), uD, 1, 1, soD + tail), 0, F(fparv[nb]))
        else:
            B1 = (st_f, ((), uD, 1, 1, soD + tail), 0, F(fpar[nb]))
        ch, r = _chain(tab, True, True, B0, B1)
        if ch is None or r[0] != B1:
            raise RegError('no overflow chain at octave parity %d' % b)
        ovf[b] = dict(B0=B0, B1=B1, ch=ch, c=(r[1], r[2]), virt=tgt_virt)

    # ---- the register steps, one arm per VIRTUAL octave parity.  The
    # source is the PEELED virtual anchor: the step's first move is onto
    # the counter's own top block and the unpeeled form denies the head a
    # concrete cell to step onto (the standing peel).
    vlap = {}
    for b in vpar:
        VS = (st_v, (uD, uD, 1, 0, soD + tail), 0, F(fparv[b]))
        VC = (st_v, ((), uD, 1, 1, soD + tail), 0, F(fparv[b]))
        VT = (st_f, (uS, uD, 1, 0, soD + tail), 0, F(fpar[b]))
        ch, r = _chain(tab, True, True, VS, VT)
        if ch is not None and r[0] == VT and r[2] > 0:
            vlap[b] = dict(kind='flat', VS=VS, T=VT, ch=ch, c=(r[1], r[2]),
                           key=(enc, st_f, (), (), 0))
            continue
        ch, r = _chain(tab, True, True, VC, VT)
        if ch is not None and r[0] == VT and r[2] > 0:
            vlap[b] = dict(kind='flat', VS=VC, T=VT, ch=ch, c=(r[1], r[2]),
                           key=(enc, st_f, (), (), 0))
            continue
        cands = [k for k in virt if k % 2 == b and k <= 6]
        if not cands:
            raise RegError('no measured virtual anchor at parity %d' % b)
        K = max(cands)
        p = 1 << K
        if p not in cfgs or (p + 1) not in cfgs:
            raise RegError('walk does not reach the virtual anchor 2^%d' % K)
        nx = cfgs[p + 1]
        want = (nx[0], tuple(ENC[enc](p + 1)) + tail, LC.rstrip0(nx[3]))
        mid = _phase(tab, cfgs[p], want)
        nest = _nested(tab, enc, st_f, tail, VS, VT, mid, K)
        vlap[b] = dict(kind='nested', VS=VS, T=VT, **nest)

    D = dict(spec=dspec, orig=spec, mirror=mirrored, enc=enc,
             tail=list(tail), st_f=st_f, st_v=st_v, vsel=vsel,
             fpar={b: list(fpar[b]) for b in (0, 1)},
             fparv={b: list(fparv[b]) for b in (0, 1)},
             vpar=vpar, virt=virt, ks=ks, p0=p0, ints=ints,
             ovf=ovf, vlap=vlap)
    D['val'] = validate(tab, D, cfgs)
    D['vis'] = visits(tab, D)
    D['boot'] = boot(tab, D, cfgs)
    return D


def _phase(tab, cfg0, want):
    """Every blank-head configuration strictly inside one register step."""
    mid, cfg = [], cfg0
    for _ in range(4000000):
        cfg = LC.wstep(tab, False, False, cfg)
        q, l, h, r = cfg
        if h == 0 and q == want[0] and tuple(l) == want[1] \
                and LC.rstrip0(r) == want[2]:
            return mid
        if h == 0:
            mid.append((q, LC.rstrip0(l), LC.rstrip0(r)))
    raise RegError('register step does not close')


# ------------------------------------------------------------ validation ---

def _den(side, j):
    pre, u, a, b, post = side
    return tuple(pre) + tuple(u) * (a * j + b) + tuple(post)


def _denc(sc, j):
    q, ls, h, rs = sc
    return (q, _den(ls, j), h, _den(rs, j))


def _anchor(D, encf, p):
    """The board's own [Cc p], as a raw configuration."""
    k = octave(p)
    if k in D['virt'] and p == (1 << k):
        return (D['st_v'], tuple(encf(p)) + tuple(D['tail']), 0,
                tuple(D['fparv'][k % 2]))
    return (D['st_f'], tuple(encf(p)) + tuple(D['tail']), 0,
            tuple(D['fpar'][k % 2]))


def validate(tab, D, cfgs, hi=HI):
    """Replay EVERY branch against the raw simulator: exact step counts,
    exact configurations, [lift]-equal landings, and -- on each register
    step -- every inner lap of its inner counter."""
    encf = ENC[D['enc']]
    n, ninner, nreg = 0, 0, 0
    for p in range(D['p0'], hi):
        k = octave(p)
        # the NEXT anchor must also lie in an octave the walk fully saw:
        # its frame is what the lap is validated against.
        if octave(p + 1) > D['ks'][-1]:
            break
        start = _anchor(D, encf, p)
        want = _anchor(D, encf, p + 1)
        if k in D['virt'] and p == (1 << k):
            nreg += 1
            V = D['vlap'][k % 2]
            if V['kind'] == 'flat':
                steps = V['c'][0] * (k - 1) + V['c'][1]
            else:
                steps = V['cb'][0] * (k - 1) + V['cb'][1]
                cur = EL.sim(tab, start, steps)
                if not EL.eqlift(cur, _denc(V['CinS'], k - 1)):
                    raise RegError('p=%d boot -> %r want %r' %
                                   (p, cur, _denc(V['CinS'], k - 1)))
                v = 1 << (k - 1)
                while True:
                    i, ov = carry(v)
                    if ov:
                        break
                    cur = EL.sim(tab, cur, V['cn'][0] * i + V['cn'][1])
                    ninner += 1
                    v += 1
                if not EL.eqlift(cur, _denc(V['CinF'], k - 1)):
                    raise RegError('p=%d inner fill -> %r want %r' %
                                   (p, cur, _denc(V['CinF'], k - 1)))
                steps = V['ce'][0] * (k - 1) + V['ce'][1]
                start = cur
        else:
            j, ov = carry(p)
            if ov:
                # [carry] reports the ONES COUNT; the chain is stated at
                # [cview p = (S j, None)], i.e. one lower.
                b = k % 2
                steps = D['ovf'][b]['c'][0] * (j - 1) + D['ovf'][b]['c'][1]
            else:
                b = k % 2
                steps = D['ints'][b]['c'][0] * j + D['ints'][b]['c'][1]
        got = EL.sim(tab, start, steps)
        if not EL.eqlift(got, want):
            raise RegError('p=%d branch: %d steps -> %r want %r' %
                           (p, steps, got, want))
        n += 1
    return '%d anchors, %d register steps, %d inner laps' % (n, nreg, ninner)


# ---------------------------------------------------------------- visits ---

def visits(tab, D):
    """A witness for every state at EVERY overflow anchor -- both parities,
    since [SkipGlue.vis_via_skip]'s hypothesis ranges over all of them."""
    out = {}
    for q in range(4):
        pre = {}
        for b in (0, 1):
            O = D['ovf'][b]
            pre[b] = LC.reach_state(tab, True, True, O['B0'], O['ch'], q)
            if pre[b] is None:
                raise RegError('no visit witness for state %s at octave '
                               'parity %d' % (LAB[q], b))
        out[q] = pre
    return out


def boot(tab, D, cfgs):
    """The step count from the blank tape to [Cc p0]."""
    encf = ENC[D['enc']]
    want = _anchor(D, encf, D['p0'])
    cfg = (0, (), 0, ())
    for t in range(400000):
        if (cfg[0] == want[0] and cfg[2] == want[2]
                and LC.rstrip0(cfg[1]) == LC.rstrip0(want[1])
                and LC.rstrip0(cfg[3]) == LC.rstrip0(want[3])):
            return t
        cfg = LC.wstep(tab, False, False, cfg)
    raise RegError('no bootstrap to p0=%d' % D['p0'])

# ---------------------------------------------------------------- render ---

BOARD = r'''(** * REG_@ID@: machine @SPEC@, boarded by CERTIFICATE (REGISTER route).

    Auto-emitted by tools/counters/regcert.py (UNTRUSTED emitter; the Coq
    kernel re-runs the checker on every line below).  A binary counter under
    the @ENCF@ digit alphabet (@ENCM@.v) whose anchor FRAME depends on the
    OCTAVE: the machine keeps a REGISTER mark past the head and moves it once
    per octave, so the family is (register state x counter) and the anchor is
    PIECEWISE (WAVE28 section 3c, the `period-2+virt` class).

      Cc p = if virt p then (@STVN@, E p ++ tail, S0, frmv p)
             else (@STFN@, E p ++ tail, S0, frm p)

    with [RegGlue.podd] the octave parity ([podd p = true] iff the octave is
    odd), [frm]/[frmv] the two frames it selects, and [virt p] the powers of
    two the machine rests at in a DIFFERENT frame from their own octave's --
    the SKIP route's virtual anchor, one dimension up.  The lap branches are
    NOT all chains:

      interior  (virt p = false, cview p = (j, Some q0)):  @CI@ steps, exact,
                the frame carried as the RIGHT OPAQUE TAIL so ONE chain
                covers both octave parities
      overflow  (cview p = (S j, None)), one chain per parity:
                podd p = true: @CO1@   podd p = false: @CO0@
      register  (virt p = true), one arm per parity: @VDESC@

    The register step is the point: the mark cannot be moved without a pass
    that COUNTS, so a NESTED branch sits inside a piecewise [Cc] and the
    exponent stays inside the [exists n] of
    [Counters/NestedLapLift.inner_to_fill_lift].  [Counters/SkipGlue.v]
    fences the virtual anchors ([reach_ovf_skip] / [vis_via_skip], the
    interior-lap hypothesis GUARDED by "not virtual"),
    [Counters/RegGlue.v] supplies the octave parity, and the closer is
    [LapGlue.glue_neverqh] directly.

    Differentially validated against the raw simulator on EVERY branch --
    step counts AND configurations, every inner lap of every register step --
    for @VAL@.
    Axiom footprint: [functional_extensionality_dep] (via [CTape.lift]). *)
From Coq Require Import Arith Lia Bool List PArith Wellfounded.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape LapGlue MonoCounter JpCounter
                                  @MODS@ LapCertGlue LapCertGlueLift
                                  IXPGadgets NestedLap NestedLapLift
                                  SkipGlue RegGlue.
From BBB4.Census Require Import TNF_QH.
From BBB4.Checkers Require Import LapDecider.
Import ListNotations.

Definition mk_@ID@ (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_@ID@.

(** @SPEC@ *)
Definition tm_@ID@ : TM := fun q s => match q, s with
@TABLE@ end.
Local Notation tm := tm_@ID@.

(** The virtual anchors.  [pexp p = Some 0] (that is, [p = 1]) is excluded by
    the [S _] pattern, so [Cc 1] is an ordinary frame anchor and the overflow
    glue holds at it too. *)
Definition virt_@ID@ (p : positive) : bool :=
  match pexp p with Some (S _) => @VSEL@ | _ => false end.
Local Notation virt := virt_@ID@.

Definition frm_@ID@ (p : positive) : list Sym :=
  if podd p then @FAR1C@ else @FAR0C@.
Local Notation frm := frm_@ID@.

Definition frmv_@ID@ (p : positive) : list Sym :=
  if podd p then @FARV1C@ else @FARV0C@.
Local Notation frmv := frmv_@ID@.

Definition Cc_@ID@ (p : positive) : cconf :=
  if virt_@ID@ p then (@STVN@, (@ENCF@ p ++ @TAIL@, S0, frmv_@ID@ p))
  else (@STFN@, (@ENCF@ p ++ @TAIL@, S0, frm_@ID@ p)).
Local Notation Cc := Cc_@ID@.

@CINDEFS@
Ltac rshape_@ID@ :=
  cbn [rep app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r;
  reflexivity.

(** ** The certificate *)

@INTDEFS@Definition B01_@ID@ : sconf := @B01@.
Definition B11_@ID@ : sconf := @B11@.
Definition cho1_@ID@ : list lstep := @CHO1@.

Lemma run_ovf1_@ID@ : srun tm true true cho1_@ID@ B01_@ID@ = Some (B11_@ID@, @CAO1@, @CBO1@).
Proof. vm_compute. reflexivity. Qed.

Definition B00_@ID@ : sconf := @B00@.
Definition B10_@ID@ : sconf := @B10@.
Definition cho0_@ID@ : list lstep := @CHO0@.

Lemma run_ovf0_@ID@ : srun tm true true cho0_@ID@ B00_@ID@ = Some (B10_@ID@, @CAO0@, @CBO0@).
Proof. vm_compute. reflexivity. Qed.

@VIRTDEFS@
(** ** Anchor glue -- the only per-machine mathematics *)

Lemma epow_@ID@ : forall n, @ENCF@ (pow2 n) = rep @UD@ n ++ @SOD@.
Proof. induction n; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

@IEPOWS@
Lemma hsucc0_@ID@ : forall p j q0, cview p = (j, Some q0) ->
  virt (Pos.succ p) = false.
Proof.
  intros p j q0 E. unfold virt_@ID@.
  rewrite (pexp_succ_int p j q0 E). reflexivity.
Qed.

Lemma hsuccv_@ID@ : forall p k, pexp p = Some (S k) -> virt (Pos.succ p) = false.
Proof.
  intros p k Hx. unfold virt_@ID@.
  rewrite (pexp_succ_virt p k Hx). reflexivity.
Qed.

Lemma vsome_@ID@ : forall p, virt p = true -> exists k, pexp p = Some (S k).
Proof.
  intros p Hv. unfold virt_@ID@ in Hv.
  destruct (pexp p) as [[|m]|]; try discriminate Hv.
  exists m. reflexivity.
Qed.

@INTGLUE@
(** *** the overflow branch.  A fill anchor is never virtual: above [1] it is
    not a power of two at all, and [1] fails the [S _] pattern. *)
Lemma vfill_@ID@ : forall p j, cview p = (S j, None) -> virt p = false.
Proof.
  intros p j E. unfold virt_@ID@.
  destruct (pexp p) as [[|k]|] eqn:Epx; [reflexivity | | reflexivity].
  exfalso. exact (pexp_not_fill p j k E Epx).
Qed.

@OVFGLUE@
(** ** The register step, one arm per octave parity *)

@VIRTGLUE@
Lemma lapv_@ID@ : forall p k, virt p = true -> pexp p = Some (S k) ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof.
  intros p k Hv Hx. destruct (podd p) eqn:Hb.
@LAPVCASES@
Qed.

(** ** SkipGlue's hypotheses *)

Lemma hint_@ID@ : forall p j q0, (@P0@ <= p)%positive ->
  cview p = (j, Some q0) -> virt p = false ->
  exists n, 0 < n /\ csteps tm n (Cc p) = Some (Cc (Pos.succ p)).
Proof. intros p j q0 _ E Hv. exact (lapi_@ID@ p j q0 E Hv). Qed.

Lemma hsucc_@ID@ : forall p j q0, cview p = (j, Some q0) ->
  virt p = false -> virt (Pos.succ p) = false.
Proof. intros p j q0 E _. exact (hsucc0_@ID@ p j q0 E). Qed.

Lemma hvlap_@ID@ : forall p, (@P0@ <= p)%positive -> virt p = true ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof.
  intros p _ Hv. destruct (vsome_@ID@ p Hv) as (k & Hx).
  exact (lapv_@ID@ p k Hv Hx).
Qed.

Lemma hvrun_@ID@ : forall p, (@P0@ <= p)%positive -> virt p = true ->
  virt (Pos.succ p) = true -> virt (Pos.succ (Pos.succ p)) = false.
Proof.
  intros p _ V1 V2. exfalso.
  destruct (vsome_@ID@ p V1) as (k & Hx).
  rewrite (hsuccv_@ID@ p k Hx) in V2. discriminate V2.
Qed.

(** ** The lap *)

Lemma lap_@ID@ : forall p, (@P0@ <= p)%positive -> exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p Hp. destruct (cview p) as [j oq] eqn:E; destruct oq as [q0|].
  - destruct (virt p) eqn:V.
    + destruct (vsome_@ID@ p V) as (k & Hx).
      destruct (lapv_@ID@ p k V Hx) as (n & c' & Hn & Hr & Hl).
      exists n, c'. split; [exact Hr | split; [exact Hl | exact Hn]].
    + destruct (lapi_@ID@ p j q0 E V) as (n & Hn & Hr).
      exists n, (Cc (Pos.succ p)).
      split; [exact Hr | split; [reflexivity | exact Hn]].
  - destruct (cview_pos p j E) as (j' & ->).
    destruct (podd p) eqn:Hb.
    + destruct (lapo1_@ID@ p j' E Hb) as (n & Hn & Hr).
      exists n, (Cc (Pos.succ p)).
      split; [exact Hr | split; [reflexivity | exact Hn]].
    + destruct (lapo0_@ID@ p j' E Hb) as (n & Hn & Hr).
      exists n, (Cc (Pos.succ p)).
      split; [exact Hr | split; [reflexivity | exact Hn]].
Qed.

(** ** Bootstrap *)

Lemma boot_@ID@ : exists t0, stepn tm t0 InitES = Some (lift (Cc @P0@)).
Proof.
  exists @BOOT@.
  assert (H : match csteps tm @BOOT@ c0 with
              | Some c => ceqb c (Cc @P0@) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm @BOOT@ c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** ** Visits

    [SkipGlue.vis_via_skip] asks for a witness at EVERY overflow anchor at or
    above [p0], and the overflow anchors alternate frames -- so the witness
    is a prefix of whichever of the two overflow chains that parity uses. *)

Lemma viso1_@ID@ : forall (l : list lstep) (q : St),
  srun_st tm true true l B01_@ID@ = Some q ->
  forall p j, cview p = (S j, None) -> podd p = true ->
  exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros l q Hst p j E Hb.
  apply (vis_of_run tm Cc true true l B01_@ID@ p j [] []);
    [exact Hst | reflexivity | reflexivity | exact (gso1_@ID@ p j E Hb)].
Qed.

Lemma viso0_@ID@ : forall (l : list lstep) (q : St),
  srun_st tm true true l B00_@ID@ = Some q ->
  forall p j, cview p = (S j, None) -> podd p = false ->
  exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros l q Hst p j E Hb.
  apply (vis_of_run tm Cc true true l B00_@ID@ p j [] []);
    [exact Hst | reflexivity | reflexivity | exact (gso0_@ID@ p j E Hb)].
Qed.

Lemma vis_@ID@ : forall p q, (@P0@ <= p)%positive ->
  exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros p q Hp.
  apply (vis_via_skip tm Cc virt @P0@ hint_@ID@ hsucc_@ID@ hvlap_@ID@
           hvrun_@ID@ q); [| exact Hp].
  intros p1 j1 Hp1 E1. destruct (podd p1) eqn:Hb1.
@VISITS1@
@VISITS0@
Qed.

Theorem nqh_@ID@ : NeverQuasiHaltsSt tm.
Proof. apply (glue_neverqh tm Cc @P0@). - exact boot_@ID@. - intros p Hp. apply (lap_@ID@ p Hp). - intros p q Hp. apply (vis_@ID@ p q Hp). Qed.

Theorem nonhalt_@ID@ : NonHalt tm.
Proof. apply never_qh_nonhalt, nqh_@ID@. Qed.
'''

INT_DEFS = r"""Definition A0@B@_@ID@ : sconf := @A0@.
Definition A1@B@_@ID@ : sconf := @A1@.
Definition chi@B@_@ID@ : list lstep := @CHI@.

Lemma run_int@B@_@ID@ : srun tm false true chi@B@_@ID@ A0@B@_@ID@ = Some (A1@B@_@ID@, @CAI@, @CBI@).
Proof. vm_compute. reflexivity. Qed.

"""

INT_GLUE = r"""(** *** the interior branch at octave parity @BV@.  The frame is CONCRETE in
    the chain's own right side: on some machines the head steps onto it. *)
Lemma gsi@B@_@ID@ : forall p j q0, cview p = (j, Some q0) -> virt p = false ->
  podd p = @BV@ -> Cc p = cden (@ENCF@ q0 ++ @TAIL@) [] j A0@B@_@ID@.
Proof.
  intros p j q0 E Hv Hb. unfold Cc_@ID@. rewrite Hv.
  unfold frm_@ID@. rewrite Hb.
  destruct (@ENCM@.@SOME@ p j q0 E) as (H1 & _).
  unfold cden, A0@B@_@ID@; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia. replace (0 * j + 0) with 0 by lia.
  rewrite H1. rshape_@ID@.
Qed.

Lemma gei@B@_@ID@ : forall p j q0, cview p = (j, Some q0) -> virt p = false ->
  podd p = @BV@ ->
  cden (@ENCF@ q0 ++ @TAIL@) [] j A1@B@_@ID@ = Cc (Pos.succ p).
Proof.
  intros p j q0 E Hv Hb. unfold Cc_@ID@.
  rewrite (hsucc0_@ID@ p j q0 E).
  unfold frm_@ID@. rewrite (podd_succ_int p j q0 E), Hb.
  destruct (@ENCM@.@SOME@ p j q0 E) as (_ & H2).
  unfold cden, A1@B@_@ID@; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia. replace (0 * j + 0) with 0 by lia.
  rewrite H2. rshape_@ID@.
Qed.

Lemma lapi@B@_@ID@ : forall p j q0, cview p = (j, Some q0) -> virt p = false ->
  podd p = @BV@ ->
  exists n, 0 < n /\ csteps tm n (Cc p) = Some (Cc (Pos.succ p)).
Proof.
  intros p j q0 E Hv Hb. exists (@CAI@ * j + @CBI@). split; [lia|].
  rewrite (gsi@B@_@ID@ p j q0 E Hv Hb).
  rewrite (srun_sound tm false true chi@B@_@ID@ A0@B@_@ID@ A1@B@_@ID@ @CAI@ @CBI@
             run_int@B@_@ID@ (@ENCF@ q0 ++ @TAIL@) [] j
             ltac:(discriminate) ltac:(reflexivity)).
  f_equal. exact (gei@B@_@ID@ p j q0 E Hv Hb).
Qed.

"""

INT_DISPATCH = r"""Lemma lapi_@ID@ : forall p j q0, cview p = (j, Some q0) -> virt p = false ->
  exists n, 0 < n /\ csteps tm n (Cc p) = Some (Cc (Pos.succ p)).
Proof.
  intros p j q0 E Hv. destruct (podd p) eqn:Hb.
  - exact (lapi1_@ID@ p j q0 E Hv Hb).
  - exact (lapi0_@ID@ p j q0 E Hv Hb).
Qed.

"""

OVF_GLUE = r'''Lemma gso@B@_@ID@ : forall p j, cview p = (S j, None) -> podd p = @BV@ ->
  Cc p = cden [] [] j B0@B@_@ID@.
Proof.
  intros p j E Hb. unfold Cc_@ID@. rewrite (vfill_@ID@ p j E).
  unfold frm_@ID@. rewrite Hb.
  destruct (@ENCM@.@NONE@ p j E) as (H1 & _).
  unfold cden, B0@B@_@ID@; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia. replace (0 * j + 0) with 0 by lia.
  rewrite H1. rshape_@ID@.
Qed.

Lemma geo@B@_@ID@ : forall p j, cview p = (S j, None) -> podd p = @BV@ ->
  cden [] [] j B1@B@_@ID@ = Cc (Pos.succ p).
Proof.
  intros p j E Hb. unfold Cc_@ID@, virt_@ID@, frm_@ID@, frmv_@ID@.
  rewrite (pexp_succ_fill p (S j) E).
  rewrite (podd_succ_fill p j E), Hb. cbn [negb].
  destruct (@ENCM@.@NONE@ p j E) as (_ & H2).
  unfold cden, B1@B@_@ID@; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 1) with (S j) by lia. replace (0 * j + 0) with 0 by lia.
  rewrite H2. rshape_@ID@.
Qed.

Lemma lapo@B@_@ID@ : forall p j, cview p = (S j, None) -> podd p = @BV@ ->
  exists n, 0 < n /\ csteps tm n (Cc p) = Some (Cc (Pos.succ p)).
Proof.
  intros p j E Hb. exists (@CAO@ * j + @CBO@). split; [lia|].
  rewrite (gso@B@_@ID@ p j E Hb).
  rewrite (srun_sound tm true true cho@B@_@ID@ B0@B@_@ID@ B1@B@_@ID@ @CAO@ @CBO@
             run_ovf@B@_@ID@ [] [] j ltac:(reflexivity) ltac:(reflexivity)).
  f_equal. exact (geo@B@_@ID@ p j E Hb).
Qed.
'''

# --- the register arm: the source/landing glue, shared by both kinds ------

VIRT_HEAD = r'''Lemma gsv@B@_@ID@ : forall p k, virt p = true -> pexp p = Some (S k) ->
  podd p = @BV@ -> Cc p = cden [] [] k VS@B@_@ID@.
Proof.
  intros p k Hv Hx Hb. unfold Cc_@ID@, frmv_@ID@. rewrite Hv, Hb.
  rewrite (pexp_some p (S k) Hx), epow_@ID@.
  unfold cden, VS@B@_@ID@; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * k + 0) with k by lia. replace (0 * k + 0) with 0 by lia.
  rshape_@ID@.
Qed.

Lemma gev@B@_@ID@ : forall p k, virt p = true -> pexp p = Some (S k) ->
  podd p = @BV@ -> lift (cden [] [] k VT@B@_@ID@) = lift (Cc (Pos.succ p)).
Proof.
  intros p k Hv Hx Hb. f_equal.
  unfold Cc_@ID@, frm_@ID@. rewrite (hsuccv_@ID@ p k Hx).
  rewrite (podd_succ_pexp p k Hx), Hb.
  rewrite (pexp_some p (S k) Hx).
  cbn [Pos.succ pow2 @ENCF@]. rewrite epow_@ID@.
  unfold cden, VT@B@_@ID@; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * k + 0) with k by lia. replace (0 * k + 0) with 0 by lia.
  rshape_@ID@.
Qed.

'''

VIRT_FLAT_DEFS = r'''(** *** the register step at octave parity @BV@: FLAT *)
Definition VS@B@_@ID@ : sconf := @VS@.
Definition VT@B@_@ID@ : sconf := @VT@.
Definition chv@B@_@ID@ : list lstep := @CHV@.

Lemma run_virt@B@_@ID@ : srun tm true true chv@B@_@ID@ VS@B@_@ID@ = Some (VT@B@_@ID@, @CAV@, @CBV@).
Proof. vm_compute. reflexivity. Qed.

'''

VIRT_FLAT_GLUE = r'''Lemma lapv@B@_@ID@ : forall p k, virt p = true -> pexp p = Some (S k) ->
  podd p = @BV@ ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof.
  intros p k Hv Hx Hb.
  exists (@CAV@ * k + @CBV@), (cden [] [] k VT@B@_@ID@).
  split; [lia|]. split; [| exact (gev@B@_@ID@ p k Hv Hx Hb)].
  rewrite (gsv@B@_@ID@ p k Hv Hx Hb).
  exact (srun_sound tm true true chv@B@_@ID@ VS@B@_@ID@ VT@B@_@ID@ @CAV@ @CBV@
           run_virt@B@_@ID@ [] [] k ltac:(reflexivity) ltac:(reflexivity)).
Qed.

'''

VIRT_NEST_CIN = r'''(** ** The INNER anchor family of the parity-@BV@ register step -- the
    counter that step re-runs *)
Definition Cin@B@_@ID@ (v : positive) : cconf :=
  (@ISTN@, (@IENCF@ v ++ @ITAIL@, S0, @IFAR@)).
Local Notation Cin@B@ := Cin@B@_@ID@.

'''

VIRT_NEST_DEFS = r'''(** *** the register step at octave parity @BV@: boot (from the PEELED
    virtual anchor -- the first move is onto the counter's own top block),
    the inner counter's laps, exit *)
Definition VS@B@_@ID@ : sconf := @VS@.
Definition CS@B@_@ID@ : sconf := @CS@.
Definition chb@B@_@ID@ : list lstep := @CHB@.

Lemma run_boot@B@_@ID@ : srun tm true true chb@B@_@ID@ VS@B@_@ID@ = Some (CS@B@_@ID@, @CAB@, @CBB@).
Proof. vm_compute. reflexivity. Qed.

Definition AI0@B@_@ID@ : sconf := @AI0@.
Definition AI1@B@_@ID@ : sconf := @AI1@.
Definition chn@B@_@ID@ : list lstep := @CHN@.

Lemma run_inner@B@_@ID@ : srun tm false true chn@B@_@ID@ AI0@B@_@ID@ = Some (AI1@B@_@ID@, @CAN@, @CBN@).
Proof. vm_compute. reflexivity. Qed.

Definition CF@B@_@ID@ : sconf := @CF@.
Definition VT@B@_@ID@ : sconf := @VT@.
Definition che@B@_@ID@ : list lstep := @CHE@.

Lemma run_exit@B@_@ID@ : srun tm true true che@B@_@ID@ CF@B@_@ID@ = Some (VT@B@_@ID@, @CAE@, @CBE@).
Proof. vm_compute. reflexivity. Qed.

'''

VIRT_NEST_GLUE = r'''Lemma gsn@B@_@ID@ : forall v i q0, cview v = (i, Some q0) ->
  Cin@B@ v = cden (@IENCF@ q0 ++ @ITAIL@) [] i AI0@B@_@ID@.
Proof.
  intros v i q0 E. destruct (@IENCM@.@ISOME@ v i q0 E) as (H1 & _).
  unfold Cin@B@_@ID@, cden, AI0@B@_@ID@; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia. replace (0 * i + 0) with 0 by lia.
  rewrite H1. rshape_@ID@.
Qed.

Lemma gen@B@_@ID@ : forall v i q0, cview v = (i, Some q0) ->
  cden (@IENCF@ q0 ++ @ITAIL@) [] i AI1@B@_@ID@ = Cin@B@ (Pos.succ v).
Proof.
  intros v i q0 E. destruct (@IENCM@.@ISOME@ v i q0 E) as (_ & H2).
  unfold Cin@B@_@ID@, cden, AI1@B@_@ID@; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia. replace (0 * i + 0) with 0 by lia.
  rewrite H2. rshape_@ID@.
Qed.

Lemma lapin@B@_@ID@ : forall v i q0, cview v = (i, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cin@B@ v) = Some c'
               /\ lift c' = lift (Cin@B@ (Pos.succ v)).
Proof.
  intros v i q0 E.
  exists (@CAN@ * i + @CBN@), (Cin@B@ (Pos.succ v)).
  split; [lia|]. split; [| reflexivity].
  rewrite (gsn@B@_@ID@ v i q0 E).
  rewrite (srun_sound tm false true chn@B@_@ID@ AI0@B@_@ID@ AI1@B@_@ID@ @CAN@ @CBN@
             run_inner@B@_@ID@ (@IENCF@ q0 ++ @ITAIL@) [] i
             ltac:(discriminate) ltac:(reflexivity)).
  f_equal. exact (gen@B@_@ID@ v i q0 E).
Qed.

Lemma gbo@B@_@ID@ : forall k, lift (cden [] [] k CS@B@_@ID@) = lift (Cin@B@ (pow2 k)).
Proof.
  intro k. f_equal.
  unfold Cin@B@_@ID@, cden, CS@B@_@ID@; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * k + 0) with k by lia. replace (0 * k + 0) with 0 by lia.
  rewrite @IEPOW@. rshape_@ID@.
Qed.

Lemma gxi@B@_@ID@ : forall k, Cin@B@ (fill (pow2 k)) = cden [] [] k CF@B@_@ID@.
Proof.
  intro k.
  destruct (@IENCM@.@INONE@ (fill (pow2 k)) k (cview_fill_pow2 k)) as (H1 & _).
  unfold Cin@B@_@ID@, cden, CF@B@_@ID@; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * k + 0) with k by lia. replace (0 * k + 0) with 0 by lia.
  rewrite H1. rshape_@ID@.
Qed.

Lemma hbo@B@_@ID@ : forall p k, virt p = true -> pexp p = Some (S k) ->
  podd p = @BV@ ->
  exists n c, 0 < n /\ csteps tm n (Cc p) = Some c
              /\ lift c = lift (Cin@B@ (pow2 k)).
Proof.
  intros p k Hv Hx Hb.
  exists (@CAB@ * k + @CBB@), (cden [] [] k CS@B@_@ID@).
  split; [lia|]. split; [| exact (gbo@B@_@ID@ k)].
  rewrite (gsv@B@_@ID@ p k Hv Hx Hb).
  exact (srun_sound tm true true chb@B@_@ID@ VS@B@_@ID@ CS@B@_@ID@ @CAB@ @CBB@
           run_boot@B@_@ID@ [] [] k ltac:(reflexivity) ltac:(reflexivity)).
Qed.

Lemma hxe@B@_@ID@ : forall p k, virt p = true -> pexp p = Some (S k) ->
  podd p = @BV@ ->
  exists n c', csteps tm n (Cin@B@ (fill (pow2 k))) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof.
  intros p k Hv Hx Hb.
  exists (@CAE@ * k + @CBE@), (cden [] [] k VT@B@_@ID@).
  split; [| exact (gev@B@_@ID@ p k Hv Hx Hb)].
  rewrite (gxi@B@_@ID@ k).
  exact (srun_sound tm true true che@B@_@ID@ CF@B@_@ID@ VT@B@_@ID@ @CAE@ @CBE@
           run_exit@B@_@ID@ [] [] k ltac:(reflexivity) ltac:(reflexivity)).
Qed.

(** The register step, composed.  The [Theta(2^k)] middle is the [exists n]
    inside [NestedLapLift.inner_to_fill_lift]; no formula for it is written. *)
Lemma lapv@B@_@ID@ : forall p k, virt p = true -> pexp p = Some (S k) ->
  podd p = @BV@ ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof.
  intros p k Hv Hx Hb.
  destruct (nested_overflow_lift tm Cc Cin@B@ lapin@B@_@ID@ p (pow2 k)
              (hbo@B@_@ID@ p k Hv Hx Hb) (hxe@B@_@ID@ p k Hv Hx Hb))
    as (n & c' & Hr & Hl & Hn).
  exists n, c'. split; [exact Hn | split; [exact Hr | exact Hl]].
Qed.

'''


def _far(fs):
    return clist(fs)


def _arm_reps(D, V, b, ID, di=None):
    """The per-parity substitutions of one register arm."""
    reps = {'@B@': str(b), '@BV@': 'true' if b else 'false',
            '@VT@': EL.cconf(V['T']), '@VS@': EL.cconf(V['VS'])}
    if V['kind'] == 'flat':
        reps.update({'@CHV@': EL.cchain(V['ch']),
                     '@CAV@': str(V['c'][0]), '@CBV@': str(V['c'][1])})
    else:
        iencf = di.get('fn') or V['key'][0]
        reps.update({
            '@CS@': EL.cconf(V['CinS']), '@CF@': EL.cconf(V['CinF']),
            '@AI0@': EL.cconf(V['AI0']), '@AI1@': EL.cconf(V['AI1']),
            '@CHB@': EL.cchain(V['chb']), '@CHN@': EL.cchain(V['chn']),
            '@CHE@': EL.cchain(V['che']),
            '@CAB@': str(V['cb'][0]), '@CBB@': str(V['cb'][1]),
            '@CAN@': str(V['cn'][0]), '@CBN@': str(V['cn'][1]),
            '@CAE@': str(V['ce'][0]), '@CBE@': str(V['ce'][1]),
            '@IENCF@': iencf, '@IENCM@': di['mod'],
            '@ISOME@': di['some'], '@INONE@': di['none'],
            '@ITAIL@': clist(V['key'][2]), '@IFAR@': clist(V['key'][3]),
            '@ISTN@': ST[V['key'][1]],
            '@IEPOW@': 'iepow%d_%s' % (b, ID),
            '@IUD@': clist(di['uD']), '@ISOD@': clist(di['soD']),
        })
    return reps


def _fill(tpl, reps):
    out = tpl
    for _ in range(3):
        for k, v in reps.items():
            out = out.replace(k, v)
    return out


IEPOW = ('Lemma iepow@B@_@ID@ : forall n, @IENCF@ (pow2 n) = rep @IUD@ n ++ @ISOD@.\n'
         'Proof. induction n; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.\n\n')


def render(D):
    spec = D['spec']
    ID = mach_id(spec)
    d = ENCDATA[D['enc']]
    encf = d.get('fn') or D['enc']
    mods = []
    for m in [d['mod']] + [ENCDATA[V['key'][0]]['mod']
                           for V in D['vlap'].values()
                           if V['kind'] == 'nested']:
        if m not in mods and m not in ('JpCounter', 'MonoCounter', 'WTape'):
            mods.append(m)

    idefs, iglue = [], []
    for b in (1, 0):
        I = D['ints'][b]
        r = {'@B@': str(b), '@BV@': 'true' if b else 'false',
             '@A0@': EL.cconf(I['A0']), '@A1@': EL.cconf(I['A1']),
             '@CHI@': EL.cchain(I['ch']),
             '@CAI@': str(I['c'][0]), '@CBI@': str(I['c'][1])}
        idefs.append(_fill(INT_DEFS, r))
        iglue.append(_fill(INT_GLUE, r))
    iglue.append(INT_DISPATCH)

    ovf = []
    for b in (1, 0):
        O = D['ovf'][b]
        ovf.append(_fill(OVF_GLUE,
                         {'@B@': str(b), '@BV@': 'true' if b else 'false',
                          '@CAO@': str(O['c'][0]), '@CBO@': str(O['c'][1])}))

    cindefs, vdefs, vglue, iepows, lapvcases, vdesc = [], [], [], [], [], []
    for b in (1, 0):
        V = D['vlap'].get(b)
        if V is None:
            lapvcases.append(
                '  - exfalso. unfold virt_@ID@ in Hv. rewrite Hx, Hb in Hv.\n'
                '    discriminate Hv.')
            continue
        di = ENCDATA[V['key'][0]] if V['kind'] == 'nested' else None
        reps = _arm_reps(D, V, b, ID, di)
        if V['kind'] == 'flat':
            vdefs.append(_fill(VIRT_FLAT_DEFS, reps))
            vglue.append(_fill(VIRT_HEAD + VIRT_FLAT_GLUE, reps))
            vdesc.append('parity %s FLAT, %d*k+%d steps'
                         % (reps['@BV@'], V['c'][0], V['c'][1]))
        else:
            cindefs.append(_fill(VIRT_NEST_CIN, reps))
            vdefs.append(_fill(VIRT_NEST_DEFS, reps))
            vglue.append(_fill(VIRT_HEAD + VIRT_NEST_GLUE, reps))
            iepows.append(_fill(IEPOW, reps))
            vdesc.append('parity %s NESTED, boot %d*k+%d then the inner '
                         'counter then exit %d*k+%d'
                         % (reps['@BV@'], V['cb'][0], V['cb'][1],
                            V['ce'][0], V['ce'][1]))
        lapvcases.append('  - exact (lapv%d_@ID@ p k Hv Hx Hb).' % b)

    vis = []
    for b in (1, 0):
        blk = ['  - destruct q.']
        for q in range(4):
            blk.append('    + exact (viso%d_%s %s %s '
                       'ltac:(vm_compute; reflexivity) p1 j1 E1 Hb1).'
                       % (b, ID, EL.cchain(D['vis'][q][b]), ST[q]))
        vis.append('\n'.join(blk))

    reps = {
        '@ID@': ID, '@SPEC@': spec, '@TABLE@': coq_table(spec),
        '@MODS@': ' '.join(mods),
        '@ENCF@': encf, '@ENCM@': d['mod'],
        '@SOME@': d['some'], '@NONE@': d['none'],
        '@UD@': clist(d['uD']), '@SOD@': clist(d['soD']),
        '@TAIL@': clist(D['tail']),
        '@STFN@': ST[D['st_f']], '@STVN@': ST[D['st_v']],
        '@FARV1C@': _far(D['fparv'][1]), '@FARV0C@': _far(D['fparv'][0]),
        '@FAR1C@': _far(D['fpar'][1]), '@FAR0C@': _far(D['fpar'][0]),
        '@VSEL@': D['vsel'],
        '@P0@': str(D['p0']), '@BOOT@': str(D['boot']),
        '@INTDEFS@': ''.join(idefs), '@INTGLUE@': ''.join(iglue),
        '@B01@': EL.cconf(D['ovf'][1]['B0']),
        '@B11@': EL.cconf(D['ovf'][1]['B1']),
        '@CHO1@': EL.cchain(D['ovf'][1]['ch']),
        '@CAO1@': str(D['ovf'][1]['c'][0]), '@CBO1@': str(D['ovf'][1]['c'][1]),
        '@B00@': EL.cconf(D['ovf'][0]['B0']),
        '@B10@': EL.cconf(D['ovf'][0]['B1']),
        '@CHO0@': EL.cchain(D['ovf'][0]['ch']),
        '@CAO0@': str(D['ovf'][0]['c'][0]), '@CBO0@': str(D['ovf'][0]['c'][1]),
        '@CINDEFS@': ''.join(cindefs),
        '@VIRTDEFS@': ''.join(vdefs),
        '@VIRTGLUE@': ''.join(vglue),
        '@IEPOWS@': ''.join(iepows),
        '@LAPVCASES@': '\n'.join(lapvcases),
        '@OVFGLUE@': '\n'.join(ovf),
        '@VISITS1@': vis[0], '@VISITS0@': vis[1],
        '@CI@': '%d*j+%d / %d*j+%d by parity'
                % (D['ints'][1]['c'] + D['ints'][0]['c']),
        '@CO1@': '%d*j+%d' % D['ovf'][1]['c'],
        '@CO0@': '%d*j+%d' % D['ovf'][0]['c'],
        '@VDESC@': '; '.join(vdesc),
        '@VAL@': D['val'],
    }
    out = BOARD
    for _ in range(3):
        for k, v in reps.items():
            out = out.replace(k, v)
    return out


# --------------------------------------------------------------- process ---

def process(spec, enc, tail, mirrored, do_emit, force=False):
    D = derive(spec, enc, tuple(tail), mirrored)
    if not do_emit:
        return dict(spec=spec, ok=True, enc=enc, p0=D['p0'], val=D['val'])
    path = os.path.join(OUTDIR, '%s_%s.v' % (PREFIX, mach_id(spec)))
    if os.path.exists(path) and not force:
        return dict(spec=spec, ok=True, enc=enc, file=path, skipped=True,
                    val=D['val'])
    src = render(D)
    if mirrored:
        src = mirrorize(src, spec, D['spec'])
    open(path, 'w').write(src)
    ok, log = coqc(os.path.relpath(path, REPO))
    if not ok:
        os.remove(path)
        lg = [l for l in log.strip().splitlines() if l.strip()]
        raise RegError('coqc: ' + '\n'.join(lg[-6:]))
    return dict(spec=spec, ok=True, enc=enc, file=path, val=D['val'])


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--json')
    ap.add_argument('--kind')
    ap.add_argument('--spec')
    ap.add_argument('--enc')
    ap.add_argument('--tail')
    ap.add_argument('--mirror', action='store_true')
    ap.add_argument('--emit', action='store_true')
    ap.add_argument('--force', action='store_true')
    ap.add_argument('--out')
    ap.add_argument('--frames', action='store_true',
                    help='the TWO-FORM read: per-octave frames with full '
                         'coverage, and the period-1/2 pick')
    a = ap.parse_args()
    if a.frames:
        rows = ([r for r in json.load(open(a.json))
                 if not a.kind or r['kind'] == a.kind] if a.json else
                [dict(spec=a.spec, enc=a.enc, mirror=a.mirror,
                      tail=json.loads(a.tail) if a.tail else [])])
        for r in rows:
            ds = mirror_spec(r['spec']) if r['mirror'] else r['spec']
            try:
                fr, _ = frame_probe(ds, r['enc'], tuple(r['tail']))
                P, pick, ks = frames_of_probe(fr)
                print('%-40s period-%d  %s' % (
                    r['spec'], P,
                    ' | '.join('%d:%s@%s' % (k, LAB[pick[k][0]],
                                             ''.join(map(str, pick[k][1]))
                                             or '-') for k in ks)))
            except Exception as e:                             # noqa: BLE001
                print('%-40s %s: %s' % (r['spec'], type(e).__name__, e))
        return
    if a.json:
        rows = [r for r in json.load(open(a.json))
                if not a.kind or r['kind'] == a.kind]
    else:
        rows = [dict(spec=a.spec, enc=a.enc, mirror=a.mirror,
                     tail=json.loads(a.tail) if a.tail else [])]
    res, nok = [], 0
    for i, r in enumerate(rows):
        try:
            got = process(r['spec'], r['enc'], r['tail'], r['mirror'],
                          a.emit, a.force)
        except Exception as e:                                 # noqa: BLE001
            got = dict(spec=r['spec'], ok=False,
                       why='%s: %s' % (type(e).__name__, e))
        res.append(got)
        nok += bool(got['ok'])
        print('%4d/%d %-40s %s' % (
            i + 1, len(rows), r['spec'],
            ('OK %s' % got.get('val', '')) if got['ok']
            else 'no: %s' % got['why'][:200]), flush=True)
    print('\n%d / %d boarded' % (nok, len(rows)))
    if a.out:
        json.dump(res, open(a.out, 'w'), indent=1)


if __name__ == '__main__':
    main()
