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


def frame_law(byoct, virt, ks):
    """(period, forms, virtual residue).  Only P = 1 and P = 2 are wired."""
    for P in (1, 2):
        forms = [byoct[k] for k in ks[:P]]
        if not all(byoct[k] == forms[(k - ks[0]) % P] for k in ks):
            continue
        if not virt:
            vres = None
        else:
            vres = virt[0] % 2 if P == 2 else 0
            bad = [k for k in ks if (k in virt) !=
                   ((k % 2 == vres) if P == 2 else True)]
            if bad:
                continue
        return P, forms, vres
    raise RegError('frame law is not period 1 or 2')


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
    P, forms, vres = frame_law(byoct, virt, ks)
    if not virt:
        raise RegError('no virtual anchor: the flat/nested route applies')
    st_f = forms[0][0]
    if any(f[0] != st_f for f in forms):
        raise RegError('frame STATE varies by octave; not wired')
    st_v, far_v = atpow[virt[0]]
    if any(atpow[k] != (st_v, far_v) for k in virt):
        raise RegError('virtual frame varies by octave')
    # forms indexed by octave parity: fpar[b] is the far side at octaves
    # whose parity is b.  [podd p = true] iff the octave is odd.
    if P == 1:
        fpar = {0: forms[0][1], 1: forms[0][1]}
    else:
        fpar = {ks[0] % 2: forms[0][1], (ks[0] + 1) % 2: forms[1][1]}
    p0 = 1 << ks[0]

    # ---- the interior lap: ONE chain, the frame carried as the RIGHT
    # opaque tail, so both parities go through it.
    A0 = (st_f, ((), uS, 1, 0, sS), 0, F(()))
    A1 = (st_f, ((), uD, 1, 0, sD), 0, F(()))
    chi, ri = _chain(tab, False, False, A0, A1)
    if chi is None or ri[0] != A1:
        raise RegError('no interior chain (frame-opaque)')
    if ri[2] == 0:
        raise RegError('interior lap of zero length at j=0')

    # ---- the overflow laps, one per octave parity.  The target at
    # 2^(S j) is the VIRTUAL anchor when (S j) is a virtual octave and the
    # next octave's ordinary frame otherwise.
    VIRTC = (st_v, ((), uD, 1, 1, soD + tail), 0, F(far_v))
    ovf = {}
    for b in (0, 1):
        B0 = (st_f, ((), uS, 1, 0, soS + tail), 0, F(fpar[b]))
        tgt_virt = (P == 2 and vres == (1 - b)) or (P == 1)
        if tgt_virt:
            B1 = VIRTC
        else:
            B1 = (st_f, ((), uD, 1, 1, soD + tail), 0, F(fpar[1 - b]))
        ch, r = _chain(tab, True, True, B0, B1)
        if ch is None or r[0] != B1:
            raise RegError('no overflow chain at octave parity %d' % b)
        ovf[b] = dict(B0=B0, B1=B1, ch=ch, c=(r[1], r[2]), virt=tgt_virt)
        if P == 1:
            ovf[1] = ovf[0]
            break

    # ---- the register step: out of the virtual anchor, into the octave's
    # own frame.  Flat first, then the nested composition.
    vb = virt[0] % 2 if P == 2 else virt[0] % 1
    VP = (st_v, (uD, uD, 1, 0, soD + tail), 0, F(far_v))
    VT = (st_f, (uS, uD, 1, 0, soD + tail), 0, F(fpar[vb]))
    chv, rv = _chain(tab, True, True, VIRTC, VT)
    nest = None
    if chv is not None and rv[0] == VT:
        vlap = dict(kind='flat', ch=chv, c=(rv[1], rv[2]), T=VT)
    else:
        K = max(k for k in virt if k <= 6)
        p = 1 << K
        if p not in cfgs or (p + 1) not in cfgs:
            raise RegError('walk does not reach the virtual anchor 2^%d' % K)
        nx = cfgs[p + 1]
        want = (nx[0], tuple(ENC[enc](p + 1)) + tail, LC.rstrip0(nx[3]))
        mid = _phase(tab, cfgs[p], want)
        nest = _nested(tab, enc, st_f, tail, VP, VT, mid, K)
        vlap = dict(kind='nested', T=VT, VP=VP, **nest)

    D = dict(spec=dspec, orig=spec, mirror=mirrored, enc=enc,
             tail=list(tail), st_f=st_f, st_v=st_v, far_v=list(far_v),
             fpar={b: list(fpar[b]) for b in (0, 1)}, P=P, vres=vres,
             virt=virt, ks=ks, p0=p0, A0=A0, A1=A1, chi=chi,
             ci=(ri[1], ri[2]), VIRTC=VIRTC, ovf=ovf, vlap=vlap)
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
                tuple(D['far_v']))
    return (D['st_f'], tuple(encf(p)) + tuple(D['tail']), 0,
            tuple(D['fpar'][k % 2]))


def validate(tab, D, cfgs, hi=HI):
    """Replay EVERY branch against the raw simulator: exact step counts,
    exact configurations, [lift]-equal landings, and -- on the register
    step -- every inner lap of the inner counter."""
    encf = ENC[D['enc']]
    n, ninner = 0, 0
    for p in range(D['p0'], hi):
        k = octave(p)
        if k > D['ks'][-1]:
            break
        start = _anchor(D, encf, p)
        want = _anchor(D, encf, p + 1)
        if k in D['virt'] and p == (1 << k):
            V = D['vlap']
            if V['kind'] == 'flat':
                steps = V['c'][0] * (k - 1) + V['c'][1]
            else:
                # boot + the inner counter's own laps + exit
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
                    s = V['cn'][0] * i + V['cn'][1]
                    cur = EL.sim(tab, cur, s)
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
                steps = D['ci'][0] * j + D['ci'][1]
        got = EL.sim(tab, start, steps)
        if not EL.eqlift(got, want):
            raise RegError('p=%d branch: %d steps -> %r want %r' %
                           (p, steps, got, want))
        n += 1
    return '%d anchors, %d register steps, %d inner laps' % (
        n, len([k for k in D['virt'] if (1 << k) < hi]), ninner)


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
    OCTAVE: the machine keeps a one-cell REGISTER past the head and moves it
    once per octave, so the family is (register state x counter) and the
    anchor is piecewise (WAVE28 section 3c, `period-2+virt`).

      Cc p = if virt p then (@STVN@, E p ++ tail, S0, @FARVC@)
             else (@STFN@, E p ++ tail, S0, if podd p then @FAR1C@ else @FAR0C@)

    [RegGlue.podd] is the octave parity ([podd p = true] iff the octave is
    odd); [virt p] holds at the powers of two the machine rests at in a
    DIFFERENT frame from their own octave's -- the SKIP route's virtual
    anchor, one dimension up.  Four lap branches, and they are NOT four
    ordinary chains:

      interior  (virt p = false, cview p = (j, Some q0)):  @CI@ steps, exact,
                the frame carried as the RIGHT OPAQUE TAIL so ONE chain
                covers both octave parities
      overflow  (cview p = (S j, None)), one chain per parity:
                podd p = true:  @CO1@ steps   podd p = false: @CO0@ steps
      register  (virt p = true): boot @CB@, then the INNER counter's own laps
                to its all-ones fill, then exit @CE@ -- [Theta(2^k)], and the
                exponent is never written down
                ([Counters/NestedLapLift.nested_overflow_lift]).

    The register step is the whole point: the mark cannot be moved without a
    pass that COUNTS, so a nested branch sits inside a piecewise [Cc].
    [Counters/SkipGlue.v] fences the virtual anchors ([reach_ovf_skip] /
    [vis_via_skip], the interior-lap hypothesis GUARDED by "not virtual"),
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

(** The virtual anchors: the powers of two whose octave parity is the one
    the machine rests at in its transient frame.  [pexp p = Some 0] (that
    is, [p = 1]) is excluded by the [S _] pattern, so [Cc 1] is an ordinary
    frame anchor and the overflow glue holds at it too. *)
Definition virt_@ID@ (p : positive) : bool :=
  match pexp p with Some (S _) => @VSEL@ | _ => false end.
Local Notation virt := virt_@ID@.

Definition frm_@ID@ (p : positive) : list Sym :=
  if podd p then @FAR1C@ else @FAR0C@.
Local Notation frm := frm_@ID@.

Definition Cc_@ID@ (p : positive) : cconf :=
  if virt_@ID@ p then (@STVN@, (@ENCF@ p ++ @TAIL@, S0, @FARVC@))
  else (@STFN@, (@ENCF@ p ++ @TAIL@, S0, frm_@ID@ p)).
Local Notation Cc := Cc_@ID@.

(** ** The INNER anchor family -- the counter the register step re-runs *)
Definition Cin_@ID@ (v : positive) : cconf :=
  (@ISTN@, (@IENCF@ v ++ @ITAIL@, S0, @IFAR@)).
Local Notation Cin := Cin_@ID@.

Ltac rshape_@ID@ :=
  cbn [rep app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r;
  reflexivity.

(** ** The certificate *)

Definition A0_@ID@ : sconf := @A0@.
Definition A1_@ID@ : sconf := @A1@.
Definition chi_@ID@ : list lstep := @CHI@.

Lemma run_int_@ID@ : srun tm false false chi_@ID@ A0_@ID@ = Some (A1_@ID@, @CAI@, @CBI@).
Proof. vm_compute. reflexivity. Qed.

Definition B01_@ID@ : sconf := @B01@.
Definition B11_@ID@ : sconf := @B11@.
Definition cho1_@ID@ : list lstep := @CHO1@.

Lemma run_ovf1_@ID@ : srun tm true true cho1_@ID@ B01_@ID@ = Some (B11_@ID@, @CAO1@, @CBO1@).
Proof. vm_compute. reflexivity. Qed.

Definition B00_@ID@ : sconf := @B00@.
Definition B10_@ID@ : sconf := @B10@.
Definition cho0_@ID@ : list lstep := @CHO0@.

Lemma run_ovf0_@ID@ : srun tm true true cho0_@ID@ B00_@ID@ = Some (B10_@ID@, @CAO0@, @CBO0@).
Proof. vm_compute. reflexivity. Qed.

(** *** the register step: boot (from the PEELED virtual anchor -- the first
    move is onto the counter's own top block), inner laps, exit *)
Definition VP_@ID@ : sconf := @VP@.
Definition CS_@ID@ : sconf := @CS@.
Definition chb_@ID@ : list lstep := @CHB@.

Lemma run_boot_@ID@ : srun tm true true chb_@ID@ VP_@ID@ = Some (CS_@ID@, @CAB@, @CBB@).
Proof. vm_compute. reflexivity. Qed.

Definition AI0_@ID@ : sconf := @AI0@.
Definition AI1_@ID@ : sconf := @AI1@.
Definition chn_@ID@ : list lstep := @CHN@.

Lemma run_inner_@ID@ : srun tm false true chn_@ID@ AI0_@ID@ = Some (AI1_@ID@, @CAN@, @CBN@).
Proof. vm_compute. reflexivity. Qed.

Definition CF_@ID@ : sconf := @CF@.
Definition VT_@ID@ : sconf := @VT@.
Definition che_@ID@ : list lstep := @CHE@.

Lemma run_exit_@ID@ : srun tm true true che_@ID@ CF_@ID@ = Some (VT_@ID@, @CAE@, @CBE@).
Proof. vm_compute. reflexivity. Qed.

(** ** Anchor glue -- the only per-machine mathematics *)

Lemma epow_@ID@ : forall n, @ENCF@ (pow2 n) = rep @UD@ n ++ @SOD@.
Proof. induction n; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

Lemma iepow_@ID@ : forall n, @IENCF@ (pow2 n) = rep @IUD@ n ++ @ISOD@.
Proof. induction n; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

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

(** *** the interior branch.  The frame is the RIGHT OPAQUE TAIL, so the one
    chain speaks at both octave parities at once. *)
Lemma gsi_@ID@ : forall p j q0, cview p = (j, Some q0) -> virt p = false ->
  Cc p = cden (@ENCF@ q0 ++ @TAIL@) (frm p) j A0_@ID@.
Proof.
  intros p j q0 E Hv. unfold Cc_@ID@. rewrite Hv.
  destruct (@ENCM@.@SOME@ p j q0 E) as (H1 & _).
  unfold cden, A0_@ID@; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia. replace (0 * j + 0) with 0 by lia.
  rewrite H1. rshape_@ID@.
Qed.

Lemma gei_@ID@ : forall p j q0, cview p = (j, Some q0) -> virt p = false ->
  cden (@ENCF@ q0 ++ @TAIL@) (frm p) j A1_@ID@ = Cc (Pos.succ p).
Proof.
  intros p j q0 E Hv. unfold Cc_@ID@.
  rewrite (hsucc0_@ID@ p j q0 E).
  unfold frm_@ID@. rewrite (podd_succ_int p j q0 E).
  destruct (@ENCM@.@SOME@ p j q0 E) as (_ & H2).
  unfold cden, A1_@ID@; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia. replace (0 * j + 0) with 0 by lia.
  rewrite H2. rshape_@ID@.
Qed.

Lemma lapi_@ID@ : forall p j q0, cview p = (j, Some q0) -> virt p = false ->
  exists n, 0 < n /\ csteps tm n (Cc p) = Some (Cc (Pos.succ p)).
Proof.
  intros p j q0 E Hv. exists (@CAI@ * j + @CBI@). split; [lia|].
  rewrite (gsi_@ID@ p j q0 E Hv).
  rewrite (srun_sound tm false false chi_@ID@ A0_@ID@ A1_@ID@ @CAI@ @CBI@
             run_int_@ID@ (@ENCF@ q0 ++ @TAIL@) (frm p) j
             ltac:(discriminate) ltac:(discriminate)).
  f_equal. exact (gei_@ID@ p j q0 E Hv).
Qed.

(** *** the overflow branch.  A fill anchor is never virtual: above [1] it is
    not a power of two at all, and [1] fails the [S _] pattern. *)
Lemma vfill_@ID@ : forall p j, cview p = (S j, None) -> virt p = false.
Proof.
  intros p j E. unfold virt_@ID@.
  destruct (pexp p) as [[|k]|] eqn:Epx; [reflexivity | | reflexivity].
  exfalso. exact (pexp_not_fill p j k E Epx).
Qed.

@OVFGLUE@

(** *** the register step *)

Lemma vpar_@ID@ : forall p k, virt p = true -> pexp p = Some (S k) ->
  podd p = @VPARV@.
Proof.
  intros p k Hv Hx. unfold virt_@ID@ in Hv. rewrite Hx in Hv.
  destruct (podd p); @VPARD@.
Qed.

Lemma gsv_@ID@ : forall p k, virt p = true -> pexp p = Some (S k) ->
  Cc p = cden [] [] k VP_@ID@.
Proof.
  intros p k Hv Hx. unfold Cc_@ID@. rewrite Hv.
  rewrite (pexp_some p (S k) Hx), epow_@ID@.
  unfold cden, VP_@ID@; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * k + 0) with k by lia. replace (0 * k + 0) with 0 by lia.
  rshape_@ID@.
Qed.

Lemma gsn_@ID@ : forall v i q0, cview v = (i, Some q0) ->
  Cin v = cden (@IENCF@ q0 ++ @ITAIL@) [] i AI0_@ID@.
Proof.
  intros v i q0 E. destruct (@IENCM@.@ISOME@ v i q0 E) as (H1 & _).
  unfold Cin_@ID@, cden, AI0_@ID@; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia. replace (0 * i + 0) with 0 by lia.
  rewrite H1. rshape_@ID@.
Qed.

Lemma gen_@ID@ : forall v i q0, cview v = (i, Some q0) ->
  cden (@IENCF@ q0 ++ @ITAIL@) [] i AI1_@ID@ = Cin (Pos.succ v).
Proof.
  intros v i q0 E. destruct (@IENCM@.@ISOME@ v i q0 E) as (_ & H2).
  unfold Cin_@ID@, cden, AI1_@ID@; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia. replace (0 * i + 0) with 0 by lia.
  rewrite H2. rshape_@ID@.
Qed.

Lemma lapin_@ID@ : forall v i q0, cview v = (i, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cin v) = Some c'
               /\ lift c' = lift (Cin (Pos.succ v)).
Proof.
  intros v i q0 E.
  exists (@CAN@ * i + @CBN@), (Cin (Pos.succ v)).
  split; [lia|]. split; [| reflexivity].
  rewrite (gsn_@ID@ v i q0 E).
  rewrite (srun_sound tm false true chn_@ID@ AI0_@ID@ AI1_@ID@ @CAN@ @CBN@
             run_inner_@ID@ (@IENCF@ q0 ++ @ITAIL@) [] i
             ltac:(discriminate) ltac:(reflexivity)).
  f_equal. exact (gen_@ID@ v i q0 E).
Qed.

Lemma gbo_@ID@ : forall k, lift (cden [] [] k CS_@ID@) = lift (Cin (pow2 k)).
Proof.
  intro k. f_equal.
  unfold Cin_@ID@, cden, CS_@ID@; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * k + 0) with k by lia. replace (0 * k + 0) with 0 by lia.
  rewrite iepow_@ID@. rshape_@ID@.
Qed.

Lemma gxi_@ID@ : forall k, Cin (fill (pow2 k)) = cden [] [] k CF_@ID@.
Proof.
  intro k.
  destruct (@IENCM@.@INONE@ (fill (pow2 k)) k (cview_fill_pow2 k)) as (H1 & _).
  unfold Cin_@ID@, cden, CF_@ID@; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * k + 0) with k by lia. replace (0 * k + 0) with 0 by lia.
  rewrite H1. rshape_@ID@.
Qed.

Lemma gev_@ID@ : forall p k, virt p = true -> pexp p = Some (S k) ->
  lift (cden [] [] k VT_@ID@) = lift (Cc (Pos.succ p)).
Proof.
  intros p k Hv Hx. f_equal.
  unfold Cc_@ID@, frm_@ID@. rewrite (hsuccv_@ID@ p k Hx).
  rewrite (podd_succ_pexp p k Hx), (vpar_@ID@ p k Hv Hx).
  rewrite (pexp_some p (S k) Hx).
  cbn [Pos.succ pow2 @ENCF@]. rewrite epow_@ID@.
  unfold cden, VT_@ID@; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * k + 0) with k by lia. replace (0 * k + 0) with 0 by lia.
  rshape_@ID@.
Qed.

Lemma hbo_@ID@ : forall p k, virt p = true -> pexp p = Some (S k) ->
  exists n c, 0 < n /\ csteps tm n (Cc p) = Some c
              /\ lift c = lift (Cin (pow2 k)).
Proof.
  intros p k Hv Hx.
  exists (@CAB@ * k + @CBB@), (cden [] [] k CS_@ID@).
  split; [lia|]. split; [| exact (gbo_@ID@ k)].
  rewrite (gsv_@ID@ p k Hv Hx).
  exact (srun_sound tm true true chb_@ID@ VP_@ID@ CS_@ID@ @CAB@ @CBB@
           run_boot_@ID@ [] [] k ltac:(reflexivity) ltac:(reflexivity)).
Qed.

Lemma hxe_@ID@ : forall p k, virt p = true -> pexp p = Some (S k) ->
  exists n c', csteps tm n (Cin (fill (pow2 k))) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof.
  intros p k Hv Hx.
  exists (@CAE@ * k + @CBE@), (cden [] [] k VT_@ID@).
  split; [| exact (gev_@ID@ p k Hv Hx)].
  rewrite (gxi_@ID@ k).
  exact (srun_sound tm true true che_@ID@ CF_@ID@ VT_@ID@ @CAE@ @CBE@
           run_exit_@ID@ [] [] k ltac:(reflexivity) ltac:(reflexivity)).
Qed.

(** The register step, composed.  The [Theta(2^k)] middle is the [exists n]
    inside [NestedLapLift.inner_to_fill_lift]; no formula for it is written. *)
Lemma lapv_@ID@ : forall p k, virt p = true -> pexp p = Some (S k) ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof.
  intros p k Hv Hx.
  destruct (nested_overflow_lift tm Cc Cin lapin_@ID@ p (pow2 k)
              (hbo_@ID@ p k Hv Hx) (hxe_@ID@ p k Hv Hx))
    as (n & c' & Hr & Hl & Hn).
  exists n, c'. split; [exact Hn | split; [exact Hr | exact Hl]].
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
  intros p j E Hb. unfold Cc_@ID@, virt_@ID@, frm_@ID@.
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


def _far(fs):
    return clist(fs)


def render(D):
    spec = D['spec']
    ID = mach_id(spec)
    d = ENCDATA[D['enc']]
    encf = d.get('fn') or D['enc']
    V = D['vlap']
    if V['kind'] != 'nested':
        raise RegError('only the NESTED register step is rendered')
    ienc = V['key'][0]
    di = ENCDATA[ienc]
    iencf = di.get('fn') or ienc
    mods = []
    for m in (d['mod'], di['mod']):
        if m not in mods and m not in ('JpCounter', 'MonoCounter', 'WTape'):
            mods.append(m)

    # the two overflow arms, by octave parity ([podd p = true] is parity 1)
    ovf = []
    for b in (1, 0):
        O = D['ovf'][b]
        geofrm = ''
        ovf.append(OVF_GLUE
                   .replace('@B@', str(b)).replace('@BV@',
                                                   'true' if b else 'false')
                   .replace('@CAO@', str(O['c'][0]))
                   .replace('@CBO@', str(O['c'][1]))
                   .replace('@GEOFRM@', geofrm))

    vis = []
    for b in (1, 0):
        blk = ['  %s destruct q.' % ('-' if b == 1 else '-')]
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
        '@IENCF@': iencf, '@IENCM@': di['mod'],
        '@ISOME@': di['some'], '@INONE@': di['none'],
        '@UD@': clist(d['uD']), '@SOD@': clist(d['soD']),
        '@IUD@': clist(di['uD']), '@ISOD@': clist(di['soD']),
        '@TAIL@': clist(D['tail']),
        '@ITAIL@': clist(V['key'][2]), '@IFAR@': clist(V['key'][3]),
        '@ISTN@': ST[V['key'][1]],
        '@STFN@': ST[D['st_f']], '@STVN@': ST[D['st_v']],
        '@FARVC@': _far(D['far_v']),
        '@FAR1C@': _far(D['fpar'][1]), '@FAR0C@': _far(D['fpar'][0]),
        '@VSEL@': 'negb (podd p)' if D['vres'] == 0 else 'podd p',
        '@VPARV@': 'false' if D['vres'] == 0 else 'true',
        '@VPARD@': ('[discriminate | reflexivity]' if D['vres'] == 0
                    else '[reflexivity | discriminate]'),
        '@P0@': str(D['p0']), '@BOOT@': str(D['boot']),
        '@A0@': EL.cconf(D['A0']), '@A1@': EL.cconf(D['A1']),
        '@CHI@': EL.cchain(D['chi']),
        '@CAI@': str(D['ci'][0]), '@CBI@': str(D['ci'][1]),
        '@B01@': EL.cconf(D['ovf'][1]['B0']),
        '@B11@': EL.cconf(D['ovf'][1]['B1']),
        '@CHO1@': EL.cchain(D['ovf'][1]['ch']),
        '@CAO1@': str(D['ovf'][1]['c'][0]), '@CBO1@': str(D['ovf'][1]['c'][1]),
        '@B00@': EL.cconf(D['ovf'][0]['B0']),
        '@B10@': EL.cconf(D['ovf'][0]['B1']),
        '@CHO0@': EL.cchain(D['ovf'][0]['ch']),
        '@CAO0@': str(D['ovf'][0]['c'][0]), '@CBO0@': str(D['ovf'][0]['c'][1]),
        '@VP@': EL.cconf(V['VP']), '@CS@': EL.cconf(V['CinS']),
        '@CHB@': EL.cchain(V['chb']),
        '@CAB@': str(V['cb'][0]), '@CBB@': str(V['cb'][1]),
        '@AI0@': EL.cconf(V['AI0']), '@AI1@': EL.cconf(V['AI1']),
        '@CHN@': EL.cchain(V['chn']),
        '@CAN@': str(V['cn'][0]), '@CBN@': str(V['cn'][1]),
        '@CF@': EL.cconf(V['CinF']), '@VT@': EL.cconf(V['T']),
        '@CHE@': EL.cchain(V['che']),
        '@CAE@': str(V['ce'][0]), '@CBE@': str(V['ce'][1]),
        '@OVFGLUE@': '\n'.join(ovf),
        '@VISITS1@': vis[0], '@VISITS0@': vis[1],
        '@CI@': '%d*j+%d' % D['ci'],
        '@CO1@': '%d*j+%d' % D['ovf'][1]['c'],
        '@CO0@': '%d*j+%d' % D['ovf'][0]['c'],
        '@CB@': '%d*k+%d' % V['cb'], '@CE@': '%d*k+%d' % V['ce'],
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
    a = ap.parse_args()
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
