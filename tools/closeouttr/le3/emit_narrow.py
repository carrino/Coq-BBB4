#!/usr/bin/env python3
"""UNTRUSTED emitter: a valfam family whose fill law NARROWS the counter in
some phase -> a Coq board closed by [LadderCheckNarrowTr] (SCOPING_INSTR
7.4.LE3).

LE2's respell re-reads a narrowing fill when the terminator it lands on
starts with the top digit word.  When it does not (the landing terminator is
off a digit-word boundary by a cell: `(10)^k 01 -> (11)^(k-1) 0101`), this
emits the family as it is: the [Fam] record carries the fill laws with
`f_s = max(widens, 0)`, the board carries `nar ph = max(-widens, 0)` and a
minimum width per phase `minw` (the least fixpoint of the floor constraints;
the cycle must gain width overall or there is none).  The split is
[LadderCheck]'s (Binary, 1) one: interior arms per digit and index, fill
arms per index (from the phase's floor up) and phase.  Arm search, visits
and boot are emit_step.py's.

    python3 emit_narrow.py CERT.json -o OUT.v [--qh]
"""
import argparse
import copy
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import emit_step as S  # noqa: E402
from emit_step import (E, NoClosure, blk, ARM_GRID, coq_conf, coq_chain_l,  # noqa: E402
                       coq_seg, clist, ST, SYM, _splits, _rstrip0, Arms,
                       nvisits, prog_coq, inner_coq, ARM, BOOTL)


def minimum_widths(fills, nph):
    """least minw with minw >= 1, minw + f_s >= nar + m, and
    minw + f_s >= nar + minw[to]; None if the cycle loses width"""
    minw = [1] * nph
    for _ in range(4 * nph + 4):
        ch = False
        for ph, f in enumerate(fills):
            w = f['widens_by']
            fs, nar = max(w, 0), max(-w, 0)
            m = len(f['target_prefix']) + len(f['target_suffix'])
            need = max(1, nar + m - fs, nar + minw[f['lands_in_phase']] - fs)
            if need > minw[ph]:
                minw[ph], ch = need, True
        if not ch:
            return minw
        if max(minw) > 64:
            return None
    return None


def fam_cells(fam, ds, ph):
    tails = fam.get('terminators_by_phase') or [fam['terminator']]
    out = list(fam['near_head_prefix'])
    for d in ds:
        out.extend(fam['digits'][d])
    return out + list(tails[ph])


def advance_boot(cert, minw, members=64, steps=400000):
    """walk the family's own successor (fills narrowing as they do) from the
    boot to the first member at or above its phase's floor, and find the
    index at which the machine stands on it (up to trailing blanks)"""
    fam = cert['family']
    fills = cert.get('fill_by_phase') or [cert['fill']]
    b = fam['base']
    ds, ph = list(cert['boot']['digits_lsb_first']), cert['boot'].get('phase', 0)
    for _ in range(members):
        if len(ds) >= minw[ph]:
            break
        if all(d == b - 1 for d in ds):
            f = fills[ph]
            w = len(ds) + f['widens_by']
            mid = w - len(f['target_prefix']) - len(f['target_suffix'])
            if mid < 0:
                return None
            ds = (list(f['target_prefix']) + [f['target_fill_digit']] * mid
                  + list(f['target_suffix']))
            ph = f['lands_in_phase']
        else:
            i = 0
            while ds[i] == b - 1:
                ds[i] = 0
                i += 1
            ds[i] += 1
    else:
        return None
    want = _rstrip0(fam_cells(fam, ds, ph))
    other = _rstrip0(fam['other_side_cells'])
    q0, hs, right = 'ABCD'.index(fam['state']), fam['head'], fam['side'] == 'R'
    tab = E.parse_pins_tab(cert['spec'])
    L_, R_, h, q = [], [], 0, 0
    for t in range(steps):
        if q == q0 and h == hs:
            side, oth = (R_, L_) if right else (L_, R_)
            if _rstrip0(side) == want and _rstrip0(oth) == other:
                return dict(steps_from_blank=t, digits_lsb_first=ds, phase=ph,
                            cells=fam_cells(fam, ds, ph))
        e = tab[(q, h)]
        if e is None:
            return None
        wv, d, nq = e
        if d == 'R':
            L_.insert(0, wv)
            h = R_.pop(0) if R_ else 0
        else:
            R_.insert(0, wv)
            h = L_.pop(0) if L_ else 0
        q = nq
    return None


def closure_data_narrow(cert, tab):
    fam = cert['family']
    fills = cert.get('fill_by_phase') or [cert['fill']]
    nph = len(fills)
    b = fam['base']
    if fam.get('code') != 'binary' or fam.get('weights') is not None:
        raise NoClosure('code %s / numeration %s: (Binary, 1) only'
                        % (fam.get('code'), fam.get('numeration')))
    if fam.get('value_step_per_anchor_visit', 1) != 1:
        raise NoClosure('step %d' % fam['value_step_per_anchor_visit'])
    if b < 2:
        raise NoClosure('base %d' % b)
    for ph, f in enumerate(fills):
        if not 0 <= f['lands_in_phase'] < nph:
            raise NoClosure('phase %d fills into phase %d' % (ph, f['lands_in_phase']))
    minw = minimum_widths(fills, nph)
    if minw is None:
        raise NoClosure('the phase cycle does not gain width: no floor')
    nar = [max(-f['widens_by'], 0) for f in fills]
    digs = [tuple(w) for w in fam['digits']]
    pre = tuple(fam['near_head_prefix'])
    tails = [tuple(t) for t in
             (fam.get('terminators_by_phase') or [fam['terminator']])]
    if len(tails) < nph:
        raise NoClosure('%d fill laws but %d terminators' % (nph, len(tails)))
    boot = cert['boot']
    ph0 = boot.get('phase', 0)
    ds0 = list(boot['digits_lsb_first'])
    if not 0 <= ph0 < nph or len(ds0) < minw[ph0]:
        raise NoClosure('boot %r in phase %d is below the floor %r' % (ds0, ph0, minw))
    other = tuple(fam['other_side_cells'])
    q = ord(fam['state']) - 65
    hs = fam['head']
    left = fam['side'] == 'L'
    OTHER = (other, (), 0, 0, ())

    def conf(sd):
        return (q, sd, hs, OTHER) if left else (q, OTHER, hs, sd)

    derive = Arms(tab).derive
    el, er = (not left), left

    def interior_at(n0, stride):
        got = []
        for d in range(b - 1):
            for r in range(n0 + stride):
                st = 0 if r < n0 else stride
                c0 = conf(blk(pre + digs[b - 1] * r, digs[b - 1], st, digs[d]))
                c1 = conf(blk(pre + digs[0] * r, digs[0], st, digs[d + 1]))
                try:
                    ch = derive(el, er, c0, c1, 'interior arm d=%d r=%d' % (d, r))
                except NoClosure:
                    return None
                got.append((d, r, c0, c1, ch))
        return got

    inter, n0i, sti = None, None, None
    for n0, stride in ARM_GRID:
        got = interior_at(n0, stride)
        if got is not None:
            inter, n0i, sti = got, n0, stride
            break
    if inter is None:
        raise NoClosure('interior arm: no program at any threshold and stride')

    def fill_at(n0, stride):
        got = []
        for ph, f in enumerate(fills):
            to = f['lands_in_phase']
            mid = f['target_fill_digit']
            mf = len(f['target_prefix']) + len(f['target_suffix'])
            fpre = tuple(x for d in f['target_prefix'] for x in digs[d])
            fsuf = tuple(x for d in f['target_suffix'] for x in digs[d])
            for r in range(minw[ph], n0 + stride):
                st = 0 if r < n0 else stride
                fl = conf(blk(pre + digs[b - 1] * r, digs[b - 1], st, tails[ph]))
                total = r + f['widens_by'] - mf
                if total < 0:
                    return None
                hit = None
                for m1 in _splits(total):
                    cand = conf(blk(pre + fpre + digs[mid] * m1, digs[mid], st,
                                    digs[mid] * (total - m1) + fsuf + tails[to]))
                    try:
                        ch = derive(True, True, fl, cand,
                                    'fill arm r=%d ph=%d' % (r, ph))
                    except NoClosure:
                        continue
                    hit = (r, ph, m1, total - m1, fl, cand, ch)
                    break
                if hit is None:
                    return None
                got.append(hit)
        return got

    want = [(q_, s_) for q_ in range(4) for s_ in range(2)
            if (q_, s_) not in E.TR_PINS]

    def visit_phase(fill):
        seen_at = {(r, ph): nvisits(tab, want, fl, ch)
                   for r, ph, _1, _2, fl, _c, ch in fill}
        for pv in range(nph):
            if all(i in seen_at[k] for k in seen_at if k[1] == pv for i in want):
                return pv, {r: {i: seen_at[(r, p)][i] for i in want}
                            for (r, p) in seen_at if p == pv}
        return None

    mw = max(minw)
    grid = [(n0, st) for n0, st in ARM_GRID if n0 >= mw]
    grid += [(n0, st) for n0 in range(max(mw, 7), mw + 4) for st in range(1, 4)]
    fill, n0f, stf, pv, nvis = None, None, None, None, None
    for n0, stride in grid:
        f2 = fill_at(n0, stride)
        if f2 is None:
            continue
        vp = visit_phase(f2)
        if vp is None:
            continue
        fill, n0f, stf = f2, n0, stride
        pv, nvis = vp
        break
    if fill is None:
        raise NoClosure('fill arm: no program, or no visit phase, at any '
                        'threshold and stride (floors %r)' % minw)

    def kto(ph, tgt):
        cur = ph
        for k in range(nph + 1):
            if cur == tgt:
                return k
            cur = fills[cur]['lands_in_phase']
        return None
    kcyc = [kto(ph, pv) for ph in range(nph)]
    if any(k is None for k in kcyc):
        raise NoClosure('the phase cycle does not reach phase %d' % pv)

    cells = list(pre)
    for d in ds0:
        cells.extend(digs[d])
    cells.extend(tails[ph0])
    if _rstrip0(cells) != _rstrip0(boot['cells']):
        raise NoClosure('boot cells %r are not the family at %r'
                        % (boot['cells'], ds0))
    return dict(nest=True, b=b, el=el, er=er, nph=nph, ph0=ph0, pv=pv,
                kcyc=kcyc, nar=nar, minw=minw, inter=inter, n0i=n0i, sti=sti,
                fill=fill, n0f=n0f, stf=stf, ds0=ds0,
                t0=boot['steps_from_blank'], nvis=nvis, want=want)


THM = '''Lemma iarm_reach_%(mid)s : forall d r,
  d < fm_b FAM - 1 -> r < %(n0i)d + %(sti)d ->
  ReachL tm (negb (fm_left FAM)) (fm_left FAM)
    (lr_lhs (iarm_%(mid)s d r)) (lr_rhs (iarm_%(mid)s d r)).
Proof.
  intros d r Hd Hr. vm_compute in Hd.
%(isound)s  exfalso; lia.
Qed.

Lemma iarm_lhs_%(mid)s : forall d r,
  d < fm_b FAM - 1 -> r < %(n0i)d + %(sti)d ->
  lr_lhs (iarm_%(mid)s d r)
    = cls_conf FAM (cls_side FAM [] (fm_b FAM - 1) r
                      (astride %(n0i)d %(sti)d r) [d]).
Proof.
  intros d r Hd Hr. vm_compute in Hd.
%(icomp)s  exfalso; lia.
Qed.

Lemma iarm_rhs_%(mid)s : forall d r,
  d < fm_b FAM - 1 -> r < %(n0i)d + %(sti)d ->
  lr_rhs (iarm_%(mid)s d r)
    = cls_conf FAM (cls_side FAM [] 0 r (astride %(n0i)d %(sti)d r) [S d]).
Proof.
  intros d r Hd Hr. vm_compute in Hd.
%(icomp)s  exfalso; lia.
Qed.

Lemma farm_reach_%(mid)s : forall r ph, minw_%(mid)s ph <= r ->
  r < %(n0f)d + %(stf)d -> ph < %(nph)d ->
  ReachL tm true true (lr_lhs (farm_%(mid)s r ph)) (lr_rhs (farm_%(mid)s r ph)).
Proof.
  intros r ph Hr0 Hr Hph.
%(fsound)s  exfalso; lia.
Qed.

Lemma farm_lhs_%(mid)s : forall r ph, minw_%(mid)s ph <= r ->
  r < %(n0f)d + %(stf)d -> ph < %(nph)d ->
  lr_lhs (farm_%(mid)s r ph)
    = cls_conf FAM (run_side FAM (fm_b FAM - 1) r (astride %(n0f)d %(stf)d r)
                      0 ph [] []).
Proof.
  intros r ph Hr0 Hr Hph.
%(fcomp)s  exfalso; lia.
Qed.

Lemma farm_rhs_%(mid)s : forall r ph, minw_%(mid)s ph <= r ->
  r < %(n0f)d + %(stf)d -> ph < %(nph)d ->
  lr_rhs (farm_%(mid)s r ph)
    = cls_conf FAM (run_side FAM (f_mid (fam_fill FAM ph)) (fm1_%(mid)s r ph)
                      (astride %(n0f)d %(stf)d r) (fm2_%(mid)s r ph)
                      (f_to (fam_fill FAM ph))
                      (f_pre (fam_fill FAM ph)) (f_suf (fam_fill FAM ph))).
Proof.
  intros r ph Hr0 Hr Hph.
%(fcomp)s  exfalso; lia.
Qed.

Lemma fm12_%(mid)s : forall r ph, minw_%(mid)s ph <= r ->
  r < %(n0f)d + %(stf)d -> ph < %(nph)d ->
  fm1_%(mid)s r ph + fm2_%(mid)s r ph + nar_%(mid)s ph
  + (length (f_pre (fam_fill FAM ph)) + length (f_suf (fam_fill FAM ph)))
  = r + f_s (fam_fill FAM ph).
Proof.
  intros r ph Hr0 Hr Hph.
%(flia)s  exfalso; lia.
Qed.

Lemma vis_ok_%(mid)s : forall r t, ~ In t pins_%(mid)s ->
  minw_%(mid)s %(pv)d <= r -> r < %(n0f)d + %(stf)d ->
  nfire tm true true nrules (vsegs_%(mid)s r t) (vis_%(mid)s r t)
    (lr_lhs (farm_%(mid)s r %(pv)d)) = Some t.
Proof.
  intros r t Hnp Hr0 Hr.
%(fvis)s  exfalso; lia.
Qed.

'''

NQH = '''(** The machine-level theorem, at the INSTRUCTION level, through the
    narrowing board [LadderCheckNarrowTr.boardNw_neverqhtr]. *)
Theorem nqhtr_%(mid)s : NeverQuasiHaltsTr tm_%(mid)s.
Proof.
  eapply (boardNw_neverqhtr tm_%(mid)s pins_%(mid)s FAM %(nph)d
                            nar_%(mid)s minw_%(mid)s iarm_%(mid)s %(n0i)d %(sti)d
                            farm_%(mid)s %(n0f)d %(stf)d
                            fm1_%(mid)s fm2_%(mid)s %(pv)d
                            nrules vsegs_%(mid)s vis_%(mid)s
                            %(ds0)s %(ph0)d).
%(args)s  - exact bootl_%(mid)s.
Qed.
'''

QH = '''(** a pinned instruction fired before the boot: the quasihalt witness *)
Lemma wit_%(mid)s :
  existsb (fun tg => cfires tm_%(mid)s c0 %(t0)d tg) pins_%(mid)s = true.
Proof. vm_compute. reflexivity. Qed.

Lemma bnd_%(mid)s : (%(t0)d <=? 32779478) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

(** The machine-level theorem, on the QUASIHALTING side, through the
    narrowing board [LadderCheckNarrowTr.boardNw_qhtr]. *)
Theorem qhtr_%(mid)s :
  NonHalt tm_%(mid)s /\\ QHBoundTr 32779478 tm_%(mid)s /\\ QuasiHaltsTr tm_%(mid)s.
Proof.
  eapply (boardNw_qhtr tm_%(mid)s pins_%(mid)s FAM %(nph)d
                       nar_%(mid)s minw_%(mid)s iarm_%(mid)s %(n0i)d %(sti)d
                       farm_%(mid)s %(n0f)d %(stf)d
                       fm1_%(mid)s fm2_%(mid)s %(pv)d
                       nrules vsegs_%(mid)s vis_%(mid)s
                       %(ds0)s %(ph0)d).
%(args)s  - exact bootl_%(mid)s.
  - exact wit_%(mid)s.
  - exact bnd_%(mid)s.
Qed.
'''

HEAD = '''
(** ** The closure: a fill law that NARROWS ([LadderCheckNarrowTr])

    The phase cycle widens by %(ws)s; [LadderFam.Fill] states a widening as
    a [nat], so the narrowing is carried beside the family ([nar]), with a
    floor per phase ([minw] = %(minw)s) below which no width is reached.
    Interior arms at threshold %(n0i)d stride %(sti)d, fill arms at threshold
    %(n0f)d stride %(stf)d from each phase's floor.  Every arm is a
    [LadderNest] segment program. *)
From BBB4.Checkers Require Import LadderCheckNarrowTr.

'''


def emit_closure_narrow(cert, tab, mid):
    cd = S.two_pass(closure_data_narrow, ORIG, tab)
    if isinstance(cd, NoClosure):
        return E.CLOSURE_NONE % cd, None
    b = cd['b']
    n0i, sti, n0f, stf = cd['n0i'], cd['sti'], cd['n0f'], cd['stf']
    nph, ph0, pv, minw = cd['nph'], cd['ph0'], cd['pv'], cd['minw']
    nA, nF = n0i + sti, n0f + stf
    el, er = cd['el'], cd['er']
    fills = ORIG.get('fill_by_phase') or [ORIG['fill']]
    L = [HEAD % dict(ws=', '.join('%+d' % f['widens_by'] for f in fills),
                     minw=minw, n0i=n0i, sti=sti, n0f=n0f, stf=stf)]
    inner, arms = [], []
    for d, r, c0, c1, ch in cd['inter']:
        arms.append(('iarm%d_%d' % (d, r), c0, c1, prog_coq(tab, inner, ch), el, er))
    offs = {}
    for r, ph, _m1, _m2, fl, fr, fch in cd['fill']:
        offs[(r, ph)] = len(inner)
        arms.append(('farm%d_%d' % (r, ph), fl, fr, prog_coq(tab, inner, fch),
                     True, True))
    L.append(inner_coq(mid, inner))
    for nm, c0, c1, segs, el_, er_ in arms:
        L.append(ARM % dict(nm=nm, mid=mid, lhs=coq_conf(c0), rhs=coq_conf(c1),
                            segs=';\n   '.join(segs), el=str(el_).lower(),
                            er=str(er_).lower()))
    d0, r0 = cd['inter'][0][:2]
    fr0, fp0 = cd['fill'][0][:2]
    L.append('''(** *** The dispatch, the narrowings and the floors *)
Definition iarm_%(mid)s (d r : nat) : LRule :=
  match d, r with
  %(ib)s
  | _, _ => iarm%(d0)d_%(r0)d_%(mid)s
  end.

Definition farm_%(mid)s (r ph : nat) : LRule :=
  match r, ph with
  %(fb)s
  | _, _ => farm%(fr0)d_%(fp0)d_%(mid)s
  end.

Definition fm1_%(mid)s (r ph : nat) : nat :=
  match r, ph with %(b1)s | _, _ => 0 end.
Definition fm2_%(mid)s (r ph : nat) : nat :=
  match r, ph with %(b2)s | _, _ => 0 end.

Definition nar_%(mid)s (ph : nat) : nat :=
  match ph with %(nb)s | _ => 0 end.
Definition minw_%(mid)s (ph : nat) : nat :=
  match ph with %(mb)s | _ => 1 end.

Definition vis_%(mid)s (r : nat) (t : Instr) : list lstep :=
  match r, t with
  %(vb)s
  | _, _ => []
  end.

Definition vsegs_%(mid)s (r : nat) (t : Instr) : list nseg :=
  match r, t with
  %(sb)s
  | _, _ => []
  end.

''' % dict(
        mid=mid, d0=d0, r0=r0, fr0=fr0, fp0=fp0,
        ib='\n  '.join('| %d, %d => iarm%d_%d_%s' % (d, r, d, r, mid)
                       for d, r, *_ in cd['inter']),
        fb='\n  '.join('| %d, %d => farm%d_%d_%s' % (r, ph, r, ph, mid)
                       for r, ph, *_ in cd['fill']),
        b1=' '.join('| %d, %d => %d' % (r, ph, m1) for r, ph, m1, *_ in cd['fill']),
        b2=' '.join('| %d, %d => %d' % (r, ph, m2)
                    for r, ph, _m1, m2, *_ in cd['fill']),
        nb=' '.join('| %d => %d' % (ph, x) for ph, x in enumerate(cd['nar'])),
        mb=' '.join('| %d => %d' % (ph, x) for ph, x in enumerate(minw)),
        vb='\n  '.join('| %d, (%s, %s) => %s'
                       % (r, ST[i[0]], SYM[i[1]], coq_chain_l(v[1]))
                       for r in sorted(cd['nvis'])
                       for i, v in sorted(cd['nvis'][r].items())),
        sb='\n  '.join('| %d, (%s, %s) => [%s]'
                       % (r, ST[i[0]], SYM[i[1]],
                          '; '.join(coq_seg(sg, offs[(r, pv)]) for sg in v[0]))
                       for r in sorted(cd['nvis'])
                       for i, v in sorted(cd['nvis'][r].items()))))

    def reach(nm):
        return ('eapply narm_reach; [exact nrules_sound_%(mid)s '
                '| exact ok_' + nm + '_%(mid)s]')

    def ibranches(body):
        out = []
        for d in range(b - 1):
            rb = []
            for r in range(nA):
                rb.append('    destruct r as [|r].\n    { %s. }\n'
                          % (body % dict(d=d, r=r, mid=mid)))
            out.append('  destruct d as [|d].\n  {\n%s    exfalso; lia.\n  }\n'
                       % ''.join(rb))
        return ''.join(out)

    def fbranches(body):
        out = []
        for r in range(nF):
            pb = []
            for ph in range(nph):
                if r < minw[ph]:
                    pb.append('    destruct ph as [|ph].\n'
                              '    { vm_compute in Hr0; lia. }\n')
                else:
                    pb.append('    destruct ph as [|ph].\n    { %s. }\n'
                              % (body % dict(r=r, ph=ph, mid=mid)))
            out.append('  destruct r as [|r].\n  {\n%s    exfalso; lia.\n  }\n'
                       % ''.join(pb))
        return ''.join(out)

    fvis = ''.join(
        ('  destruct r as [|r].\n  { vm_compute in Hr0; lia. }\n' if r < minw[pv] else
         '  destruct r as [|r].\n  { destruct t as [q s]; destruct q, s; '
         'try (exfalso; apply Hnp; simpl; tauto); vm_compute; reflexivity. }\n')
        for r in range(nF))
    L.append(THM % dict(
        mid=mid, nph=nph, n0i=n0i, sti=sti, n0f=n0f, stf=stf, pv=pv,
        isound=ibranches(reach('iarm%(d)d_%(r)d')),
        icomp=ibranches('vm_compute; reflexivity'),
        fsound=fbranches(reach('farm%(r)d_%(ph)d')),
        fcomp=fbranches('vm_compute; reflexivity'),
        flia=fbranches('vm_compute; lia'),
        fvis=fvis))
    L.append(BOOTL % dict(mid=mid, t0=cd['t0'], ds0=clist(cd['ds0'], str),
                          ph0=ph0,
                          tmb=('tm_%s' % mid) if E.TR_QH is not None else 'tm'))

    def pharg(body):
        out = ['  - intros ph Hph.\n']
        for _ in range(nph):
            out.append('    destruct ph as [|ph].\n    { %s. }\n' % body)
        out.append('    exfalso; lia.\n')
        return ''.join(out)

    hcyc = ''.join(['  - intros ph Hph.\n']
                   + ['    destruct ph as [|ph].\n'
                      '    { exists %d; vm_compute; reflexivity. }\n' % k
                      for k in cd['kcyc']]
                   + ['    exfalso; lia.\n'])
    args = ''.join([
        '  - vm_compute; lia.\n',                       # Hb
        '  - vm_compute; reflexivity.\n',               # Hcode
        '  - vm_compute; reflexivity.\n',               # Hstep
        pharg('vm_compute; repeat constructor'),        # Hfpre
        pharg('vm_compute; repeat constructor'),        # Hfsuf
        pharg('vm_compute; lia'),                       # Hfmid
        pharg('vm_compute; lia'),                       # Hfto
        pharg('vm_compute; split; [lia | split; lia]'),  # Hmin
        pharg('vm_compute; lia'),                       # HN0f
        '  - lia.\n',                                   # Hpv
        hcyc,                                           # Hcyc
        '  - exact fm12_%s.\n' % mid,
        '  - repeat constructor.\n',                    # Hbnd0
        '  - vm_compute; lia.\n',                       # Hlen0
        '  - lia.\n',                                   # Hph0
        '  - lia.\n',                                   # Hsti
        '  - exact iarm_reach_%s.\n' % mid,
        '  - exact iarm_lhs_%s.\n' % mid,
        '  - exact iarm_rhs_%s.\n' % mid,
        '  - lia.\n',                                   # Hstf
        '  - exact farm_reach_%s.\n' % mid,
        '  - exact farm_lhs_%s.\n' % mid,
        '  - exact farm_rhs_%s.\n' % mid,
        '  - exact nrules_sound_%s.\n' % mid,
        '  - exact vis_ok_%s.\n' % mid,
    ])
    common = dict(mid=mid, t0=cd['t0'], ds0=clist(cd['ds0'], str), ph0=ph0,
                  nph=nph, pv=pv, n0i=n0i, sti=sti, n0f=n0f, stf=stf, args=args)
    L.append((QH if E.TR_QH is not None else NQH) % common)
    return ''.join(L), cd


ORIG = None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('cert')
    ap.add_argument('-o', '--out', required=True)
    ap.add_argument('--qh', action='store_true')
    ap.add_argument('--scan', default=os.path.join(HERE, '..', '..', '..',
                                                   'censustr_v9_scan_1e8.txt'))
    args = ap.parse_args()
    cert = json.load(open(args.cert))
    if isinstance(cert, list):
        cert = cert[0]
    global ORIG
    E.emit_closure = emit_closure_narrow
    if args.qh:
        row = None
        for l in open(args.scan):
            if l.startswith(cert['spec'] + ' '):
                row = l.split()[1:]
                break
        E.TR_PINS, lastf = E.quiet_pins(cert['spec'], row)
        t0, ds, ph, cells = E.qh_boot(cert, lastf)
        cert['boot'] = dict(cert['boot'], steps_from_blank=t0,
                            digits_lsb_first=ds, phase=ph, cells=cells)
        E.TR_QH = t0
    else:
        E.TR_PINS = E.unfired(cert['spec'], 10 ** 6)
    # a boot below its phase's floor moves to the next member at or above it
    fills = cert.get('fill_by_phase') or [cert['fill']]
    minw = minimum_widths(fills, len(fills))
    b0 = cert['boot']
    if minw is not None and len(b0['digits_lsb_first']) < minw[b0.get('phase', 0)]:
        nb = advance_boot(cert, minw)
        if nb is not None:
            cert['boot'] = dict(b0, **nb)
            if args.qh:
                E.TR_QH = nb['steps_from_blank']
    ORIG = copy.deepcopy(cert)
    # the Fam record states f_s : nat; the narrowing rides beside it
    for f in (cert.get('fill_by_phase') or []) + ([cert['fill']] if cert.get('fill') else []):
        f['widens_by'] = max(f['widens_by'], 0)
    good, bad, cd = E.emit(cert, args.out)
    print('%s: closure %s' % (args.out, 'BUILT' if cd else 'not built'))
    return 0 if cd else 1


if __name__ == '__main__':
    sys.exit(main())
