#!/usr/bin/env python3
"""UNTRUSTED emitter (SCOPING_INSTR 7.4.LE7): a mirrored binary counter
(`mirror_detect.py`) -> a Coq board closed by [LadderCheckMirrorTr].

The machine and the header are `emit_ladder.emit`'s (its one-sided [Fam]
record is written but unused); the closure is replaced by the mirror's two
arm classes, each a [LadderNest] segment program found by LE3's arm search
(`emit_step.Arms`), with a repeated block on BOTH sides at one index:

* interior `d r`: `t^r d | t^r d -> 0^r (d+1) | 0^r (d+1)`, both rests opaque;
* top `r` (r > 0): `t^r sufL | t^r sufR -> 0^r 1 sufL | 0^r 1 sufR`, both tails
  known empty;

each as TWO halves, one side's carry and then the other's, meeting on the
anchor cell at the (state, symbol) `mirror_split.split_of` reads off the run;
each half rewrites one side and keeps the other as an opaque tail.

The fires are read from every top arm (`emit_step.nvisits`).

    python3 emit_mirror.py SPEC DETECT.jsonl -o OUT.v [--qh]
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
                       coq_seg, clist, ST, SYM, Arms, nvisits, prog_coq, inner_coq, ARM)
import mirror_detect as MD  # noqa: E402
import mirror_split as MS  # noqa: E402
sys.path.insert(0, os.path.join(HERE, '..', 'le6'))
sys.path.insert(0, os.path.join(HERE, '..', 'le4'))
import emit_run2z as RZ  # noqa: E402


def cells(s):
    return tuple(int(ch) for ch in s)


def boot_of(spec, det, lastf, steps=400000):
    """(t, x) at the first anchor visit past lastf that reads"""
    q0, s0 = det['anchor']
    L, R = det['L'], det['R']
    aL = (L['pre'], L['l'], L['words'], L['suf'])
    aR = (R['pre'], R['l'], R['words'], R['suf'])
    vis = MD.both_strings(spec, steps).get((q0, s0), [])
    for t, ls, rs in vis:
        if t <= lastf:
            continue
        d = MD.decode(ls, *aL)
        if d and MD.decode(rs, *aR) == d:
            return t, d
    raise NoClosure('no boot past %d' % lastf)


SFLAT = ((), (), 0, 0, ())


def hcL(q, l, h):
    return (q, l, h, SFLAT)


def hcR(q, r, h):
    return (q, SFLAT, h, r)


def halfA(lf, q, h, l, r):
    return hcL(q, l, h) if lf else hcR(q, r, h)


def halfB(lf, q, h, l, r):
    return hcR(q, r, h) if lf else hcL(q, l, h)


def closure_data(det, tab, boot, sp):
    q, hs = det['anchor']
    lf, qI, hI, qT, hT = sp['lf'], sp['qI'], sp['hI'], sp['qT'], sp['hT']
    L, R = det['L'], det['R']
    preL, preR = cells(L['pre']), cells(R['pre'])
    sufL, sufR = cells(L['suf']), cells(R['suf'])
    DL = [cells(w) for w in L['words']]
    DR = [cells(w) for w in R['words']]
    b = 2
    derive = Arms(tab).derive

    def sides(n0, st, r, wLt, wRt, wL0, wR0):
        s_ = 0 if r < n0 else st
        return (blk(preL + DL[b - 1] * r, DL[b - 1], s_, wLt),
                blk(preR + DR[b - 1] * r, DR[b - 1], s_, wRt),
                blk(preL + DL[0] * r, DL[0], s_, wL0),
                blk(preR + DR[0] * r, DR[0], s_, wR0))

    def inter_at(n0, st):
        got = []
        for d in range(b - 1):
            for r in range(n0 + st):
                Lt, Rt, L0, R0 = sides(n0, st, r, DL[d], DR[d], DL[d + 1], DR[d + 1])
                a0, a1 = halfA(lf, q, hs, Lt, Rt), halfA(lf, qI, hI, L0, R0)
                b0, b1 = halfB(lf, qI, hI, Lt, Rt), halfB(lf, q, hs, L0, R0)
                try:
                    p1 = derive(False, False, a0, a1, 'interior half 1 d=%d r=%d' % (d, r))
                    p2 = derive(False, False, b0, b1, 'interior half 2 d=%d r=%d' % (d, r))
                except NoClosure:
                    return None
                got.append((d, r, (a0, a1, p1), (b0, b1, p2)))
        return got

    def top_at(n0, st):
        got = []
        for r in range(1, n0 + st):
            Lt, Rt, L0, R0 = sides(n0, st, r, sufL, sufR, DL[1] + sufL, DR[1] + sufR)
            a0, a1 = halfA(lf, q, hs, Lt, Rt), halfA(lf, qT, hT, L0, R0)
            b0, b1 = halfB(lf, qT, hT, Lt, Rt), halfB(lf, q, hs, L0, R0)
            try:
                p1 = derive(lf, not lf, a0, a1, 'top half 1 r=%d' % r)
                p2 = derive(not lf, lf, b0, b1, 'top half 2 r=%d' % r)
            except NoClosure:
                return None
            got.append((r, (a0, a1, p1), (b0, b1, p2)))
        return got

    inter = None
    for n0, st in ARM_GRID:
        inter = inter_at(n0, st)
        if inter is not None:
            n0i, sti = n0, st
            break
    if inter is None:
        raise NoClosure('interior: no program at any threshold and stride')
    want = [(q_, s_) for q_ in range(4) for s_ in range(2) if (q_, s_) not in E.TR_PINS]
    top = None
    for n0, st in ARM_GRID:
        if n0 < 1:
            continue
        g = top_at(n0, st)
        if g is None:
            continue
        how = {}
        ok = True
        for r, (a0, _a1, p1), (b0, _b1, p2) in g:
            s1 = RZ.nvisits_f(tab, want, a0, p1, lf, not lf)
            s2 = RZ.nvisits_f(tab, want, b0, p2, not lf, lf)
            for i in want:
                if i in s1:
                    how[(r, i)] = (1, s1[i])
                elif i in s2:
                    how[(r, i)] = (2, s2[i])
                else:
                    ok = False
        if ok:
            top, n0t, stt = g, n0, st
            break
    if top is None:
        raise NoClosure('top: no program, or an instruction neither half of a top arm fires')
    return dict(nest=True, inter=inter, n0i=n0i, sti=sti, top=top, n0t=n0t, stt=stt, how=how,
                want=want, preL=preL, preR=preR, sufL=sufL, sufR=sufR, DL=DL, DR=DR,
                q=q, hs=hs, sp=sp, boot=boot, fill=top)


HEAD = '''
(** ** The closure: a MIRRORED binary counter ([LadderCheckMirrorTr])

    At the anchor each side, read outward from the head, is
    [pre ++ flat_map D x ++ suf] for ONE digit string [x] (its own two words
    per side): left [%(Lp)s (%(L0)s|%(L1)s)^n %(Ls)s], right [%(Rp)s (%(R0)s|%(R1)s)^n %(Rs)s].
    Every increment is two one-sided programs, the %(first)s side first,
    meeting on the anchor cell.  Interior arms at threshold %(n0i)d stride
    %(sti)d, top arms at %(n0t)d / %(stt)d.  Every arm is a [LadderNest]
    segment program. *)
From BBB4.Checkers Require Import LadderCheckMirrorTr.

Definition mDL_%(mid)s : list (list Sym) := %(DLc)s.
Definition mDR_%(mid)s : list (list Sym) := %(DRc)s.
Definition mpreL_%(mid)s : list Sym := %(preLc)s.
Definition mpreR_%(mid)s : list Sym := %(preRc)s.
Definition msufL_%(mid)s : list Sym := %(sufLc)s.
Definition msufR_%(mid)s : list Sym := %(sufRc)s.

'''

SL = '(sLt 2 mDL_%(mid)s mpreL_%(mid)s %(N0)s %(ST)s %(D)s r %(WLt)s)'
SR = '(sRt 2 mDR_%(mid)s mpreR_%(mid)s %(N0)s %(ST)s %(D)s r %(WRt)s)'
SL0 = '(sL0 mDL_%(mid)s mpreL_%(mid)s %(N0)s %(ST)s r %(WL0)s)'
SR0 = '(sR0 mDR_%(mid)s mpreR_%(mid)s %(N0)s %(ST)s r %(WR0)s)'

ARMLEM = '''Lemma %(nm)s_reach_%(mid)s : %(binder)s
  ReachL tm %(el)s %(er)s (lr_lhs (%(nm)s_%(mid)s %(args)s)) (lr_rhs (%(nm)s_%(mid)s %(args)s)).
Proof.
  %(intro)s
%(sound)s  exfalso; lia.
Qed.

Lemma %(nm)s_lhs_%(mid)s : %(binder)s
  lr_lhs (%(nm)s_%(mid)s %(args)s) = %(half0)s %(lf)s %(q0)s %(h0)s %(sl)s %(sr)s.
Proof.
  %(intro)s
%(comp)s  exfalso; lia.
Qed.

Lemma %(nm)s_rhs_%(mid)s : %(binder)s
  lr_rhs (%(nm)s_%(mid)s %(args)s) = %(half1)s %(lf)s %(q1)s %(h1)s %(sl0)s %(sr0)s.
Proof.
  %(intro)s
%(comp)s  exfalso; lia.
Qed.

'''

THM = '''Lemma vis_ok_%(mid)s : forall t, ~ In t pins_%(mid)s ->
  forall r, 0 < r -> r < %(n0t)d + %(stt)d ->
    nfire tm %(lf)s (negb %(lf)s) nrules (vsegs1_%(mid)s r t) (vis1_%(mid)s r t) (lr_lhs (at1_%(mid)s r)) = Some t
    \\/ nfire tm (negb %(lf)s) %(lf)s nrules (vsegs2_%(mid)s r t) (vis2_%(mid)s r t) (lr_lhs (at2_%(mid)s r)) = Some t.
Proof.
  intros t Hnp. destruct t as [q s]; destruct q, s; try (exfalso; apply Hnp; simpl; tauto);
  intros r H0 Hr.
%(fvis)s
Qed.

Lemma bootl_%(mid)s :
  stepn %(tmb)s %(t0)d InitES = Some (lift (mcfg mDL_%(mid)s mDR_%(mid)s mpreL_%(mid)s mpreR_%(mid)s msufL_%(mid)s msufR_%(mid)s %(q)s %(hs)s %(x0)s)).
Proof.
  assert (H : match csteps %(tmb)s %(t0)d c0 with
              | Some c => ceqb c (mcfg mDL_%(mid)s mDR_%(mid)s mpreL_%(mid)s mpreR_%(mid)s msufL_%(mid)s msufR_%(mid)s %(q)s %(hs)s %(x0)s)
              | None => false end = true) by (vm_compute; reflexivity).
  destruct (csteps %(tmb)s %(t0)d c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

'''

ARGS = '''  - lia.
  - split; [repeat constructor; lia | discriminate].
  - lia.
  - exact ai1_reach_%(mid)s.
  - exact ai2_reach_%(mid)s.
  - exact ai1_lhs_%(mid)s.
  - exact ai1_rhs_%(mid)s.
  - exact ai2_lhs_%(mid)s.
  - exact ai2_rhs_%(mid)s.
  - lia.
  - lia.
  - exact at1_reach_%(mid)s.
  - exact at2_reach_%(mid)s.
  - exact at1_lhs_%(mid)s.
  - exact at1_rhs_%(mid)s.
  - exact at2_lhs_%(mid)s.
  - exact at2_rhs_%(mid)s.
  - exact nrules_sound_%(mid)s.
  - exact vis_ok_%(mid)s.
  - exact bootl_%(mid)s.
'''

CALL = '''(%(board)s tm_%(mid)s pins_%(mid)s 2 mDL_%(mid)s mDR_%(mid)s mpreL_%(mid)s mpreR_%(mid)s
                 msufL_%(mid)s msufR_%(mid)s %(q)s %(hs)s %(lf)s %(qI)s %(qT)s %(hI)s %(hT)s
                 ai1_%(mid)s ai2_%(mid)s %(n0i)d %(sti)d at1_%(mid)s at2_%(mid)s %(n0t)d %(stt)d
                 nrules vsegs1_%(mid)s vsegs2_%(mid)s vis1_%(mid)s vis2_%(mid)s %(x0)s)'''

NQH = '''(** The machine-level theorem, at the INSTRUCTION level, through
    [LadderCheckMirrorTr.boardM_neverqhtr]. *)
Theorem nqhtr_%(mid)s : NeverQuasiHaltsTr tm_%(mid)s.
Proof.
  eapply %(call)s.
%(args)sQed.
'''

QH = '''Lemma wit_%(mid)s :
  existsb (fun tg => cfires tm_%(mid)s c0 %(t0)d tg) pins_%(mid)s = true.
Proof. vm_compute. reflexivity. Qed.

Lemma bnd_%(mid)s : (%(t0)d <=? 32779478) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

(** The machine-level theorem, on the QUASIHALTING side, through
    [LadderCheckMirrorTr.boardM_qhtr]. *)
Theorem qhtr_%(mid)s :
  NonHalt tm_%(mid)s /\\ QHBoundTr 32779478 tm_%(mid)s /\\ QuasiHaltsTr tm_%(mid)s.
Proof.
  eapply %(call)s.
%(args)s  - exact wit_%(mid)s.
  - exact bnd_%(mid)s.
Qed.
'''

TABLES = '''Definition ai1_%(mid)s (d r : nat) : LRule :=
  match d, r with %(ib1)s | _, _ => ai1_0_0_%(mid)s end.
Definition ai2_%(mid)s (d r : nat) : LRule :=
  match d, r with %(ib2)s | _, _ => ai2_0_0_%(mid)s end.
Definition at1_%(mid)s (r : nat) : LRule :=
  match r with %(tb1)s | _ => at1_%(t1)d_%(mid)s end.
Definition at2_%(mid)s (r : nat) : LRule :=
  match r with %(tb2)s | _ => at2_%(t1)d_%(mid)s end.

'''


def syms(c):
    return '[' + ';'.join('S%d' % x for x in c) + ']'


RUN = None


def emit_closure_mirror(cert, tab, mid):
    cd = S.two_pass(lambda _c, _t: closure_data(*RUN), cert, tab)
    if isinstance(cd, NoClosure):
        return E.CLOSURE_NONE % cd, None
    n0i, sti, n0t, stt = cd['n0i'], cd['sti'], cd['n0t'], cd['stt']
    DL, DR = cd['DL'], cd['DR']
    sp = cd['sp']
    lf = 'true' if sp['lf'] else 'false'
    q, hs = ST[cd['q']], SYM[cd['hs']]
    qI, hI, qT, hT = ST[sp['qI']], SYM[sp['hI']], ST[sp['qT']], SYM[sp['hT']]
    word = lambda c: ''.join(map(str, c))  # noqa: E731
    L = [HEAD % dict(mid=mid, n0i=n0i, sti=sti, n0t=n0t, stt=stt,
                     first='left' if sp['lf'] else 'right',
                     Lp=word(cd['preL']), Rp=word(cd['preR']), Ls=word(cd['sufL']),
                     Rs=word(cd['sufR']), L0=word(DL[0]), L1=word(DL[1]),
                     R0=word(DR[0]), R1=word(DR[1]),
                     DLc='[' + ';'.join(syms(w) for w in DL) + ']',
                     DRc='[' + ';'.join(syms(w) for w in DR) + ']',
                     preLc=syms(cd['preL']), preRc=syms(cd['preR']),
                     sufLc=syms(cd['sufL']), sufRc=syms(cd['sufR']))]
    inner, arms = [], []
    for d, r, (a0, a1, p1), (b0, b1, p2) in cd['inter']:
        arms.append(('ai1_%d_%d' % (d, r), a0, a1, prog_coq(tab, inner, p1), False, False))
        arms.append(('ai2_%d_%d' % (d, r), b0, b1, prog_coq(tab, inner, p2), False, False))
    offs1, offs2 = {}, {}
    for r, (a0, a1, p1), (b0, b1, p2) in cd['top']:
        offs1[r] = len(inner)
        arms.append(('at1_%d' % r, a0, a1, prog_coq(tab, inner, p1), sp['lf'], not sp['lf']))
        offs2[r] = len(inner)
        arms.append(('at2_%d' % r, b0, b1, prog_coq(tab, inner, p2), not sp['lf'], sp['lf']))
    L.append(inner_coq(mid, inner))
    for nm, c0, c1, segs, el_, er_ in arms:
        L.append(ARM % dict(nm=nm, mid=mid, lhs=coq_conf(c0), rhs=coq_conf(c1),
                            segs=';\n   '.join(segs), el=str(el_).lower(),
                            er=str(er_).lower()))
    t1 = cd['top'][0][0]
    how = cd['how']

    def visdef(nm, k, which, offs):
        rows = sorted((r, i) for (r, i), (kk, _v) in how.items() if kk == k)
        if which == 'vis':
            body = '\n  '.join('| %d, (%s, %s) => %s' % (r, ST[i[0]], SYM[i[1]],
                                                        coq_chain_l(how[(r, i)][1][1]))
                               for r, i in rows)
            typ = 'list lstep'
        else:
            body = '\n  '.join('| %d, (%s, %s) => [%s]'
                               % (r, ST[i[0]], SYM[i[1]],
                                  '; '.join(coq_seg(sg, offs[r]) for sg in how[(r, i)][1][0]))
                               for r, i in rows)
            typ = 'list nseg'
        return ('Definition %s_%s (r : nat) (t : Instr) : %s :=\n  match r, t with\n  %s\n'
                '  | _, _ => []\n  end.\n\n' % (nm, mid, typ, body))

    L.append(TABLES % dict(
        mid=mid, t1=t1,
        ib1=' '.join('| %d, %d => ai1_%d_%d_%s' % (d, r, d, r, mid) for d, r, *_ in cd['inter']),
        ib2=' '.join('| %d, %d => ai2_%d_%d_%s' % (d, r, d, r, mid) for d, r, *_ in cd['inter']),
        tb1=' '.join('| %d => at1_%d_%s' % (r, r, mid) for r, *_ in cd['top']),
        tb2=' '.join('| %d => at2_%d_%s' % (r, r, mid) for r, *_ in cd['top'])))
    L.append(visdef('vis1', 1, 'vis', offs1) + visdef('vsegs1', 1, 'segs', offs1)
             + visdef('vis2', 2, 'vis', offs2) + visdef('vsegs2', 2, 'segs', offs2))

    def reach(nm):
        return ('eapply narm_reach; [exact nrules_sound_%s | exact ok_%s_%s]'
                % (mid, nm, mid))

    def rb(n, body, lo=0):
        return ''.join('  destruct r as [|r].\n  { %s. }\n'
                       % ('exfalso; lia' if r < lo else body(r)) for r in range(n))

    def sides(N0, STd, D, WLt, WRt, WL0, WR0):
        dd = dict(mid=mid, N0=N0, ST=STd, D=D, WLt=WLt, WRt=WRt, WL0=WL0, WR0=WR0)
        return SL % dd, SR % dd, SL0 % dd, SR0 % dd

    vm = lambda r: 'vm_compute; reflexivity'  # noqa: E731
    sl, sr, sl0, sr0 = sides(n0i, sti, 'd', '(digL mDL_%s d)' % mid, '(digR mDR_%s d)' % mid,
                             '(digL mDL_%s (S d))' % mid, '(digR mDR_%s (S d))' % mid)
    ibind = 'forall d r, d < 2 - 1 -> r < %d + %d ->' % (n0i, sti)
    iintro = 'intros d r Hd Hr. destruct d as [|d]; [|exfalso; lia].'
    for k, (h0n, q0, h0, h1n, q1, h1) in ((1, ('halfA', q, hs, 'halfA', qI, hI)),
                                         (2, ('halfB', qI, hI, 'halfB', q, hs))):
        L.append(ARMLEM % dict(nm='ai%d' % k, mid=mid, binder=ibind, el='false', er='false',
                               args='d r', intro=iintro,
                               sound=rb(n0i + sti, lambda r, k=k: reach('ai%d_0_%d' % (k, r))),
                               comp=rb(n0i + sti, vm), half0=h0n, half1=h1n, lf=lf,
                               q0=q0, h0=h0, q1=q1, h1=h1, sl=sl, sr=sr, sl0=sl0, sr0=sr0))
    sl, sr, sl0, sr0 = sides(n0t, stt, '0', 'msufL_%s' % mid, 'msufR_%s' % mid,
                             '(digL mDL_%s 1 ++ msufL_%s)' % (mid, mid),
                             '(digR mDR_%s 1 ++ msufR_%s)' % (mid, mid))
    tbind = 'forall r, 0 < r -> r < %d + %d ->' % (n0t, stt)
    for k, (h0n, q0, h0, h1n, q1, h1), (el_, er_) in (
            (1, ('halfA', q, hs, 'halfA', qT, hT), (lf, '(negb %s)' % lf)),
            (2, ('halfB', qT, hT, 'halfB', q, hs), ('(negb %s)' % lf, lf))):
        L.append(ARMLEM % dict(nm='at%d' % k, mid=mid, binder=tbind, el=el_, er=er_,
                               args='r', intro='intros r H0 Hr.',
                               sound=rb(n0t + stt, lambda r, k=k: reach('at%d_%d' % (k, r)), lo=1),
                               comp=rb(n0t + stt, vm, lo=1), half0=h0n, half1=h1n, lf=lf,
                               q0=q0, h0=h0, q1=q1, h1=h1, sl=sl, sr=sr, sl0=sl0, sr0=sr0))
    t0, x0 = cd['boot']

    def fv(i):
        return ''.join('  destruct r as [|r].\n  { %s }\n'
                       % ('exfalso; lia.' if r < 1 else
                          ('%s; vm_compute; reflexivity.'
                           % ('left' if how[(r, i)][0] == 1 else 'right')))
                       for r in range(n0t + stt))

    L.append(THM % dict(
        mid=mid, n0t=n0t, stt=stt, lf=lf, q=q, hs=hs,
        fvis=''.join('  - ' + fv((q_, s_)).lstrip() + '    exfalso; lia.\n'
                     for q_ in range(4) for s_ in range(2)
                     if (q_, s_) in cd['want']).rstrip('\n'),
        t0=t0, x0=clist(x0, str),
        tmb=('tm_%s' % mid) if E.TR_QH is not None else 'tm'))
    common = dict(mid=mid, n0i=n0i, sti=sti, n0t=n0t, stt=stt, x0=clist(x0, str),
                  t0=t0, q=q, hs=hs, lf=lf, qI=qI, hI=hI, qT=qT, hT=hT)
    args = ARGS % common
    if E.TR_QH is not None:
        L.append(QH % dict(mid=mid, t0=t0, call=CALL % dict(common, board='boardM_qhtr'),
                           args=args))
    else:
        L.append(NQH % dict(mid=mid, call=CALL % dict(common, board='boardM_neverqhtr'),
                            args=args))
    return ''.join(L), cd


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('spec')
    ap.add_argument('detect')
    ap.add_argument('-o', '--out', required=True)
    ap.add_argument('--qh', action='store_true')
    ap.add_argument('--scan', default=os.path.join(HERE, '..', '..', '..',
                                                   'censustr_v9_scan_1e8.txt'))
    args = ap.parse_args()
    det = None
    for l in open(args.detect):
        r = json.loads(l)
        if r['spec'] == args.spec and r.get('anchor'):
            det = r
    if det is None:
        raise SystemExit('%s: not a mirrored-counter row' % args.spec)
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
    boot = boot_of(spec, det, lastf)
    sp = det.get('split') or MS.split_of(spec, det)
    if sp is None:
        raise SystemExit('%s: no split of the increments on the anchor cell' % spec)
    if args.qh:
        E.TR_QH = boot[0]
    tab = E.parse_tm(spec)
    global RUN
    RUN = (det, tab, boot, sp)
    q, hs = det['anchor']
    cert = dict(spec=spec, ladder=[], arms=[],
                family=dict(base=2, digits=[[int(ch) for ch in w] for w in det['L']['words']],
                            near_head_prefix=[int(ch) for ch in det['L']['pre']],
                            terminator=[], terminators_by_phase=[[]], code='binary',
                            value_step_per_anchor_visit=1, state='ABCD'[q], head=hs,
                            side='L', other_side_cells=[]),
                fill=dict(widens_by=1, target_prefix=[], target_fill_digit=0,
                          target_suffix=[1], lands_in_phase=0))
    E.emit_closure = emit_closure_mirror
    good, bad, cd = E.emit(cert, args.out)
    print('%s: closure %s' % (args.out, 'BUILT' if cd else 'not built'))
    return 0 if cd else 1


if __name__ == '__main__':
    sys.exit(main())
