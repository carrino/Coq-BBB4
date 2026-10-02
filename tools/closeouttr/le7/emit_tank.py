#!/usr/bin/env python3
"""UNTRUSTED emitter (SCOPING_INSTR 7.4.LE7): a counter that widens into a
tank (`tank_detect.py`) -> a Coq board closed by [LadderCheckTankTr].

The machine, the header and the [Fam] record (digits, prefix, anchor, side)
are `emit_ladder.emit`'s; the closure has three arm classes, each a
[LadderNest] segment program found by LE3's arm search:

* interior `d r`: `t^r d X -> 0^r (d+1) X`, the rest of the counter opaque;
* widening `r > 0`: `t^r T X -> 0^r 1 X` (one tank word becomes the new digit);
* refill `r > 0`: `t^r suf -> z T^(r+a) suf`, both tails known empty.

The fires are read from every refill arm.

    python3 emit_tank.py SPEC DETECT.jsonl -o OUT.v [--qh]
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
                       coq_seg, clist, ST, SYM, _splits, Arms, nvisits, prog_coq,
                       inner_coq, ARM)
import tank_detect as KD  # noqa: E402
import fastsim  # noqa: E402


def cells(s):
    return tuple(int(ch) for ch in s)


def boot_of(spec, det, lastf, steps=600000):
    """(t, x, m) at the first anchor visit past lastf that reads"""
    q0, s0, side = det['anchor']
    tm = KD.TD.parse(spec)
    tape, h, q = {}, 0, 0
    for t in range(steps):
        s = tape.get(h, 0)
        if t > lastf and q == q0 and s == s0:
            cs = [i for i, v in tape.items() if v]
            st = None
            if side == 'R' and (not cs or min(cs) >= h):
                st = ''.join(str(tape.get(i, 0)) for i in range(h + 1, max(cs + [h]) + 1))
            elif side == 'L' and (not cs or max(cs) <= h):
                st = ''.join(str(tape.get(i, 0)) for i in range(h - 1, min(cs + [h]) - 1, -1))
            if st is not None:
                r = KD.read(st, det['pre'], det['l'], det['D'], det['F'], det['suf'])
                if r is not None and r[0]:
                    return t, r[0], r[1]
        w, d, nq = tm[(q, s)]
        tape[h] = w
        h += d
        q = nq
    raise NoClosure('no boot past %d' % lastf)


def closure_data(det, tab, boot):
    q, hs, side = det['anchor']
    left = side == 'L'
    OTHER = ((), (), 0, 0, ())
    pre, suf = cells(det['pre']), cells(det['suf'])
    D = [cells(w) for w in det['D']]
    T = cells(det['F'])
    z, a = det['refill'][0], det['refill'][1]
    if a < 0:
        raise NoClosure('refill tank length k%+d' % a)
    ZC = tuple(c for dg in z for c in D[dg])
    b = 2
    derive = Arms(tab).derive
    el, er = (not left), left

    def conf(sd):
        return (q, sd, hs, OTHER) if left else (q, OTHER, hs, sd)

    def inter_at(n0, st):
        got = []
        for d in range(b - 1):
            for r in range(n0 + st):
                s_ = 0 if r < n0 else st
                c0 = conf(blk(pre + D[b - 1] * r, D[b - 1], s_, D[d]))
                c1 = conf(blk(pre + D[0] * r, D[0], s_, D[d + 1]))
                try:
                    got.append((d, r, c0, c1, derive(el, er, c0, c1, 'interior d=%d r=%d' % (d, r))))
                except NoClosure:
                    return None
        return got

    def wid_at(n0, st):
        got = []
        for r in range(1, n0 + st):
            s_ = 0 if r < n0 else st
            c0 = conf(blk(pre + D[b - 1] * r, D[b - 1], s_, T))
            c1 = conf(blk(pre + D[0] * r, D[0], s_, D[1]))
            try:
                got.append((r, c0, c1, derive(el, er, c0, c1, 'widening r=%d' % r)))
            except NoClosure:
                return None
        return got

    def refill_at(n0, st):
        got = []
        for r in range(1, n0 + st):
            s_ = 0 if r < n0 else st
            c0 = conf(blk(pre + D[b - 1] * r, D[b - 1], s_, suf))
            hit = None
            for f1 in _splits(r + a):
                c1 = conf(blk(pre + ZC + T * f1, T, s_, T * (r + a - f1) + suf))
                try:
                    hit = (r, f1, r + a - f1, c0, c1, derive(True, True, c0, c1, 'refill r=%d' % r))
                    break
                except NoClosure:
                    continue
            if hit is None:
                return None
            got.append(hit)
        return got

    def first(fn, grid):
        for n0, st in grid:
            g = fn(n0, st)
            if g is not None:
                return g, n0, st
        raise NoClosure('%s: no program at any threshold and stride' % fn.__name__)

    inter, n0i, sti = first(inter_at, ARM_GRID)
    grid1 = [(n0, st) for n0, st in ARM_GRID if n0 >= 1]
    wid, n0w, stw = first(wid_at, grid1)
    want = [(q_, s_) for q_ in range(4) for s_ in range(2) if (q_, s_) not in E.TR_PINS]
    refill = None
    for n0, st in grid1:
        g = refill_at(n0, st)
        if g is None:
            continue
        seen = {r: nvisits(tab, want, c0, ch) for r, _f1, _f2, c0, _c1, ch in g}
        if all(i in seen[r] for r in seen for i in want):
            refill, n0r, str_ = g, n0, st
            nvis = {r: {i: seen[r][i] for i in want} for r in seen}
            break
    if refill is None:
        raise NoClosure('refill: no program, or an instruction a refill arm does not fire')
    return dict(nest=True, el=el, er=er, inter=inter, n0i=n0i, sti=sti, wid=wid, n0w=n0w,
                stw=stw, refill=refill, n0r=n0r, str=str_, nvis=nvis, want=want, a=a, z=z,
                T=T, suf=suf, boot=boot, fill=refill)


HEAD = '''
(** ** The closure: a counter that widens into a TANK ([LadderCheckTankTr])

    The counter side is [pre ++ x ++ T^m ++ suf], [x] binary over the two
    digit words, [T = %(Tw)s]: inside a width [x] counts; at its top [x]
    widens by a digit and the tank loses a word; with the tank empty the
    machine refills to [x = %(zs)s], [m = width + %(a)d].  Interior arms at
    threshold %(n0i)d stride %(sti)d, widening arms at %(n0w)d / %(stw)d,
    refill arms at %(n0r)d / %(str)d.  Every arm is a [LadderNest] segment
    program. *)
From BBB4.Checkers Require Import LadderCheckTankTr.

Definition tankz_%(mid)s : list nat := %(zc)s.
Definition tankT_%(mid)s : list Sym := %(Tc)s.
Definition tanksuf_%(mid)s : list Sym := %(sufc)s.

'''

THM = '''Lemma iarm_reach_%(mid)s : forall d r, d < fm_b FAM - 1 -> r < %(n0i)d + %(sti)d ->
  ReachL tm (negb (fm_left FAM)) (fm_left FAM) (lr_lhs (iarm_%(mid)s d r)) (lr_rhs (iarm_%(mid)s d r)).
Proof.
  intros d r Hd Hr. vm_compute in Hd. destruct d as [|d]; [|exfalso; lia].
%(isound)s  exfalso; lia.
Qed.

Lemma iarm_lhs_%(mid)s : forall d r, d < fm_b FAM - 1 -> r < %(n0i)d + %(sti)d ->
  lr_lhs (iarm_%(mid)s d r) = cls_conf FAM (blk (fm_pre FAM ++ rep (dig FAM (fm_b FAM - 1)) r)
    (dig FAM (fm_b FAM - 1)) (astride %(n0i)d %(sti)d r) (dig FAM d)).
Proof.
  intros d r Hd Hr. vm_compute in Hd. destruct d as [|d]; [|exfalso; lia].
%(icomp)s  exfalso; lia.
Qed.

Lemma iarm_rhs_%(mid)s : forall d r, d < fm_b FAM - 1 -> r < %(n0i)d + %(sti)d ->
  lr_rhs (iarm_%(mid)s d r) = cls_conf FAM (blk (fm_pre FAM ++ rep (dig FAM 0) r)
    (dig FAM 0) (astride %(n0i)d %(sti)d r) (dig FAM (S d))).
Proof.
  intros d r Hd Hr. vm_compute in Hd. destruct d as [|d]; [|exfalso; lia].
%(icomp)s  exfalso; lia.
Qed.

Lemma warm_reach_%(mid)s : forall r, 0 < r -> r < %(n0w)d + %(stw)d ->
  ReachL tm (negb (fm_left FAM)) (fm_left FAM) (lr_lhs (warm_%(mid)s r)) (lr_rhs (warm_%(mid)s r)).
Proof.
  intros r H0 Hr.
%(wsound)s  exfalso; lia.
Qed.

Lemma warm_lhs_%(mid)s : forall r, 0 < r -> r < %(n0w)d + %(stw)d ->
  lr_lhs (warm_%(mid)s r) = cls_conf FAM (blk (fm_pre FAM ++ rep (dig FAM (fm_b FAM - 1)) r)
    (dig FAM (fm_b FAM - 1)) (astride %(n0w)d %(stw)d r) tankT_%(mid)s).
Proof.
  intros r H0 Hr.
%(wcomp)s  exfalso; lia.
Qed.

Lemma warm_rhs_%(mid)s : forall r, 0 < r -> r < %(n0w)d + %(stw)d ->
  lr_rhs (warm_%(mid)s r) = cls_conf FAM (blk (fm_pre FAM ++ rep (dig FAM 0) r)
    (dig FAM 0) (astride %(n0w)d %(stw)d r) (dig FAM 1)).
Proof.
  intros r H0 Hr.
%(wcomp)s  exfalso; lia.
Qed.

Lemma rarm_reach_%(mid)s : forall r, 0 < r -> r < %(n0r)d + %(str)d ->
  ReachL tm true true (lr_lhs (rarm_%(mid)s r)) (lr_rhs (rarm_%(mid)s r)).
Proof.
  intros r H0 Hr.
%(rsound)s  exfalso; lia.
Qed.

Lemma rarm_lhs_%(mid)s : forall r, 0 < r -> r < %(n0r)d + %(str)d ->
  lr_lhs (rarm_%(mid)s r) = cls_conf FAM (blk (fm_pre FAM ++ rep (dig FAM (fm_b FAM - 1)) r)
    (dig FAM (fm_b FAM - 1)) (astride %(n0r)d %(str)d r) tanksuf_%(mid)s).
Proof.
  intros r H0 Hr.
%(rcomp)s  exfalso; lia.
Qed.

Lemma rarm_rhs_%(mid)s : forall r, 0 < r -> r < %(n0r)d + %(str)d ->
  lr_rhs (rarm_%(mid)s r) = cls_conf FAM (blk (fm_pre FAM ++ flat_map (dig FAM) tankz_%(mid)s
    ++ rep tankT_%(mid)s (fm1_%(mid)s r)) tankT_%(mid)s (astride %(n0r)d %(str)d r)
    (rep tankT_%(mid)s (fm2_%(mid)s r) ++ tanksuf_%(mid)s)).
Proof.
  intros r H0 Hr.
%(rcomp)s  exfalso; lia.
Qed.

Lemma fm_%(mid)s : forall r, 0 < r -> r < %(n0r)d + %(str)d ->
  fm1_%(mid)s r + fm2_%(mid)s r = r + %(a)d.
Proof.
  intros r H0 Hr.
%(rlia)s  exfalso; lia.
Qed.

Lemma vis_ok_%(mid)s : forall t, ~ In t pins_%(mid)s -> forall r, 0 < r -> r < %(n0r)d + %(str)d ->
  nfire tm true true nrules (vsegs_%(mid)s r t) (vis_%(mid)s r t) (lr_lhs (rarm_%(mid)s r)) = Some t.
Proof.
  intros t Hnp. destruct t as [q s]; destruct q, s; try (exfalso; apply Hnp; simpl; tauto);
  intros r H0 Hr.
%(fvis)s
Qed.

Lemma bootl_%(mid)s :
  stepn %(tmb)s %(t0)d InitES = Some (lift (kcfg FAM tankT_%(mid)s tanksuf_%(mid)s (%(x0)s, %(m0)d))).
Proof.
  assert (H : match csteps %(tmb)s %(t0)d c0 with
              | Some c => ceqb c (kcfg FAM tankT_%(mid)s tanksuf_%(mid)s (%(x0)s, %(m0)d))
              | None => false end = true) by (vm_compute; reflexivity).
  destruct (csteps %(tmb)s %(t0)d c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

'''

ARGS = '''  - vm_compute; lia.
  - repeat constructor.
  - discriminate.
  - repeat constructor.
  - discriminate.
  - lia.
  - exact iarm_reach_%(mid)s.
  - exact iarm_lhs_%(mid)s.
  - exact iarm_rhs_%(mid)s.
  - lia.
  - lia.
  - exact warm_reach_%(mid)s.
  - exact warm_lhs_%(mid)s.
  - exact warm_rhs_%(mid)s.
  - lia.
  - lia.
  - exact rarm_reach_%(mid)s.
  - exact rarm_lhs_%(mid)s.
  - exact rarm_rhs_%(mid)s.
  - exact fm_%(mid)s.
  - exact nrules_sound_%(mid)s.
  - exact vis_ok_%(mid)s.
  - exact bootl_%(mid)s.
'''

CALL = '''(%(board)s tm_%(mid)s pins_%(mid)s FAM tankT_%(mid)s tanksuf_%(mid)s %(a)d tankz_%(mid)s
                 iarm_%(mid)s %(n0i)d %(sti)d warm_%(mid)s %(n0w)d %(stw)d
                 rarm_%(mid)s %(n0r)d %(str)d fm1_%(mid)s fm2_%(mid)s
                 nrules vsegs_%(mid)s vis_%(mid)s %(x0)s %(m0)d)'''

NQH = '''(** The machine-level theorem, at the INSTRUCTION level, through
    [LadderCheckTankTr.boardK_neverqhtr]. *)
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
    [LadderCheckTankTr.boardK_qhtr]. *)
Theorem qhtr_%(mid)s :
  NonHalt tm_%(mid)s /\\ QHBoundTr 32779478 tm_%(mid)s /\\ QuasiHaltsTr tm_%(mid)s.
Proof.
  eapply %(call)s.
%(args)s  - exact wit_%(mid)s.
  - exact bnd_%(mid)s.
Qed.
'''

TABLES = '''Definition iarm_%(mid)s (d r : nat) : LRule :=
  match d, r with %(ib)s | _, _ => iarm0_0_0_%(mid)s end.
Definition warm_%(mid)s (r : nat) : LRule :=
  match r with %(wb)s | _ => warm%(w1)d_%(mid)s end.
Definition rarm_%(mid)s (r : nat) : LRule :=
  match r with %(rb)s | _ => rarm%(r1)d_%(mid)s end.
Definition fm1_%(mid)s (r : nat) : nat := match r with %(b1)s | _ => 0 end.
Definition fm2_%(mid)s (r : nat) : nat := match r with %(b2)s | _ => 0 end.

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

'''


def syms(c):
    return '[' + ';'.join('S%d' % x for x in c) + ']'


RUN = None


def emit_closure_tank(cert, tab, mid):
    cd = S.two_pass(lambda _c, _t: closure_data(*RUN), cert, tab)
    if isinstance(cd, NoClosure):
        return E.CLOSURE_NONE % cd, None
    n0i, sti, n0w, stw = cd['n0i'], cd['sti'], cd['n0w'], cd['stw']
    n0r, str_ = cd['n0r'], cd['str']
    a, el, er = cd['a'], cd['el'], cd['er']
    L = [HEAD % dict(mid=mid, Tw=''.join(map(str, cd['T'])), zs=clist(cd['z'], str), a=a,
                     n0i=n0i, sti=sti, n0w=n0w, stw=stw, n0r=n0r, str=str_,
                     zc=clist(cd['z'], str), Tc=syms(cd['T']), sufc=syms(cd['suf']))]
    inner, arms = [], []
    for d, r, c0, c1, ch in cd['inter']:
        arms.append(('iarm0_%d_%d' % (d, r), c0, c1, prog_coq(tab, inner, ch), el, er))
    for r, c0, c1, ch in cd['wid']:
        arms.append(('warm%d' % r, c0, c1, prog_coq(tab, inner, ch), el, er))
    offs = {}
    for r, _f1, _f2, c0, c1, ch in cd['refill']:
        offs[r] = len(inner)
        arms.append(('rarm%d' % r, c0, c1, prog_coq(tab, inner, ch), True, True))
    L.append(inner_coq(mid, inner))
    for nm, c0, c1, segs, el_, er_ in arms:
        L.append(ARM % dict(nm=nm, mid=mid, lhs=coq_conf(c0), rhs=coq_conf(c1),
                            segs=';\n   '.join(segs), el=str(el_).lower(), er=str(er_).lower()))
    nv = cd['nvis']
    L.append(TABLES % dict(
        mid=mid, w1=cd['wid'][0][0], r1=cd['refill'][0][0],
        ib=' '.join('| %d, %d => iarm0_%d_%d_%s' % (d, r, d, r, mid) for d, r, *_ in cd['inter']),
        wb=' '.join('| %d => warm%d_%s' % (r, r, mid) for r, *_ in cd['wid']),
        rb=' '.join('| %d => rarm%d_%s' % (r, r, mid) for r, *_ in cd['refill']),
        b1=' '.join('| %d => %d' % (r, f1) for r, f1, *_ in cd['refill']),
        b2=' '.join('| %d => %d' % (r, f2) for r, _f1, f2, *_ in cd['refill']),
        vb='\n  '.join('| %d, (%s, %s) => %s' % (r, ST[i[0]], SYM[i[1]], coq_chain_l(v[1]))
                       for r in sorted(nv) for i, v in sorted(nv[r].items())),
        sb='\n  '.join('| %d, (%s, %s) => [%s]'
                       % (r, ST[i[0]], SYM[i[1]], '; '.join(coq_seg(sg, offs[r]) for sg in v[0]))
                       for r in sorted(nv) for i, v in sorted(nv[r].items()))))

    def reach(nm):
        return ('eapply narm_reach; [exact nrules_sound_%s | exact ok_%s_%s]' % (mid, nm, mid))

    def rb(n, body, lo=0):
        return ''.join('  destruct r as [|r].\n  { %s. }\n'
                       % ('exfalso; lia' if r < lo else body(r)) for r in range(n))

    vm = lambda r: 'vm_compute; reflexivity'  # noqa: E731
    t0, x0, m0 = cd['boot']
    L.append(THM % dict(
        mid=mid, n0i=n0i, sti=sti, n0w=n0w, stw=stw, n0r=n0r, str=str_, a=a,
        isound=rb(n0i + sti, lambda r: reach('iarm0_0_%d' % r)),
        icomp=rb(n0i + sti, vm),
        wsound=rb(n0w + stw, lambda r: reach('warm%d' % r), lo=1),
        wcomp=rb(n0w + stw, vm, lo=1),
        rsound=rb(n0r + str_, lambda r: reach('rarm%d' % r), lo=1),
        rcomp=rb(n0r + str_, vm, lo=1),
        rlia=rb(n0r + str_, lambda r: 'vm_compute; lia', lo=1),
        fvis=''.join('  - ' + rb(n0r + str_, vm, lo=1).lstrip() + '    exfalso; lia.\n'
                     for q_ in range(4) for s_ in range(2)
                     if (q_, s_) in cd['want']).rstrip('\n'),
        t0=t0, x0=clist(x0, str), m0=m0,
        tmb=('tm_%s' % mid) if E.TR_QH is not None else 'tm'))
    common = dict(mid=mid, a=a, n0i=n0i, sti=sti, n0w=n0w, stw=stw, n0r=n0r, str=str_,
                  x0=clist(x0, str), m0=m0, t0=t0)
    args = ARGS % common
    if E.TR_QH is not None:
        L.append(QH % dict(mid=mid, t0=t0, call=CALL % dict(common, board='boardK_qhtr'),
                           args=args))
    else:
        L.append(NQH % dict(mid=mid, call=CALL % dict(common, board='boardK_neverqhtr'),
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
        raise SystemExit('%s: not a tank row' % args.spec)
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
    if args.qh:
        E.TR_QH = boot[0]
    tab = E.parse_tm(spec)
    global RUN
    RUN = (det, tab, boot)
    q, hs, side = det['anchor']
    cert = dict(spec=spec, ladder=[], arms=[],
                family=dict(base=2, digits=[[int(ch) for ch in w] for w in det['D']],
                            near_head_prefix=[int(ch) for ch in det['pre']],
                            terminator=[], terminators_by_phase=[[]], code='binary',
                            value_step_per_anchor_visit=1, state='ABCD'[q], head=hs,
                            side=side, other_side_cells=[]),
                fill=dict(widens_by=1, target_prefix=[], target_fill_digit=0,
                          target_suffix=[1], lands_in_phase=0))
    E.emit_closure = emit_closure_tank
    good, bad, cd = E.emit(cert, args.out)
    print('%s: closure %s' % (args.out, 'BUILT' if cd else 'not built'))
    return 0 if cd else 1


if __name__ == '__main__':
    sys.exit(main())
