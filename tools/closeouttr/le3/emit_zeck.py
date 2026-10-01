#!/usr/bin/env python3
"""UNTRUSTED emitter: a valfam certificate whose numeration is Zeckendorf
("fibonacci(shifted)": weights 1, 2, 3, 5, ..., no two adjacent ones) -> a
Coq board closed by [LadderCheckZeckTr] (SCOPING_INSTR 7.4.LE3).

The family's digit words, prefix, terminator and anchor come from the
certificate; the arms are the three classes of [LadderCheckZeckTr] in two
kinds each ([u] = [] or [1]), over the two-digit word [01]:

  interior  u (01)^k 0 0 X -> 0^|u| (00)^k 1 0 X       (X opaque)
  end       u (01)^k 0 T   -> 0^|u| (00)^k 1 T
  top       u (01)^k T     -> 0^|u| (00)^k 0 T

with emit_step's arm search; the visits are from the top arms' anchors.

    python3 emit_zeck.py CERT.json -o OUT.v [--qh]
"""
import argparse
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import emit_step as S  # noqa: E402
from emit_step import (E, NoClosure, blk, ARM_GRID, coq_conf, coq_chain_l,  # noqa: E402
                       coq_seg, clist, ST, SYM, Arms, nvisits, prog_coq,
                       inner_coq, ARM, BOOTL, _rstrip0)


def zok(x):
    return all(d < 2 for d in x) and all(not (a == 1 and b == 1) for a, b in zip(x, x[1:]))


def closure_data_zeck(cert, tab):
    fam = cert['family']
    if fam.get('numeration') != 'fibonacci(shifted)' or fam['base'] != 2:
        raise NoClosure('numeration %s: LadderCheckZeckTr is Zeckendorf over two words'
                        % fam.get('numeration'))
    if fam.get('value_step_per_anchor_visit', 1) != 1:
        raise NoClosure('step %d' % fam['value_step_per_anchor_visit'])
    tails = fam.get('terminators_by_phase') or [fam['terminator']]
    if len(tails) != 1:
        raise NoClosure('%d phases: LadderCheckZeckTr has one' % len(tails))
    D0, D1 = (tuple(w) for w in fam['digits'])
    pre = tuple(fam['near_head_prefix'])
    T = tuple(tails[0])
    boot = cert['boot']
    x0 = list(boot['digits_lsb_first'])
    if not x0 or not zok(x0):
        raise NoClosure('boot %r is not a Zeckendorf string' % x0)
    cells = list(pre) + [c for d in x0 for c in (D0, D1)[d]] + list(T)
    if _rstrip0(cells) != _rstrip0(boot['cells']):
        raise NoClosure('boot cells %r are not the family at %r' % (boot['cells'], x0))
    other = tuple(fam['other_side_cells'])
    q = ord(fam['state']) - 65
    hs = fam['head']
    left = fam['side'] == 'L'
    OTHER = (other, (), 0, 0, ())

    def conf(sd):
        return (q, sd, hs, OTHER) if left else (q, OTHER, hs, sd)

    derive = Arms(tab).derive
    el, er = (not left), left
    W01, W00 = D0 + D1, D0 + D0
    U = {0: (), 1: D1}
    U0 = {0: (), 1: D0}

    def grid_arms(kind, n0, st):
        got = []
        for i in (0, 1):
            for r in range(n0 + st):
                if kind == 'T' and i == 0 and r == 0:
                    continue
                s_ = 0 if r < n0 else st
                lp = pre + U[i] + W01 * r
                rp = pre + U0[i] + W00 * r
                if kind == 'I':
                    c0, c1 = conf(blk(lp, W01, s_, D0 + D0)), conf(blk(rp, W00, s_, D1 + D0))
                    e = (el, er)
                elif kind == 'E':
                    c0, c1 = conf(blk(lp, W01, s_, D0 + T)), conf(blk(rp, W00, s_, D1 + T))
                    e = (True, True)
                else:
                    c0, c1 = conf(blk(lp, W01, s_, T)), conf(blk(rp, W00, s_, D0 + T))
                    e = (True, True)
                try:
                    got.append((i, r, c0, c1, derive(e[0], e[1], c0, c1,
                                                     '%s arm i=%d r=%d' % (kind, i, r))))
                except NoClosure:
                    return None
        return got

    def first(kind, grid):
        for n0, st in grid:
            g = grid_arms(kind, n0, st)
            if g is not None:
                return g, n0, st
        raise NoClosure('%s arm: no program at any threshold and stride' % kind)

    inter, n0i, sti = first('I', ARM_GRID)
    endc, n0e, ste = first('E', ARM_GRID)
    want = [(q_, s_) for q_ in range(4) for s_ in range(2)
            if (q_, s_) not in E.TR_PINS]
    top = nvis = None
    for n0, st in [(n0, st) for n0, st in ARM_GRID if n0 >= 1]:
        g = grid_arms('T', n0, st)
        if g is None:
            continue
        seen = {(i, r): nvisits(tab, want, c0, ch) for i, r, c0, _c1, ch in g}
        if all(w in seen[k] for k in seen for w in want):
            top, n0t, stt = g, n0, st
            nvis = {k: {w: seen[k][w] for w in want} for k in seen}
            break
    if top is None:
        raise NoClosure('top arm: no program, or an instruction no top anchor fires')
    return dict(nest=True, el=el, er=er, inter=inter, n0i=n0i, sti=sti,
                endc=endc, n0e=n0e, ste=ste, top=top, n0t=n0t, stt=stt,
                nvis=nvis, x0=x0, t0=boot['steps_from_blank'],
                fill=top)  # emit_ladder's report line


HEAD = '''
(** ** The closure: a ZECKENDORF counter ([LadderCheckZeckTr])

    Weights 1, 2, 3, 5, ..., no two adjacent ones.  Interior arms at
    threshold %(n0i)d stride %(sti)d, end arms at %(n0e)d / %(ste)d, top arms
    at %(n0t)d / %(stt)d, each in the two kinds of the alternating prefix.
    Every arm is a [LadderNest] segment program. *)
From BBB4.Checkers Require Import LadderCheckZeckTr.

'''

THM = '''Lemma iarm_reach_%(mid)s : forall i r, i < 2 -> r < %(n0i)d + %(sti)d ->
  ReachL tm (negb (fm_left FAM)) (fm_left FAM) (lr_lhs (iarm_%(mid)s i r)) (lr_rhs (iarm_%(mid)s i r)).
Proof. intros i r Hi Hr.
%(isound)s  exfalso; lia.
Qed.

Lemma iarm_lhs_%(mid)s : forall i r, i < 2 -> r < %(n0i)d + %(sti)d ->
  lr_lhs (iarm_%(mid)s i r) = cls_conf FAM (cls_sideW FAM (zu i) [0;1] r (astride %(n0i)d %(sti)d r) [0;0]).
Proof. intros i r Hi Hr.
%(icomp)s  exfalso; lia.
Qed.

Lemma iarm_rhs_%(mid)s : forall i r, i < 2 -> r < %(n0i)d + %(sti)d ->
  lr_rhs (iarm_%(mid)s i r) = cls_conf FAM (cls_sideW FAM (zu0 i) [0;0] r (astride %(n0i)d %(sti)d r) [1;0]).
Proof. intros i r Hi Hr.
%(icomp)s  exfalso; lia.
Qed.

Lemma earm_reach_%(mid)s : forall i r, i < 2 -> r < %(n0e)d + %(ste)d ->
  ReachL tm true true (lr_lhs (earm_%(mid)s i r)) (lr_rhs (earm_%(mid)s i r)).
Proof. intros i r Hi Hr.
%(esound)s  exfalso; lia.
Qed.

Lemma earm_lhs_%(mid)s : forall i r, i < 2 -> r < %(n0e)d + %(ste)d ->
  lr_lhs (earm_%(mid)s i r) = cls_conf FAM (run_sideW FAM [0;1] r (astride %(n0e)d %(ste)d r) 0 0 (zu i) [0]).
Proof. intros i r Hi Hr.
%(ecomp)s  exfalso; lia.
Qed.

Lemma earm_rhs_%(mid)s : forall i r, i < 2 -> r < %(n0e)d + %(ste)d ->
  lr_rhs (earm_%(mid)s i r) = cls_conf FAM (run_sideW FAM [0;0] r (astride %(n0e)d %(ste)d r) 0 0 (zu0 i) [1]).
Proof. intros i r Hi Hr.
%(ecomp)s  exfalso; lia.
Qed.

Lemma tarm_reach_%(mid)s : forall i r, i < 2 -> r < %(n0t)d + %(stt)d -> (i = 0 -> 0 < r) ->
  ReachL tm true true (lr_lhs (tarm_%(mid)s i r)) (lr_rhs (tarm_%(mid)s i r)).
Proof. intros i r Hi Hr H0.
%(tsound)s  exfalso; lia.
Qed.

Lemma tarm_lhs_%(mid)s : forall i r, i < 2 -> r < %(n0t)d + %(stt)d -> (i = 0 -> 0 < r) ->
  lr_lhs (tarm_%(mid)s i r) = cls_conf FAM (run_sideW FAM [0;1] r (astride %(n0t)d %(stt)d r) 0 0 (zu i) []).
Proof. intros i r Hi Hr H0.
%(tcomp)s  exfalso; lia.
Qed.

Lemma tarm_rhs_%(mid)s : forall i r, i < 2 -> r < %(n0t)d + %(stt)d -> (i = 0 -> 0 < r) ->
  lr_rhs (tarm_%(mid)s i r) = cls_conf FAM (run_sideW FAM [0;0] r (astride %(n0t)d %(stt)d r) 0 0 (zu0 i) [0]).
Proof. intros i r Hi Hr H0.
%(tcomp)s  exfalso; lia.
Qed.

Lemma vis_ok_%(mid)s : forall i r t, ~ In t pins_%(mid)s -> i < 2 -> r < %(n0t)d + %(stt)d ->
  (i = 0 -> 0 < r) ->
  nfire tm true true nrules (vsegs_%(mid)s i r t) (vis_%(mid)s i r t) (lr_lhs (tarm_%(mid)s i r)) = Some t.
Proof. intros i r t Hnp Hi Hr H0.
%(fvis)s  exfalso; lia.
Qed.

Lemma bootl_%(mid)s :
  stepn %(tmb)s %(t0)d InitES = Some (lift (fam_cfg FAM (%(x0)s, 0, 0))).
Proof.
  assert (H : match csteps %(tmb)s %(t0)d c0 with
              | Some c => ceqb c (fam_cfg FAM (%(x0)s, 0, 0))
              | None => false end = true) by (vm_compute; reflexivity).
  destruct (csteps %(tmb)s %(t0)d c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

'''

ARGS = '''  - vm_compute; reflexivity.
  - vm_compute; lia.
  - lia.
  - exact iarm_reach_%(mid)s.
  - exact iarm_lhs_%(mid)s.
  - exact iarm_rhs_%(mid)s.
  - lia.
  - exact earm_reach_%(mid)s.
  - exact earm_lhs_%(mid)s.
  - exact earm_rhs_%(mid)s.
  - lia.
  - lia.
  - exact tarm_reach_%(mid)s.
  - exact tarm_lhs_%(mid)s.
  - exact tarm_rhs_%(mid)s.
  - exact nrules_sound_%(mid)s.
  - exact vis_ok_%(mid)s.
  - exact bootl_%(mid)s.
'''

CALL = '''(%(board)s tm_%(mid)s pins_%(mid)s FAM
                 iarm_%(mid)s %(n0i)d %(sti)d earm_%(mid)s %(n0e)d %(ste)d
                 tarm_%(mid)s %(n0t)d %(stt)d nrules vsegs_%(mid)s vis_%(mid)s %(x0)s)'''

NQH = '''Theorem nqhtr_%(mid)s : NeverQuasiHaltsTr tm_%(mid)s.
Proof.
  eapply %(call)s.
%(args)sQed.
'''

QH = '''Lemma wit_%(mid)s :
  existsb (fun tg => cfires tm_%(mid)s c0 %(t0)d tg) pins_%(mid)s = true.
Proof. vm_compute. reflexivity. Qed.

Lemma bnd_%(mid)s : (%(t0)d <=? 32779478) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Theorem qhtr_%(mid)s :
  NonHalt tm_%(mid)s /\\ QHBoundTr 32779478 tm_%(mid)s /\\ QuasiHaltsTr tm_%(mid)s.
Proof.
  eapply %(call)s.
%(args)s  - exact wit_%(mid)s.
  - exact bnd_%(mid)s.
Qed.
'''


def emit_closure_zeck(cert, tab, mid):
    cd = S.two_pass(closure_data_zeck, cert, tab)
    if isinstance(cd, NoClosure):
        return E.CLOSURE_NONE % cd, None
    n0i, sti, n0e, ste, n0t, stt = (cd[k] for k in ('n0i', 'sti', 'n0e', 'ste', 'n0t', 'stt'))
    el, er = cd['el'], cd['er']
    L = [HEAD % dict(n0i=n0i, sti=sti, n0e=n0e, ste=ste, n0t=n0t, stt=stt)]
    inner, arms = [], []
    for nm, grp, e in (('iarm', cd['inter'], (el, er)), ('earm', cd['endc'], (True, True))):
        for i, r, c0, c1, ch in grp:
            arms.append(('%s%d_%d' % (nm, i, r), c0, c1, prog_coq(tab, inner, ch)) + e)
    offs = {}
    for i, r, c0, c1, ch in cd['top']:
        offs[(i, r)] = len(inner)
        arms.append(('tarm%d_%d' % (i, r), c0, c1, prog_coq(tab, inner, ch), True, True))
    L.append(inner_coq(mid, inner))
    for nm, c0, c1, segs, el_, er_ in arms:
        L.append(ARM % dict(nm=nm, mid=mid, lhs=coq_conf(c0), rhs=coq_conf(c1),
                            segs=';\n   '.join(segs), el=str(el_).lower(),
                            er=str(er_).lower()))

    def disp(nm, grp):
        i0, r0 = grp[0][:2]
        return ('Definition %s_%s (i r : nat) : LRule :=\n  match i, r with %s | _, _ => %s%d_%d_%s end.\n'
                % (nm, mid, ' '.join('| %d, %d => %s%d_%d_%s' % (i, r, nm, i, r, mid)
                                      for i, r, *_ in grp), nm, i0, r0, mid))
    L.append(disp('iarm', cd['inter']) + disp('earm', cd['endc']) + disp('tarm', cd['top']))
    L.append('''
Definition vis_%(mid)s (i r : nat) (t : Instr) : list lstep :=
  match i, r, t with
  %(vb)s
  | _, _, _ => []
  end.

Definition vsegs_%(mid)s (i r : nat) (t : Instr) : list nseg :=
  match i, r, t with
  %(sb)s
  | _, _, _ => []
  end.

''' % dict(mid=mid,
           vb='\n  '.join('| %d, %d, (%s, %s) => %s' % (k[0], k[1], ST[w[0]], SYM[w[1]], coq_chain_l(v[1]))
                          for k in sorted(cd['nvis']) for w, v in sorted(cd['nvis'][k].items())),
           sb='\n  '.join('| %d, %d, (%s, %s) => [%s]'
                          % (k[0], k[1], ST[w[0]], SYM[w[1]],
                             '; '.join(coq_seg(sg, offs[k]) for sg in v[0]))
                          for k in sorted(cd['nvis']) for w, v in sorted(cd['nvis'][k].items()))))

    def br(n, body, skip=lambda i, r: False):
        out = []
        for i in (0, 1):
            rb = []
            for r in range(n):
                rb.append('    destruct r as [|r].\n    { %s. }\n'
                          % ('exfalso; specialize (H0 eq_refl); lia' if skip(i, r)
                             else body(i, r)))
            out.append('  destruct i as [|i].\n  {\n%s    exfalso; lia.\n  }\n' % ''.join(rb))
        return ''.join(out)

    def reach(nm):
        return lambda i, r: ('eapply narm_reach; [exact nrules_sound_%s | exact ok_%s%d_%d_%s]'
                             % (mid, nm, i, r, mid))
    vm = lambda i, r: 'vm_compute; reflexivity'  # noqa: E731
    sk = lambda i, r: i == 0 and r == 0  # noqa: E731
    fv = lambda i, r: ('destruct t as [q s]; destruct q, s; try (exfalso; apply Hnp; simpl; tauto); '
                       'vm_compute; reflexivity')  # noqa: E731
    sk0 = '    destruct r as [|r].\n    { exfalso; lia. }\n'
    t0 = cd['t0']
    L.append(THM % dict(
        mid=mid, n0i=n0i, sti=sti, n0e=n0e, ste=ste, n0t=n0t, stt=stt,
        isound=br(n0i + sti, reach('iarm')), icomp=br(n0i + sti, vm),
        esound=br(n0e + ste, reach('earm')), ecomp=br(n0e + ste, vm),
        tsound=br(n0t + stt, reach('tarm'), sk), tcomp=br(n0t + stt, vm, sk),
        fvis=br(n0t + stt, fv, sk),
        t0=t0, x0=clist(cd['x0'], str),
        tmb=('tm_%s' % mid) if E.TR_QH is not None else 'tm'))
    common = dict(mid=mid, n0i=n0i, sti=sti, n0e=n0e, ste=ste, n0t=n0t, stt=stt,
                  x0=clist(cd['x0'], str), t0=t0)
    args = ARGS % common
    if E.TR_QH is not None:
        L.append(QH % dict(mid=mid, t0=t0, args=args, call=CALL % dict(common, board='boardZ_qhtr')))
    else:
        L.append(NQH % dict(mid=mid, args=args, call=CALL % dict(common, board='boardZ_neverqhtr')))
    return ''.join(L), cd


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
    E.emit_closure = emit_closure_zeck
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
    good, bad, cd = E.emit(cert, args.out)
    print('%s: closure %s' % (args.out, 'BUILT' if cd else 'not built'))
    return 0 if cd else 1


if __name__ == '__main__':
    sys.exit(main())
