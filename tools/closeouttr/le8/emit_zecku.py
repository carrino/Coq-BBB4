#!/usr/bin/env python3
"""UNTRUSTED emitter: a `zecku_detect.py` certificate (a Zeckendorf string that
counts UP inside a fixed width and overflows to zero `2 dh` digits wider;
tokens 0 -> A, 10 -> B) -> a Coq board closed by [LadderCheckZeckUTr]
(SCOPING_INSTR 7.4.LE8).

The counter side at the anchor is `pre ++ tcells tau ++ T` for a token list
tau (false = A, true = B); the arms are [LadderCheckZeckUTr]'s three classes
(PL 0 = [], PL 1 = A, PR 0 = A, PR 1 = B; u0 the overflow kind, ue = 1 - u0):

  interior  PR u B^k A X   -> PL u (AA)^k B X               (X opaque; u = 0, 1)
  end       PR ue B^k A T  -> PL ue (AA)^k B T
  overflow  PR u0 B^k T    -> PL (1 - u0) (AA)^(k + dh + u0) T

with emit_step's arm search (LE6's `emit_zeckd.py`, the classes changed);
the visits are from the overflow arms' anchors.

    python3 emit_zecku.py CERT.json -o OUT.v [--qh]
"""
import argparse
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'le3'))
sys.path.insert(0, os.path.join(HERE, '..', 'le4'))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, '..', 'le6'))
import emit_step as S  # noqa: E402
from emit_step import (E, NoClosure, blk, ARM_GRID, coq_conf, coq_chain_l,  # noqa: E402
                       coq_seg, clist, ST, SYM, Arms, nvisits, prog_coq,
                       inner_coq, ARM, BOOTL, _rstrip0)


from zeckw_detect import zw  # noqa: E402
from zecku_detect import find_after  # noqa: E402


def tokens(x):
    """the token list of the digit string x ++ [0] (false = 0, true = 10)"""
    y, out, i = list(x) + [0], [], 0
    while i < len(y):
        if y[i] == 0:
            out.append(False); i += 1
        else:
            out.append(True); i += 2
    return out


def ovf_tokens(ovf):
    """the overflow of a zecku_detect mode as [LadderCheckZeckUTr]'s (a, w)"""
    if ovf[0] == 'reset':
        return 1 + ovf[1], []
    if ovf[0] == 'pad':
        return 0, [True] + [False] * ovf[1]
    raise NoClosure('overflow mode %r' % (ovf,))


def closure_data_zeck(cert, tab):
    fam = cert['family']
    if fam.get('numeration') != 'zecku':
        raise NoClosure('numeration %s: LadderCheckZeckUTr is the fixed-width Zeckendorf count up'
                        % fam.get('numeration'))
    pre = tuple(fam['near_head_prefix'])
    T = tuple(fam['terminator'])
    A, B = tuple(fam['zA']), tuple(fam['zB'])
    boot = cert['boot']
    x0 = list(boot['digits_lsb_first'])
    tau = tokens(x0)
    cells = list(pre) + zw(x0 + [0], list(A), list(B)) + list(T)
    if _rstrip0(cells) != _rstrip0(boot['cells']):
        raise NoClosure('boot cells %r are not the family at %r' % (boot['cells'], x0))
    # the overflow alt i -> false^(i + a) ++ w, in tokens
    a, w = ovf_tokens(cert['ovf'])
    nd = a + sum(2 if b else 1 for b in w)
    if nd % 2 != 1:
        raise NoClosure('overflow %r adds an odd number of digits: no checker' % (cert['ovf'],))
    dh = (nd - 1) // 2
    # the digit count of tau is len(x0) + 1 = u0 + 1 (mod 2)
    u0 = len(x0) % 2
    ue = 1 - u0
    po, co = (u0 + a) % 2, (u0 + a) // 2
    W = tuple(c for b in w for c in (B if b else A))
    other = tuple(fam['other_side_cells'])
    q = ord(fam['state']) - 65
    hs = fam['head']
    left = fam['side'] == 'L'
    OTHER = (other, (), 0, 0, ())

    def conf(sd):
        return (q, sd, hs, OTHER) if left else (q, OTHER, hs, sd)

    derive = Arms(tab).derive
    el, er = (not left), left
    AA = A + A
    PL = {0: (), 1: A}
    PR = {0: A, 1: B}

    def grid_arms(kind, n0, st):
        got = []
        kinds = (0, 1) if kind == 'I' else ((ue,) if kind == 'E' else (u0,))
        for i in kinds:
            for r in range(n0 + st):
                s_ = 0 if r < n0 else st
                lp = pre + PR[i] + B * r
                rp = pre + PL[i] + AA * r
                if kind == 'I':
                    c0, c1 = conf(blk(lp, B, s_, A)), conf(blk(rp, AA, s_, B))
                    e = (el, er)
                elif kind == 'E':
                    c0, c1 = conf(blk(lp, B, s_, A + T)), conf(blk(rp, AA, s_, B + T))
                    e = (True, True)
                else:
                    c0 = conf(blk(lp, B, s_, T))
                    c1 = conf(blk(pre + PL[po] + AA * (r + co), AA, s_, W + T))
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
    for n0, st in ARM_GRID:
        g = grid_arms('T', n0, st)
        if g is None:
            continue
        seen = {r: nvisits(tab, want, c0, ch) for i, r, c0, _c1, ch in g}
        if all(w in seen[k] for k in seen for w in want):
            top, n0t, stt = g, n0, st
            nvis = {k: {w: seen[k][w] for w in want} for k in seen}
            break
    if top is None:
        raise NoClosure('overflow arm: no program, or an instruction no overflow anchor fires')
    return dict(nest=True, el=el, er=er, inter=inter, n0i=n0i, sti=sti,
                endc=endc, n0e=n0e, ste=ste, top=top, n0t=n0t, stt=stt,
                nvis=nvis, tau=tau, t0=boot['steps_from_blank'], T=T, A=A, B=B,
                u0=u0, ue=ue, dh=dh, a=a, w=w, po=po, co=co,
                fill=top)  # emit_ladder's report line


HEAD = '''
(** ** The closure: a fixed-width ZECKENDORF COUNT UP over two token words ([LadderCheckZeckUTr])

    Tokens [0 -> ZA], [10 -> ZB]; overflow kind %(u0)d, [alt i -> false^(i + %(a)d) ++ ZW]
    (2 * %(dh)d digits wider).
    Interior arms at threshold %(n0i)d stride %(sti)d (two kinds), end arms
    at %(n0e)d / %(ste)d, overflow arms at %(n0t)d / %(stt)d.  Every arm is a
    [LadderNest] segment program. *)
From BBB4.Checkers Require Import LadderCheckZeckDTr LadderCheckZeckUTr.

Definition zt_%(mid)s : list Sym := %(T)s.
Local Notation ZT := zt_%(mid)s.
Definition za_%(mid)s : list Sym := %(A)s.
Local Notation ZA := za_%(mid)s.
Definition zb_%(mid)s : list Sym := %(B)s.
Local Notation ZB := zb_%(mid)s.
Definition zw_%(mid)s : list bool := %(w)s.
Local Notation ZW := zw_%(mid)s.

'''

THM = '''Lemma iarm_reach_%(mid)s : forall i r, i < 2 -> r < %(n0i)d + %(sti)d ->
  ReachL tm (negb (fm_left FAM)) (fm_left FAM) (lr_lhs (iarm_%(mid)s i r)) (lr_rhs (iarm_%(mid)s i r)).
Proof. intros i r Hi Hr.
%(isound)s  exfalso; lia.
Qed.

Lemma iarm_lhs_%(mid)s : forall i r, i < 2 -> r < %(n0i)d + %(sti)d ->
  lr_lhs (iarm_%(mid)s i r) = cls_conf FAM (zdside FAM (zdPR ZA ZB i) ZB r (astride %(n0i)d %(sti)d r) ZA).
Proof. intros i r Hi Hr.
%(icomp)s  exfalso; lia.
Qed.

Lemma iarm_rhs_%(mid)s : forall i r, i < 2 -> r < %(n0i)d + %(sti)d ->
  lr_rhs (iarm_%(mid)s i r) = cls_conf FAM (zdside FAM (zdPL ZA i) (ZA ++ ZA) r (astride %(n0i)d %(sti)d r) ZB).
Proof. intros i r Hi Hr.
%(icomp)s  exfalso; lia.
Qed.

Lemma earm_reach_%(mid)s : forall r, r < %(n0e)d + %(ste)d ->
  ReachL tm true true (lr_lhs (earm_%(mid)s r)) (lr_rhs (earm_%(mid)s r)).
Proof. intros r Hr.
%(esound)s  exfalso; lia.
Qed.

Lemma earm_lhs_%(mid)s : forall r, r < %(n0e)d + %(ste)d ->
  lr_lhs (earm_%(mid)s r) = cls_conf FAM (zdside FAM (zdPR ZA ZB (1 - %(u0)d)) ZB r (astride %(n0e)d %(ste)d r) (ZA ++ ZT)).
Proof. intros r Hr.
%(ecomp)s  exfalso; lia.
Qed.

Lemma earm_rhs_%(mid)s : forall r, r < %(n0e)d + %(ste)d ->
  lr_rhs (earm_%(mid)s r) = cls_conf FAM (zdside FAM (zdPL ZA (1 - %(u0)d)) (ZA ++ ZA) r (astride %(n0e)d %(ste)d r) (ZB ++ ZT)).
Proof. intros r Hr.
%(ecomp)s  exfalso; lia.
Qed.

Lemma tarm_reach_%(mid)s : forall r, r < %(n0t)d + %(stt)d ->
  ReachL tm true true (lr_lhs (tarm_%(mid)s r)) (lr_rhs (tarm_%(mid)s r)).
Proof. intros r Hr.
%(tsound)s  exfalso; lia.
Qed.

Lemma tarm_lhs_%(mid)s : forall r, r < %(n0t)d + %(stt)d ->
  lr_lhs (tarm_%(mid)s r) = cls_conf FAM (zdside FAM (zdPR ZA ZB %(u0)d) ZB r (astride %(n0t)d %(stt)d r) ZT).
Proof. intros r Hr.
%(tcomp)s  exfalso; lia.
Qed.

Lemma tarm_rhs_%(mid)s : forall r, r < %(n0t)d + %(stt)d ->
  lr_rhs (tarm_%(mid)s r) = cls_conf FAM (zdside FAM (zdPL ZA %(po)d) (ZA ++ ZA) (r + %(co)d)
                                        (astride %(n0t)d %(stt)d r) (tcells ZA ZB ZW ++ ZT)).
Proof. intros r Hr.
%(tcomp)s  exfalso; lia.
Qed.

Lemma vis_ok_%(mid)s : forall r t, ~ In t pins_%(mid)s -> r < %(n0t)d + %(stt)d ->
  nfire tm true true nrules (vsegs_%(mid)s r t) (vis_%(mid)s r t) (lr_lhs (tarm_%(mid)s r)) = Some t.
Proof. intros r t Hnp Hr.
%(fvis)s  exfalso; lia.
Qed.

Lemma uinv0_%(mid)s : uinv %(u0)d %(x0)s.
Proof. split; [discriminate | exists %(n0)d; reflexivity]. Qed.

Lemma bootl_%(mid)s :
  stepn %(tmb)s %(t0)d InitES = Some (lift (zdcfg FAM ZA ZB ZT %(x0)s)).
Proof.
  assert (H : match csteps %(tmb)s %(t0)d c0 with
              | Some c => ceqb c (zdcfg FAM ZA ZB ZT %(x0)s)
              | None => false end = true) by (vm_compute; reflexivity).
  destruct (csteps %(tmb)s %(t0)d c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

'''

ARGS = '''  - lia.
  - lia.
  - lia.
  - reflexivity.
  - exact uinv0_%(mid)s.
  - lia.
  - exact iarm_reach_%(mid)s.
  - exact iarm_lhs_%(mid)s.
  - exact iarm_rhs_%(mid)s.
  - lia.
  - exact earm_reach_%(mid)s.
  - exact earm_lhs_%(mid)s.
  - exact earm_rhs_%(mid)s.
  - lia.
  - exact tarm_reach_%(mid)s.
  - exact tarm_lhs_%(mid)s.
  - exact tarm_rhs_%(mid)s.
  - exact nrules_sound_%(mid)s.
  - exact vis_ok_%(mid)s.
  - exact bootl_%(mid)s.
'''

CALL = '''(%(board)s tm_%(mid)s pins_%(mid)s FAM ZA ZB ZT %(u0)d %(a)d %(po)d %(co)d %(dh)d ZW
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
    u0, dh = cd['u0'], cd['dh']
    L = [HEAD % dict(n0i=n0i, sti=sti, n0e=n0e, ste=ste, n0t=n0t, stt=stt, mid=mid,
                     u0=u0, dh=dh, a=cd['a'], w=clist(cd['w'], lambda b: 'true' if b else 'false'),
                     T=clist(cd['T'], lambda c: 'S%d' % c),
                     A=clist(cd['A'], lambda c: 'S%d' % c),
                     B=clist(cd['B'], lambda c: 'S%d' % c))]
    inner, arms = [], []
    for i, r, c0, c1, ch in cd['inter']:
        arms.append(('iarm%d_%d' % (i, r), c0, c1, prog_coq(tab, inner, ch), el, er))
    for i, r, c0, c1, ch in cd['endc']:
        arms.append(('earm_%d' % r, c0, c1, prog_coq(tab, inner, ch), True, True))
    offs = {}
    for i, r, c0, c1, ch in cd['top']:
        offs[r] = len(inner)
        arms.append(('tarm_%d' % r, c0, c1, prog_coq(tab, inner, ch), True, True))
    L.append(inner_coq(mid, inner))
    for nm, c0, c1, segs, el_, er_ in arms:
        L.append(ARM % dict(nm=nm, mid=mid, lhs=coq_conf(c0), rhs=coq_conf(c1),
                            segs=';\n   '.join(segs), el=str(el_).lower(),
                            er=str(er_).lower()))

    def disp2(nm, grp):
        i0, r0 = grp[0][:2]
        return ('Definition %s_%s (i r : nat) : LRule :=\n  match i, r with %s | _, _ => %s%d_%d_%s end.\n'
                % (nm, mid, ' '.join('| %d, %d => %s%d_%d_%s' % (i, r, nm, i, r, mid)
                                      for i, r, *_ in grp), nm, i0, r0, mid))

    def disp1(nm, grp):
        r0 = grp[0][1]
        return ('Definition %s_%s (r : nat) : LRule :=\n  match r with %s | _ => %s_%d_%s end.\n'
                % (nm, mid, ' '.join('| %d => %s_%d_%s' % (r, nm, r, mid)
                                      for _i, r, *_ in grp), nm, r0, mid))
    L.append(disp2('iarm', cd['inter']) + disp1('earm', cd['endc']) + disp1('tarm', cd['top']))
    L.append('''
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

''' % dict(mid=mid,
           vb='\n  '.join('| %d, (%s, %s) => %s' % (k, ST[w[0]], SYM[w[1]], coq_chain_l(v[1]))
                          for k in sorted(cd['nvis']) for w, v in sorted(cd['nvis'][k].items())),
           sb='\n  '.join('| %d, (%s, %s) => [%s]'
                          % (k, ST[w[0]], SYM[w[1]],
                             '; '.join(coq_seg(sg, offs[k]) for sg in v[0]))
                          for k in sorted(cd['nvis']) for w, v in sorted(cd['nvis'][k].items()))))

    def br2(n, body):
        out = []
        for i in (0, 1):
            rb = []
            for r in range(n):
                rb.append('    destruct r as [|r].\n    { %s. }\n' % body(i, r))
            out.append('  destruct i as [|i].\n  {\n%s    exfalso; lia.\n  }\n' % ''.join(rb))
        return ''.join(out)

    def br1(n, body):
        return ''.join('  destruct r as [|r].\n  { %s. }\n' % body(r) for r in range(n))

    def reach2(nm):
        return lambda i, r: ('eapply narm_reach; [exact nrules_sound_%s | exact ok_%s%d_%d_%s]'
                             % (mid, nm, i, r, mid))

    def reach1(nm):
        return lambda r: ('eapply narm_reach; [exact nrules_sound_%s | exact ok_%s_%d_%s]'
                          % (mid, nm, r, mid))
    vm2 = lambda i, r: 'vm_compute; reflexivity'  # noqa: E731
    vm1 = lambda r: 'vm_compute; reflexivity'  # noqa: E731
    fv = lambda r: ('destruct t as [q s]; destruct q, s; try (exfalso; apply Hnp; simpl; tauto); '
                    'vm_compute; reflexivity')  # noqa: E731
    t0 = cd['t0']
    tau = cd['tau']
    ndig = sum(2 if b else 1 for b in tau)
    x0 = clist(tau, lambda b: 'true' if b else 'false')
    L.append(THM % dict(
        mid=mid, n0i=n0i, sti=sti, n0e=n0e, ste=ste, n0t=n0t, stt=stt, u0=u0, dh=dh,
        po=cd['po'], co=cd['co'],
        isound=br2(n0i + sti, reach2('iarm')), icomp=br2(n0i + sti, vm2),
        esound=br1(n0e + ste, reach1('earm')), ecomp=br1(n0e + ste, vm1),
        tsound=br1(n0t + stt, reach1('tarm')), tcomp=br1(n0t + stt, vm1),
        fvis=br1(n0t + stt, fv), n0=(ndig - u0 - 1) // 2,
        t0=t0, x0=x0,
        tmb=('tm_%s' % mid) if E.TR_QH is not None else 'tm'))
    common = dict(mid=mid, n0i=n0i, sti=sti, n0e=n0e, ste=ste, n0t=n0t, stt=stt,
                  u0=u0, dh=dh, a=cd['a'], po=cd['po'], co=cd['co'], x0=x0, t0=t0)
    args = ARGS % common
    if E.TR_QH is not None:
        L.append(QH % dict(mid=mid, t0=t0, args=args, call=CALL % dict(
            common, board='boardZU_qhtr')))
    else:
        L.append(NQH % dict(mid=mid, args=args, call=CALL % dict(
            common, board='boardZU_neverqhtr')))
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
        if cert['boot']['steps_from_blank'] <= lastf:
            got = find_after(cert, max(400000, 2 * lastf + 200000), lastf)
            if got is None:
                print('no boot past the last pinned fire %d' % lastf)
                return 1
            cert['boot'] = got
        E.TR_QH = cert['boot']['steps_from_blank']
    else:
        E.TR_PINS = E.unfired(cert['spec'], 10 ** 6)
    good, bad, cd = E.emit(cert, args.out)
    print('%s: closure %s' % (args.out, 'BUILT' if cd else 'not built'))
    return 0 if cd else 1


if __name__ == '__main__':
    sys.exit(main())
