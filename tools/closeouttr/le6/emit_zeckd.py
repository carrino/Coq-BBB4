#!/usr/bin/env python3
"""UNTRUSTED emitter: a `zeckw_detect.py` COUNTDOWN certificate (a Zeckendorf
string counting down, tokens 0 -> A, 10 -> B) -> a Coq board closed by
[LadderCheckZeckDTr] (SCOPING_INSTR 7.4.LE6).

The counter side at the anchor is `pre ++ tcells tau ++ T` for a token list
tau (false = A, true = B); the arms are the three classes of
[LadderCheckZeckDTr] in two kinds each (PL 0 = [], PL 1 = A, PR 0 = A,
PR 1 = B):

  interior  PL u (AA)^k B X  -> PR u B^k A X        (X opaque)
  end       PL u (AA)^k B T  -> PR u B^k A T
  bottom    PL u (AA)^k T    -> PR u B^k T          (u = 0: k >= 1)

with emit_step's arm search (LE4's `emit_zeck2.py`, the classes changed);
the visits are from the bottom arms' anchors.

    python3 emit_zeckd.py CERT.json -o OUT.v [--qh]
"""
import argparse
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'le3'))
sys.path.insert(0, os.path.join(HERE, '..', 'le4'))
sys.path.insert(0, HERE)
import emit_step as S  # noqa: E402
from emit_step import (E, NoClosure, blk, ARM_GRID, coq_conf, coq_chain_l,  # noqa: E402
                       coq_seg, clist, ST, SYM, Arms, nvisits, prog_coq,
                       inner_coq, ARM, BOOTL, _rstrip0)


from zeckw_detect import zw, find_after  # noqa: E402


def tokens(x):
    """the token list of the digit string x ++ [0] (false = 0, true = 10)"""
    y, out, i = list(x) + [0], [], 0
    while i < len(y):
        if y[i] == 0:
            out.append(False); i += 1
        else:
            out.append(True); i += 2
    return out


def closure_data_zeck(cert, tab):
    fam = cert['family']
    if fam.get('numeration') != 'zeckd':
        raise NoClosure('numeration %s: LadderCheckZeckDTr is the Zeckendorf countdown'
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
    mode = cert.get('mode', ['dec', 0])
    dw = int(mode[1][1:]) - 1 if isinstance(mode[1], str) else 0
    if not isinstance(mode[1], str) and mode[1] != 0:
        raise NoClosure('countdown mode %r: no checker' % (mode,))

    def BR(u):
        toks = [(u + dw) % 2 == 1] + [True] * ((u + dw) // 2)
        return tuple(c for t in toks for c in (B if t else A))

    def grid_arms(kind, n0, st):
        got = []
        for i in (0, 1):
            for r in range(n0 + st):
                if kind == 'T' and i == 0 and r == 0:
                    continue
                s_ = 0 if r < n0 else st
                lp = pre + PL[i] + AA * r
                rp = pre + PR[i] + B * r
                if kind == 'I':
                    c0, c1 = conf(blk(lp, AA, s_, B)), conf(blk(rp, B, s_, A))
                    e = (el, er)
                elif kind == 'E':
                    c0, c1 = conf(blk(lp, AA, s_, B + T)), conf(blk(rp, B, s_, A + T))
                    e = (True, True)
                else:
                    c0, c1 = conf(blk(lp, AA, s_, T)), conf(blk(pre + BR(i) + B * r, B, s_, T))
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
        raise NoClosure('bottom arm: no program, or an instruction no bottom anchor fires')
    return dict(nest=True, el=el, er=er, inter=inter, n0i=n0i, sti=sti,
                endc=endc, n0e=n0e, ste=ste, top=top, n0t=n0t, stt=stt,
                nvis=nvis, tau=tau, t0=boot['steps_from_blank'], T=T, A=A, B=B, dw=dw,
                fill=top)  # emit_ladder's report line


HEAD = '''
(** ** The closure: a ZECKENDORF COUNTDOWN over two token words ([LadderCheckZeckDTr])

    Tokens [0 -> ZA], [10 -> ZB].  Interior arms at threshold %(n0i)d stride
    %(sti)d, end arms at %(n0e)d / %(ste)d, bottom arms at %(n0t)d / %(stt)d,
    each in two kinds.  Every arm is a [LadderNest] segment program. *)
From BBB4.Checkers Require Import LadderCheckZeckDTr%(dwimp)s.

Definition zt_%(mid)s : list Sym := %(T)s.
Local Notation ZT := zt_%(mid)s.
Definition za_%(mid)s : list Sym := %(A)s.
Local Notation ZA := za_%(mid)s.
Definition zb_%(mid)s : list Sym := %(B)s.
Local Notation ZB := zb_%(mid)s.

'''

THM = '''Lemma iarm_reach_%(mid)s : forall i r, i < 2 -> r < %(n0i)d + %(sti)d ->
  ReachL tm (negb (fm_left FAM)) (fm_left FAM) (lr_lhs (iarm_%(mid)s i r)) (lr_rhs (iarm_%(mid)s i r)).
Proof. intros i r Hi Hr.
%(isound)s  exfalso; lia.
Qed.

Lemma iarm_lhs_%(mid)s : forall i r, i < 2 -> r < %(n0i)d + %(sti)d ->
  lr_lhs (iarm_%(mid)s i r) = cls_conf FAM (zdside FAM (zdPL ZA i) (ZA ++ ZA) r (astride %(n0i)d %(sti)d r) ZB).
Proof. intros i r Hi Hr.
%(icomp)s  exfalso; lia.
Qed.

Lemma iarm_rhs_%(mid)s : forall i r, i < 2 -> r < %(n0i)d + %(sti)d ->
  lr_rhs (iarm_%(mid)s i r) = cls_conf FAM (zdside FAM (zdPR ZA ZB i) ZB r (astride %(n0i)d %(sti)d r) ZA).
Proof. intros i r Hi Hr.
%(icomp)s  exfalso; lia.
Qed.

Lemma earm_reach_%(mid)s : forall i r, i < 2 -> r < %(n0e)d + %(ste)d ->
  ReachL tm true true (lr_lhs (earm_%(mid)s i r)) (lr_rhs (earm_%(mid)s i r)).
Proof. intros i r Hi Hr.
%(esound)s  exfalso; lia.
Qed.

Lemma earm_lhs_%(mid)s : forall i r, i < 2 -> r < %(n0e)d + %(ste)d ->
  lr_lhs (earm_%(mid)s i r) = cls_conf FAM (zdside FAM (zdPL ZA i) (ZA ++ ZA) r (astride %(n0e)d %(ste)d r) (ZB ++ ZT)).
Proof. intros i r Hi Hr.
%(ecomp)s  exfalso; lia.
Qed.

Lemma earm_rhs_%(mid)s : forall i r, i < 2 -> r < %(n0e)d + %(ste)d ->
  lr_rhs (earm_%(mid)s i r) = cls_conf FAM (zdside FAM (zdPR ZA ZB i) ZB r (astride %(n0e)d %(ste)d r) (ZA ++ ZT)).
Proof. intros i r Hi Hr.
%(ecomp)s  exfalso; lia.
Qed.

Lemma tarm_reach_%(mid)s : forall i r, i < 2 -> r < %(n0t)d + %(stt)d -> (i = 0 -> 0 < r) ->
  ReachL tm true true (lr_lhs (tarm_%(mid)s i r)) (lr_rhs (tarm_%(mid)s i r)).
Proof. intros i r Hi Hr H0.
%(tsound)s  exfalso; lia.
Qed.

Lemma tarm_lhs_%(mid)s : forall i r, i < 2 -> r < %(n0t)d + %(stt)d -> (i = 0 -> 0 < r) ->
  lr_lhs (tarm_%(mid)s i r) = cls_conf FAM (zdside FAM (zdPL ZA i) (ZA ++ ZA) r (astride %(n0t)d %(stt)d r) ZT).
Proof. intros i r Hi Hr H0.
%(tcomp)s  exfalso; lia.
Qed.

Lemma tarm_rhs_%(mid)s : forall i r, i < 2 -> r < %(n0t)d + %(stt)d -> (i = 0 -> 0 < r) ->
  lr_rhs (tarm_%(mid)s i r) = %(botrhs)s.
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
  stepn %(tmb)s %(t0)d InitES = Some (lift (zdcfg FAM ZA ZB ZT %(x0)s)).
Proof.
  assert (H : match csteps %(tmb)s %(t0)d c0 with
              | Some c => ceqb c (zdcfg FAM ZA ZB ZT %(x0)s)
              | None => false end = true) by (vm_compute; reflexivity).
  destruct (csteps %(tmb)s %(t0)d c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

'''

ARGS = '''  - discriminate.
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

CALL = '''(%(board)s tm_%(mid)s pins_%(mid)s FAM ZA ZB ZT
                 iarm_%(mid)s %(n0i)d %(sti)d earm_%(mid)s %(n0e)d %(ste)d
                 tarm_%(mid)s %(n0t)d %(stt)d nrules vsegs_%(mid)s vis_%(mid)s %(dwarg)s%(x0)s)'''

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
    L = [HEAD % dict(n0i=n0i, sti=sti, n0e=n0e, ste=ste, n0t=n0t, stt=stt, mid=mid,
                     T=clist(cd['T'], lambda c: 'S%d' % c),
                     A=clist(cd['A'], lambda c: 'S%d' % c),
                     B=clist(cd['B'], lambda c: 'S%d' % c),
                     dwimp=' LadderCheckZeckDwTr' if cd['dw'] else '')]
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
        botrhs=('cls_conf FAM (zdside FAM (zdBR ZA ZB %d i) ZB r (astride %d %d r) ZT)' % (cd['dw'], n0t, stt)
                if cd['dw'] else
                'cls_conf FAM (zdside FAM (zdPR ZA ZB i) ZB r (astride %d %d r) ZT)' % (n0t, stt)),
        fvis=br(n0t + stt, fv, sk),
        t0=t0, x0=clist(cd['tau'], lambda b: 'true' if b else 'false'),
        tmb=('tm_%s' % mid) if E.TR_QH is not None else 'tm'))
    common = dict(mid=mid, n0i=n0i, sti=sti, n0e=n0e, ste=ste, n0t=n0t, stt=stt,
                  dwarg=('%d ' % cd['dw']) if cd['dw'] else '',
                  x0=clist(cd['tau'], lambda b: 'true' if b else 'false'), t0=t0)
    args = ARGS % common
    if E.TR_QH is not None:
        L.append(QH % dict(mid=mid, t0=t0, args=args, call=CALL % dict(
            common, board='boardZDw_qhtr' if cd['dw'] else 'boardZD_qhtr')))
    else:
        L.append(NQH % dict(mid=mid, args=args, call=CALL % dict(
            common, board='boardZDw_neverqhtr' if cd['dw'] else 'boardZD_neverqhtr')))
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
