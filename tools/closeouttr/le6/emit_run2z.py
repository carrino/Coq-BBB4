#!/usr/bin/env python3
"""UNTRUSTED emitter (SCOPING_INSTR 7.4.LE6): LE4's `emit_run2.py` for
[LadderCheckRun2zTr], the marker run whose refill ends in a fixed digit
string `z`: `([], m) -> (0^(m+a) ++ z, c)`.  The law is read off the visits
(`z` = the digits after the longest D0 prefix of the refilled `x`); the
refill arms land on `pre D0^f1 (D0^f2 z M T^c suf)`.  Everything else is
`emit_run2.py`'s.

    python3 emit_run2z.py SPEC DETECT.jsonl -o OUT.v [--qh]
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
                       coq_seg, clist, ST, SYM, _splits, _rstrip0, Arms,
                       nvisits, prog_coq, inner_coq, ARM, BOOTL)
import termrun_detect as TD  # noqa: E402
import termrun2_detect as TD2  # noqa: E402


_read0 = TD2.read


def read_padded(st, l, pre, suf, T, M):
    """LE6: TD2.read, also with the visit string padded by up to len(M) + l
    blanks (a refilled x whose top word and the marker end in blanks beyond
    the tape's last nonzero cell)"""
    r = _read0(st, l, pre, suf, T, M)
    if r is not None or suf:
        return r
    for k in range(1, len(M) + l + 1):
        r = _read0(st + '0' * k, l, pre, suf, T, M)
        if r is not None:
            return r
    return None


TD2.read = read_padded


def visits_seq(spec, det, steps=150000):
    """[(t, x words, m)] at the detector's anchor, in order"""
    q0, s0, side = det['anchor']
    tm = TD.parse(spec)
    tape, h, q = {}, 0, 0
    out = []
    for t in range(steps):
        s = tape.get(h, 0)
        tr = tm[(q, s)]
        if tr is None:
            break
        if q == q0 and s == s0:
            cells = [i for i, v in tape.items() if v]
            st = None
            if side == 'R' and (not cells or min(cells) >= h):
                st = ''.join(str(tape.get(i, 0)) for i in range(h + 1, max(cells + [h]) + 1))
            elif side == 'L' and (not cells or max(cells) <= h):
                st = ''.join(str(tape.get(i, 0)) for i in range(h - 1, min(cells + [h]) - 1, -1))
            if st is not None:
                r = TD2.read(st, det['l'], det['pre'], det['suf'], det['T'], det['M'])
                if r is not None:
                    out.append((t, r[0], r[1]))
        w, d, nq = tr
        tape[h] = w
        h += d
        q = nq
    return out


def nvisits_f(tab, want, fl, prog, el, er):
    """emit_step.nvisits with the tail flags of the arm (LE6: the narrowing
    arms' far tail is opaque)"""
    if not (isinstance(prog, tuple) and prog[:1] == ('NEST',)):
        prog = ('NEST', [('NCh', prog)], [])
    _t, segs, rules = prog
    rr = [(a_, b_) for a_, b_, _c in rules]
    seen = {}
    for k in range(len(segs) + 1):
        got = S.nest.nrun(tab, el, er, rr, segs[:k], fl)
        if got is None:
            break
        ck = got[0]
        chs = ([segs[k][1][:i] for i in range(len(segs[k][1]) + 1)]
               if k < len(segs) and segs[k][0] == 'NCh' else [[]])
        for base in chs:
            for kind in ('SWin', 'SWinL', 'SWinR'):
                for n in range(0, 600):
                    g = S.LC.srun(tab, el, er, base + [(kind, n)], ck)
                    if g is None:
                        break
                    seen.setdefault((g[0][0], g[0][2]),
                                    (list(segs[:k]), base + [(kind, n)]))
            if all(i in seen for i in want):
                return seen
    return seen


def read_law(seq):
    """(D0, D1, a, c) from consecutive visits"""
    d0 = d1 = None
    for (_t, x, m), (_t2, x2, m2) in zip(seq, seq[1:]):
        if m == m2 and len(x) == len(x2) and x and x[0] != x2[0] and x[1:] == x2[1:]:
            d0, d1 = x[0], x2[0]
            break
    if d0 is None:
        raise NoClosure('no low-digit step seen')
    law = None
    for i, (_t, x, m) in enumerate(seq[:-1]):
        if x:
            continue
        # the refilled x: the first of the next visits (up to 4) whose x is
        # D0^k ++ z with k >= m; an x refilled to all-top (or one below it)
        # narrows at once, and the refill arm runs through those visits (LE6)
        for j in range(i + 1, min(i + 5, len(seq))):
            _t2, x2, m2 = seq[j]
            k = 0
            while k < len(x2) and x2[k] == d0:
                k += 1
            z = [0 if w == d0 else 1 for w in x2[k:]]
            if k >= m and not (z and z[0] == 0):
                law = (k - m, m2, z)
                break
        if law is None:
            raise NoClosure('a refill that is not D0^(m+a) ++ z within 4 visits')
        break
    if law is None:
        raise NoClosure('no refill seen')
    return d0, d1, law[0], law[1], law[2]


def closure_data_run(det, tab, d0, d1, a, c, boot, z):
    l = det['l']
    T = tuple(int(ch) for ch in det['T'])
    M = tuple(int(ch) for ch in det['M'])
    pre = tuple(int(ch) for ch in det['pre'])
    suf = tuple(int(ch) for ch in det['suf'])
    D0 = tuple(int(ch) for ch in d0)
    D1 = tuple(int(ch) for ch in d1)
    q, hs, side = det['anchor']
    left = side == 'L'
    OTHER = ((), (), 0, 0, ())

    def conf(sd):
        return (q, sd, hs, OTHER) if left else (q, OTHER, hs, sd)

    derive = Arms(tab).derive
    el, er = (not left), left

    ZC = tuple(cell for dgt in z for cell in (D1 if dgt else D0))
    look = [D0, D1, M]   # [ilookM e]: the next digit, or the marker (e = b = 2)

    def inter_at(n0, st):
        got = []
        for e in range(3):
            for r in range(n0 + st):
                s_ = 0 if r < n0 else st
                c0 = conf(blk(pre + D1 * r, D1, s_, D0 + look[e]))
                c1 = conf(blk(pre + D0 * r, D0, s_, D1 + look[e]))
                try:
                    got.append((e, r, c0, c1,
                                derive(el, er, c0, c1, 'interior e=%d r=%d' % (e, r))))
                except NoClosure:
                    return None
        return got

    def nar_at(n0, st):
        got = []
        for r in range(1, n0 + st):
            s_ = 0 if r < n0 else st
            c0 = conf(blk(pre + D1 * r, D1, s_, M))
            c1 = conf(blk(pre + D0 * (r - 1), D0, s_, M + T))
            try:
                got.append((r, c0, c1, derive(el, er, c0, c1, 'narrowing r=%d' % r)))
            except NoClosure:
                return None
        return got

    def refill_at(n0, st):
        got = []
        for r in range(0, n0 + st):
            s_ = 0 if r < n0 else st
            c0 = conf(blk(pre + M + T * r, T, s_, suf))
            hit = None
            for f1 in _splits(r + a):
                c1 = conf(blk(pre + D0 * f1, D0, s_, D0 * (r + a - f1) + ZC + M + T * c + suf))
                try:
                    hit = (r, f1, r + a - f1, c0, c1,
                           derive(True, True, c0, c1, 'refill r=%d' % r))
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
    narr, n0n, stn = first(nar_at, grid1)
    want = [(q_, s_) for q_ in range(4) for s_ in range(2)
            if (q_, s_) not in E.TR_PINS]
    seenN = {r: nvisits_f(tab, want, c0, ch, el, er) for r, c0, _c1, ch in narr}
    refill = nvis = None
    for n0, st in ARM_GRID:
        g = refill_at(n0, st)
        if g is None:
            continue
        seen = {r: nvisits(tab, want, c0, ch) for r, _f1, _f2, c0, _c1, ch in g}
        how = {}
        for i in want:
            if all(i in seen[r] for r in seen):
                how[i] = 'R'
            elif z and all(i in seenN[r] for r in seenN):
                how[i] = 'N'
        if len(how) == len(want):
            refill, n0r, str_ = g, n0, st
            nvis = {r: {i: seen[r][i] for i in want if how[i] == 'R'} for r in seen}
            nvisN = {r: {i: seenN[r][i] for i in want if how[i] == 'N'} for r in seenN}
            break
    if refill is None:
        raise NoClosure('refill: no program, or an instruction neither the refill nor the narrowing anchors fire')
    return dict(nest=True, el=el, er=er, inter=inter, n0i=n0i, sti=sti,
                narr=narr, n0n=n0n, stn=stn, refill=refill, n0r=n0r, str=str_,
                nvis=nvis, nvisN=nvisN, how=how, want=want, a=a, c=c, T=T, M=M, suf=suf, boot=boot, z=z,
                # emit_ladder's report line
                fill=refill)


HEAD = '''
(** ** The closure: a TERMINATOR-RUN counter with a marker ([LadderCheckRun2Tr])

    The counter side is [pre ++ x ++ M ++ T^m ++ suf], [x] binary over the
    two digit words, [M = %(M)s], [T = %(T)s]: inside a width [x] counts; the
    top of [x] narrows it by a digit and lengthens the run; an empty [x]
    refills to [0^(m + %(a)d) ++ runz] with the run [T^%(c)d] ([LadderCheckRun2zTr]).  Interior arms at threshold
    %(n0i)d stride %(sti)d, narrowing arms at %(n0n)d / %(stn)d, refill arms at
    %(n0r)d / %(str)d.  Every arm is a [LadderNest] segment program. *)
From BBB4.Checkers Require Import LadderCheckRun2zTr.

Definition runz_%(mid)s : list nat := %(zc)s.
Definition runM_%(mid)s : list Sym := %(Mc)s.
Definition runT_%(mid)s : list Sym := %(Tc)s.
Definition runsuf_%(mid)s : list Sym := %(sufc)s.

'''

THM = '''Lemma iarm_reach_%(mid)s : forall d e r, d < fm_b FAM - 1 -> e <= fm_b FAM -> r < %(n0i)d + %(sti)d ->
  ReachL tm (negb (fm_left FAM)) (fm_left FAM) (lr_lhs (iarm_%(mid)s d e r)) (lr_rhs (iarm_%(mid)s d e r)).
Proof.
  intros d e r Hd He Hr. vm_compute in Hd, He. destruct d as [|d]; [|exfalso; lia].
%(isound)s  exfalso; lia.
Qed.

Lemma iarm_lhs_%(mid)s : forall d e r, d < fm_b FAM - 1 -> e <= fm_b FAM -> r < %(n0i)d + %(sti)d ->
  lr_lhs (iarm_%(mid)s d e r)
    = cls_conf FAM (blk (fm_pre FAM ++ rep (dig FAM (fm_b FAM - 1)) r) (dig FAM (fm_b FAM - 1))
                     (astride %(n0i)d %(sti)d r) (dig FAM d ++ ilookZ FAM runM_%(mid)s e)).
Proof.
  intros d e r Hd He Hr. vm_compute in Hd, He. destruct d as [|d]; [|exfalso; lia].
%(icomp)s  exfalso; lia.
Qed.

Lemma iarm_rhs_%(mid)s : forall d e r, d < fm_b FAM - 1 -> e <= fm_b FAM -> r < %(n0i)d + %(sti)d ->
  lr_rhs (iarm_%(mid)s d e r)
    = cls_conf FAM (blk (fm_pre FAM ++ rep (dig FAM 0) r) (dig FAM 0)
                     (astride %(n0i)d %(sti)d r) (dig FAM (S d) ++ ilookZ FAM runM_%(mid)s e)).
Proof.
  intros d e r Hd He Hr. vm_compute in Hd, He. destruct d as [|d]; [|exfalso; lia].
%(icomp)s  exfalso; lia.
Qed.

Lemma narm_reach_%(mid)s : forall r, 0 < r -> r < %(n0n)d + %(stn)d ->
  ReachL tm (negb (fm_left FAM)) (fm_left FAM) (lr_lhs (narm_%(mid)s r)) (lr_rhs (narm_%(mid)s r)).
Proof.
  intros r H0 Hr.
%(nsound)s  exfalso; lia.
Qed.

Lemma narm_lhs_%(mid)s : forall r, 0 < r -> r < %(n0n)d + %(stn)d ->
  lr_lhs (narm_%(mid)s r)
    = cls_conf FAM (blk (fm_pre FAM ++ rep (dig FAM (fm_b FAM - 1)) r)
                     (dig FAM (fm_b FAM - 1)) (astride %(n0n)d %(stn)d r) runM_%(mid)s).
Proof.
  intros r H0 Hr.
%(ncomp)s  exfalso; lia.
Qed.

Lemma narm_rhs_%(mid)s : forall r, 0 < r -> r < %(n0n)d + %(stn)d ->
  lr_rhs (narm_%(mid)s r)
    = cls_conf FAM (blk (fm_pre FAM ++ rep (dig FAM 0) (r - 1))
                     (dig FAM 0) (astride %(n0n)d %(stn)d r) (runM_%(mid)s ++ runT_%(mid)s)).
Proof.
  intros r H0 Hr.
%(ncomp)s  exfalso; lia.
Qed.

Lemma rarm_reach_%(mid)s : forall r, r < %(n0r)d + %(str)d ->
  ReachL tm true true (lr_lhs (rarm_%(mid)s r)) (lr_rhs (rarm_%(mid)s r)).
Proof.
  intros r Hr.
%(rsound)s  exfalso; lia.
Qed.

Lemma rarm_lhs_%(mid)s : forall r, r < %(n0r)d + %(str)d ->
  lr_lhs (rarm_%(mid)s r)
    = cls_conf FAM (blk (fm_pre FAM ++ runM_%(mid)s ++ rep runT_%(mid)s r) runT_%(mid)s
                     (astride %(n0r)d %(str)d r) runsuf_%(mid)s).
Proof.
  intros r Hr.
%(rcomp)s  exfalso; lia.
Qed.

Lemma rarm_rhs_%(mid)s : forall r, r < %(n0r)d + %(str)d ->
  lr_rhs (rarm_%(mid)s r)
    = cls_conf FAM (blk (fm_pre FAM ++ rep (dig FAM 0) (fm1_%(mid)s r)) (dig FAM 0)
                     (astride %(n0r)d %(str)d r)
                     (rep (dig FAM 0) (fm2_%(mid)s r) ++ flat_map (dig FAM) runz_%(mid)s ++ runM_%(mid)s ++ rep runT_%(mid)s %(c)d ++ runsuf_%(mid)s)).
Proof.
  intros r Hr.
%(rcomp)s  exfalso; lia.
Qed.

Lemma fm_%(mid)s : forall r, r < %(n0r)d + %(str)d ->
  fm1_%(mid)s r + fm2_%(mid)s r = r + %(a)d.
Proof.
  intros r Hr.
%(rlia)s  exfalso; lia.
Qed.

Lemma vis_ok_%(mid)s : forall t, ~ In t pins_%(mid)s ->
  (forall r, r < %(n0r)d + %(str)d ->
     nfire tm true true nrules (vsegs_%(mid)s r t) (vis_%(mid)s r t)
       (lr_lhs (rarm_%(mid)s r)) = Some t)
  \/ (runz_%(mid)s <> [] /\ forall r, 0 < r -> r < %(n0n)d + %(stn)d ->
     nfire tm (negb (fm_left FAM)) (fm_left FAM) nrules (vsegsN_%(mid)s r t) (visN_%(mid)s r t)
       (lr_lhs (narm_%(mid)s r)) = Some t).
Proof.
  intros t Hnp. destruct t as [q s]; destruct q, s; try (exfalso; apply Hnp; simpl; tauto).
%(fvis)s
Qed.

Lemma bootl_%(mid)s :
  stepn %(tmb)s %(t0)d InitES = Some (lift (rcfgZ FAM runM_%(mid)s runT_%(mid)s runsuf_%(mid)s (%(x0)s, %(m0)d))).
Proof.
  assert (H : match csteps %(tmb)s %(t0)d c0 with
              | Some c => ceqb c (rcfgZ FAM runM_%(mid)s runT_%(mid)s runsuf_%(mid)s (%(x0)s, %(m0)d))
              | None => false end = true) by (vm_compute; reflexivity).
  destruct (csteps %(tmb)s %(t0)d c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

'''

ARGS = '''  - vm_compute; lia.
  - repeat constructor.
  - repeat constructor.
  - lia.
  - exact iarm_reach_%(mid)s.
  - exact iarm_lhs_%(mid)s.
  - exact iarm_rhs_%(mid)s.
  - lia.
  - lia.
  - exact narm_reach_%(mid)s.
  - exact narm_lhs_%(mid)s.
  - exact narm_rhs_%(mid)s.
  - lia.
  - exact rarm_reach_%(mid)s.
  - exact rarm_lhs_%(mid)s.
  - exact rarm_rhs_%(mid)s.
  - exact fm_%(mid)s.
  - exact nrules_sound_%(mid)s.
  - exact vis_ok_%(mid)s.
  - exact bootl_%(mid)s.
'''

CALL = '''(%(board)s tm_%(mid)s pins_%(mid)s FAM runM_%(mid)s runT_%(mid)s runsuf_%(mid)s %(a)d %(c)d runz_%(mid)s
                 iarm_%(mid)s %(n0i)d %(sti)d narm_%(mid)s %(n0n)d %(stn)d
                 rarm_%(mid)s %(n0r)d %(str)d fm1_%(mid)s fm2_%(mid)s
                 nrules vsegs_%(mid)s vis_%(mid)s vsegsN_%(mid)s visN_%(mid)s %(x0)s %(m0)d)'''

NQH = '''(** The machine-level theorem, at the INSTRUCTION level, through
    [LadderCheckRun2zTr.boardR_neverqhtrZ]. *)
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
    [LadderCheckRun2zTr.boardR_qhtrZ]. *)
Theorem qhtr_%(mid)s :
  NonHalt tm_%(mid)s /\\ QHBoundTr 32779478 tm_%(mid)s /\\ QuasiHaltsTr tm_%(mid)s.
Proof.
  eapply %(call)s.
%(args)s  - exact wit_%(mid)s.
  - exact bnd_%(mid)s.
Qed.
'''


def syms(cells):
    return '[' + ';'.join('S%d' % x for x in cells) + ']'


def emit_closure_run(cert, tab, mid):
    cd = S.two_pass(lambda _c, _t: closure_data_run(*RUN), cert, tab)
    if isinstance(cd, NoClosure):
        return E.CLOSURE_NONE % cd, None
    n0i, sti, n0n, stn = cd['n0i'], cd['sti'], cd['n0n'], cd['stn']
    n0r, str_ = cd['n0r'], cd['str']
    a, c = cd['a'], cd['c']
    el, er = cd['el'], cd['er']
    L = [HEAD % dict(mid=mid, T=''.join(map(str, cd['T'])), M=''.join(map(str, cd['M'])),
                     Mc=syms(cd['M']), a=a, c=c, zc=clist(cd['z'], str),
                     n0i=n0i, sti=sti, n0n=n0n, stn=stn, n0r=n0r, str=str_,
                     Tc=syms(cd['T']), sufc=syms(cd['suf']))]
    inner, arms = [], []
    for e, r, c0, c1, ch in cd['inter']:
        arms.append(('iarm0_%d_%d' % (e, r), c0, c1, prog_coq(tab, inner, ch), el, er))
    offsN = {}
    for r, c0, c1, ch in cd['narr']:
        offsN[r] = len(inner)
        arms.append(('narm%d' % r, c0, c1, prog_coq(tab, inner, ch), el, er))
    offs = {}
    for r, _f1, _f2, c0, c1, ch in cd['refill']:
        offs[r] = len(inner)
        arms.append(('rarm%d' % r, c0, c1, prog_coq(tab, inner, ch), True, True))
    L.append(inner_coq(mid, inner))
    for nm, c0, c1, segs, el_, er_ in arms:
        L.append(ARM % dict(nm=nm, mid=mid, lhs=coq_conf(c0), rhs=coq_conf(c1),
                            segs=';\n   '.join(segs), el=str(el_).lower(),
                            er=str(er_).lower()))
    L.append('''Definition iarm_%(mid)s (d e r : nat) : LRule :=
  match e, r with %(ib)s | _, _ => iarm0_0_0_%(mid)s end.
Definition narm_%(mid)s (r : nat) : LRule :=
  match r with %(nb)s | _ => narm1_%(mid)s end.
Definition rarm_%(mid)s (r : nat) : LRule :=
  match r with %(rb)s | _ => rarm0_%(mid)s end.
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

Definition visN_%(mid)s (r : nat) (t : Instr) : list lstep :=
  match r, t with
  %(vbN)s
  | _, _ => []
  end.

Definition vsegsN_%(mid)s (r : nat) (t : Instr) : list nseg :=
  match r, t with
  %(sbN)s
  | _, _ => []
  end.

''' % dict(
        mid=mid,
        ib=' '.join('| %d, %d => iarm0_%d_%d_%s' % (e, r, e, r, mid) for e, r, *_ in cd['inter']),
        nb=' '.join('| %d => narm%d_%s' % (r, r, mid) for r, *_ in cd['narr']),
        rb=' '.join('| %d => rarm%d_%s' % (r, r, mid) for r, *_ in cd['refill']),
        b1=' '.join('| %d => %d' % (r, f1) for r, f1, *_ in cd['refill']),
        b2=' '.join('| %d => %d' % (r, f2) for r, _f1, f2, *_ in cd['refill']),
        vb='\n  '.join('| %d, (%s, %s) => %s' % (r, ST[i[0]], SYM[i[1]], coq_chain_l(v[1]))
                       for r in sorted(cd['nvis']) for i, v in sorted(cd['nvis'][r].items())),
        sb='\n  '.join('| %d, (%s, %s) => [%s]'
                       % (r, ST[i[0]], SYM[i[1]],
                          '; '.join(coq_seg(sg, offs[r]) for sg in v[0]))
                       for r in sorted(cd['nvis']) for i, v in sorted(cd['nvis'][r].items())),
        vbN='\n  '.join('| %d, (%s, %s) => %s' % (r, ST[i[0]], SYM[i[1]], coq_chain_l(v[1]))
                        for r in sorted(cd['nvisN']) for i, v in sorted(cd['nvisN'][r].items())),
        sbN='\n  '.join('| %d, (%s, %s) => [%s]'
                        % (r, ST[i[0]], SYM[i[1]],
                           '; '.join(coq_seg(sg, offsN[r]) for sg in v[0]))
                        for r in sorted(cd['nvisN']) for i, v in sorted(cd['nvisN'][r].items()))))

    def reach(nm):
        return ('eapply narm_reach; [exact nrules_sound_%s | exact ok_%s_%s]'
                % (mid, nm, mid))

    def rb(n, body, lo=0):
        return ''.join('  destruct r as [|r].\n  { %s. }\n'
                       % ('exfalso; lia' if r < lo else body(r)) for r in range(n))

    def eb(n, body):
        out = []
        for e in range(3):
            out.append('  destruct e as [|e].\n  {\n%s  exfalso; lia.\n  }\n'
                       % ''.join('  destruct r as [|r].\n  { %s. }\n' % body(e, r)
                                 for r in range(n)))
        return ''.join(out)

    t0 = cd['boot']['t']
    L.append(THM % dict(
        mid=mid, n0i=n0i, sti=sti, n0n=n0n, stn=stn, n0r=n0r, str=str_, a=a, c=c,
        isound=eb(n0i + sti, lambda e, r: reach('iarm0_%d_%d' % (e, r))),
        icomp=eb(n0i + sti, lambda e, r: 'vm_compute; reflexivity'),
        nsound=rb(n0n + stn, lambda r: reach('narm%d' % r), lo=1),
        ncomp=rb(n0n + stn, lambda r: 'vm_compute; reflexivity', lo=1),
        rsound=rb(n0r + str_, lambda r: reach('rarm%d' % r)),
        rcomp=rb(n0r + str_, lambda r: 'vm_compute; reflexivity'),
        rlia=rb(n0r + str_, lambda r: 'vm_compute; lia'),
        fvis=''.join(
            ('  - left. intros r Hr.\n' + rb(n0r + str_, lambda r: 'vm_compute; reflexivity')
             + '  exfalso; lia.\n')
            if cd['how'][(q_, s_)] == 'R' else
            ('  - right. split; [discriminate|]. intros r H0 Hr.\n'
             + rb(n0n + stn, lambda r: 'vm_compute; reflexivity', lo=1) + '  exfalso; lia.\n')
            for q_ in range(4) for s_ in range(2) if (q_, s_) in cd['how']).rstrip('\n'),
        t0=t0, x0=clist(cd['boot']['x'], str), m0=cd['boot']['m'],
        tmb=('tm_%s' % mid) if E.TR_QH is not None else 'tm'))
    common = dict(mid=mid, a=a, c=c, n0i=n0i, sti=sti, n0n=n0n, stn=stn,
                  n0r=n0r, str=str_, x0=clist(cd['boot']['x'], str),
                  m0=cd['boot']['m'], t0=t0)
    args = ARGS % common
    if E.TR_QH is not None:
        call = CALL % dict(common, board='boardR_qhtrZ')
        L.append(QH % dict(mid=mid, t0=t0, call=call, args=args))
    else:
        call = CALL % dict(common, board='boardR_neverqhtrZ')
        L.append(NQH % dict(mid=mid, call=call, args=args))
    return ''.join(L), cd


RUN = None


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
        raise SystemExit('%s: not a marker terminator-run row' % args.spec)
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
    seq = visits_seq(spec, det)
    d0, d1, a, c, z = read_law(seq)
    boot = next(((t, x, m) for t, x, m in seq if t > lastf), None)
    if boot is None:
        raise SystemExit('%s: no boot past %d' % (spec, lastf))
    if args.qh:
        E.TR_QH = boot[0]
    tab = E.parse_tm(spec)
    xs = [0 if w == d0 else 1 for w in boot[1]]
    global RUN
    RUN = (det, tab, d0, d1, a, c, dict(t=boot[0], x=xs, m=boot[2]), z)
    # emit_ladder's header and Fam record: the digits, the prefix, the anchor
    q, hs, side = det['anchor']
    cert = dict(spec=spec, ladder=[], arms=[],
                family=dict(base=2, digits=[[int(ch) for ch in d0], [int(ch) for ch in d1]],
                            near_head_prefix=[int(ch) for ch in det['pre']],
                            terminator=[], terminators_by_phase=[[]], code='binary',
                            value_step_per_anchor_visit=1, state='ABCD'[q], head=hs,
                            side=side, other_side_cells=[]),
                fill=dict(widens_by=1, target_prefix=[], target_fill_digit=0,
                          target_suffix=[1], lands_in_phase=0))
    E.emit_closure = emit_closure_run
    good, bad, cd = E.emit(cert, args.out)
    print('%s: closure %s' % (args.out, 'BUILT' if cd else 'not built'))
    return 0 if cd else 1


if __name__ == '__main__':
    sys.exit(main())
