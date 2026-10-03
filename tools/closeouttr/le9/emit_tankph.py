#!/usr/bin/env python3
"""UNTRUSTED emitter (SCOPING_INSTR 7.4.LE9): a counter that widens into a
tank, with a cycle of suffix PHASES between the refills -> a Coq board
closed by [LadderCheckTankPhTr].

The model (one JSON record, `le9/tankph_models.jsonl`):

    {"spec": ..., "anchor": [q, hs, "L"|"R"], "pre": "", "D": [D0, D1],
     "T": tank word, "phases": [{"suf": "..", "kz": 0|1, "z": [..], "a": n}, ...]}

Phase p's fill goes to phase p + 1 (mod the phase count); with [kz] it keeps
the width (`x = 0^k ++ z`, `m = a`), else it refills the tank (`x = z`,
`m = k + a`).  The machine, the header and the [Fam] record are
`emit_ladder.emit`'s; the arms are LE3's arm search ([LadderNest] segment
programs):

* interior `r`: `t^r 0 X -> 0^r 1 X`, the rest of the counter opaque;
* widening `r >= 0`: `t^r T X -> 0^r 1 X`;
* fill of phase `p`, `r > 0`: `t^r suf_p -> fill_p`, both tails known empty.

The fires are read from every fill arm of one phase per instruction.

    python3 emit_tankph.py SPEC MODELS.jsonl -o OUT.v [--qh]
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


def cells(s):
    return tuple(int(ch) for ch in s)


def nphase(m):
    return len(m['phases'])


def nxt(m, p):
    return 0 if p + 1 == nphase(m) else p + 1


def read(m, st):
    """(x, m, p) of a head-out cell string, or None"""
    l = len(m['D'][0])
    for p, ph in enumerate(m['phases']):
        for k in range(l + 1):
            b = st + '0' * k
            if not b.startswith(m['pre']) or not b.endswith(ph['suf']):
                continue
            b = b[len(m['pre']):len(b) - len(ph['suf'])]
            if len(b) % l:
                continue
            ws = [b[i:i + l] for i in range(0, len(b), l)]
            x = []
            i = 0
            while i < len(ws) and ws[i] in m['D']:
                x.append(m['D'].index(ws[i]))
                i += 1
            if all(w == m['T'] for w in ws[i:]):
                return x, len(ws) - i, p
    return None


def boot_of(spec, m, lastf, steps=600000):
    """(t, x, m, p) at the first anchor visit past lastf that reads, with
    [x] nonempty or a tank"""
    q0, s0, side = m['anchor']
    tm = E.parse_tm(spec)
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
                r = read(m, st)
                if r is not None and (r[0] or r[1]):
                    return (t,) + r
        w, d, nq = tm[(q, s)]
        tape[h] = w
        h += d
        q = nq
    raise NoClosure('no boot past %d' % lastf)


def closure_data(m, tab, boot):
    q, hs, side = m['anchor']
    left = side == 'L'
    OTHER = ((), (), 0, 0, ())
    pre = cells(m['pre'])
    D = [cells(w) for w in m['D']]
    T = cells(m['T'])
    derive = Arms(tab).derive
    el, er = (not left), left

    def conf(sd):
        return (q, sd, hs, OTHER) if left else (q, OTHER, hs, sd)

    def first(fn, grid, what):
        for n0, st in grid:
            g = fn(n0, st)
            if g is not None:
                return g, n0, st
        raise NoClosure('%s: no program at any threshold and stride' % what)

    def inter_at(n0, st):
        got = []
        for r in range(n0 + st):
            s_ = 0 if r < n0 else st
            c0 = conf(blk(pre + D[1] * r, D[1], s_, D[0]))
            c1 = conf(blk(pre + D[0] * r, D[0], s_, D[1]))
            try:
                got.append((0, r, c0, c1, derive(el, er, c0, c1, 'interior r=%d' % r)))
            except NoClosure:
                return None
        return got

    def wid_at(n0, st):
        got = []
        for r in range(n0 + st):
            s_ = 0 if r < n0 else st
            c0 = conf(blk(pre + D[1] * r, D[1], s_, T))
            c1 = conf(blk(pre + D[0] * r, D[0], s_, D[1]))
            try:
                got.append((r, c0, c1, derive(el, er, c0, c1, 'widening r=%d' % r)))
            except NoClosure:
                return None
        return got

    inter, n0i, sti = first(inter_at, ARM_GRID, 'interior')
    wid, n0w, stw = first(wid_at, ARM_GRID, 'widening')
    grid1 = [(n0, st) for n0, st in ARM_GRID if n0 >= 1]
    fills = []
    for pi, ph in enumerate(m['phases']):
        suf = cells(ph['suf'])
        suf2 = cells(m['phases'][nxt(m, pi)]['suf'])
        Z = tuple(c for dg in ph['z'] for c in D[dg])
        a = ph['a']

        def fill_at(n0, st):
            got = []
            for r in range(1, n0 + st):
                s_ = 0 if r < n0 else st
                c0 = conf(blk(pre + D[1] * r, D[1], s_, suf))
                if ph['kz']:
                    c1s = [(0, 0, conf(blk(pre + D[0] * r, D[0], s_, Z + T * a + suf2)))]
                else:
                    c1s = [(f1, r + a - f1, conf(blk(pre + Z + T * f1, T, s_, T * (r + a - f1) + suf2)))
                           for f1 in _splits(r + a)]
                hit = None
                for f1, f2, c1 in c1s:
                    try:
                        hit = (r, f1, f2, c0, c1, derive(True, True, c0, c1, 'fill p%d r=%d' % (pi, r)))
                        break
                    except NoClosure:
                        continue
                if hit is None:
                    return None
                got.append(hit)
            return got
        fills.append(first(fill_at, grid1, 'fill of phase %d' % pi))
    want = [(q_, s_) for q_ in range(4) for s_ in range(2) if (q_, s_) not in E.TR_PINS]
    seen = []
    for g, _n0, _st in fills:
        seen.append({r: nvisits(tab, want, c0, ch) for r, _f1, _f2, c0, _c1, ch in g})
    vph = {}
    for i in want:
        for pi in range(len(fills)):
            if all(i in seen[pi][r] for r in seen[pi]):
                vph[i] = pi
                break
        else:
            raise NoClosure('instruction %s%d fires in no phase\'s fill arms' % ('ABCD'[i[0]], i[1]))
    return dict(nest=True, el=el, er=er, inter=inter, n0i=n0i, sti=sti, wid=wid, n0w=n0w,
                stw=stw, fills=fills, seen=seen, vph=vph, want=want, T=T, boot=boot)


HEAD = '''
(** ** The closure: a counter that widens into a TANK, with phases
    ([LadderCheckTankPhTr])

    The counter side is [pre ++ x ++ T^m ++ suf_p], [x] binary over the two
    digit words, [T = %(Tw)s], %(np)d phases (suffixes %(sufs)s): inside a
    width [x] counts; at its top [x] widens by a digit and the tank loses a
    word; with the tank empty phase [p] FILLS and the next phase begins.
    Interior arms at threshold %(n0i)d stride %(sti)d, widening arms at
    %(n0w)d / %(stw)d.  Every arm is a [LadderNest] segment program. *)
From BBB4.Checkers Require Import LadderCheckTankPhTr.

Definition tankT_%(mid)s : list Sym := %(Tc)s.
Definition sufp_%(mid)s (p : nat) : list Sym := match p with %(sufb)s end.
Definition kzp_%(mid)s (p : nat) : bool := match p with %(kzb)s end.
Definition zp_%(mid)s (p : nat) : list nat := match p with %(zb)s end.
Definition ap_%(mid)s (p : nat) : nat := match p with %(ab)s end.
Definition n0r_%(mid)s (p : nat) : nat := match p with %(n0rb)s end.
Definition str_%(mid)s (p : nat) : nat := match p with %(strb)s end.

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

Lemma warm_reach_%(mid)s : forall r, r < %(n0w)d + %(stw)d ->
  ReachL tm (negb (fm_left FAM)) (fm_left FAM) (lr_lhs (warm_%(mid)s r)) (lr_rhs (warm_%(mid)s r)).
Proof.
  intros r Hr.
%(wsound)s  exfalso; lia.
Qed.

Lemma warm_lhs_%(mid)s : forall r, r < %(n0w)d + %(stw)d ->
  lr_lhs (warm_%(mid)s r) = cls_conf FAM (blk (fm_pre FAM ++ rep (dig FAM (fm_b FAM - 1)) r)
    (dig FAM (fm_b FAM - 1)) (astride %(n0w)d %(stw)d r) tankT_%(mid)s).
Proof.
  intros r Hr.
%(wcomp)s  exfalso; lia.
Qed.

Lemma warm_rhs_%(mid)s : forall r, r < %(n0w)d + %(stw)d ->
  lr_rhs (warm_%(mid)s r) = cls_conf FAM (blk (fm_pre FAM ++ rep (dig FAM 0) r)
    (dig FAM 0) (astride %(n0w)d %(stw)d r) (dig FAM 1)).
Proof.
  intros r Hr.
%(wcomp)s  exfalso; lia.
Qed.

Lemma rarm_reach_%(mid)s : forall p r, p < %(np)d -> 0 < r -> r < n0r_%(mid)s p + str_%(mid)s p ->
  ReachL tm true true (lr_lhs (rarm_%(mid)s p r)) (lr_rhs (rarm_%(mid)s p r)).
Proof.
  intros p r Hp H0 Hr.
%(rsound)s  exfalso; lia.
Qed.

Lemma rarm_lhs_%(mid)s : forall p r, p < %(np)d -> 0 < r -> r < n0r_%(mid)s p + str_%(mid)s p ->
  lr_lhs (rarm_%(mid)s p r) = cls_conf FAM (blk (fm_pre FAM ++ rep (dig FAM (fm_b FAM - 1)) r)
    (dig FAM (fm_b FAM - 1)) (astride (n0r_%(mid)s p) (str_%(mid)s p) r) (sufp_%(mid)s p)).
Proof.
  intros p r Hp H0 Hr.
%(rcomp)s  exfalso; lia.
Qed.

Lemma rarm_rhs_%(mid)s : forall p r, p < %(np)d -> 0 < r -> r < n0r_%(mid)s p + str_%(mid)s p ->
  lr_rhs (rarm_%(mid)s p r) =
    if kzp_%(mid)s p
    then cls_conf FAM (blk (fm_pre FAM ++ rep (dig FAM 0) r) (dig FAM 0)
                         (astride (n0r_%(mid)s p) (str_%(mid)s p) r)
                         (flat_map (dig FAM) (zp_%(mid)s p) ++ rep tankT_%(mid)s (ap_%(mid)s p)
                          ++ sufp_%(mid)s (nxtP %(np)d p)))
    else cls_conf FAM (blk (fm_pre FAM ++ flat_map (dig FAM) (zp_%(mid)s p)
                              ++ rep tankT_%(mid)s (fm1_%(mid)s p r)) tankT_%(mid)s
                         (astride (n0r_%(mid)s p) (str_%(mid)s p) r)
                         (rep tankT_%(mid)s (fm2_%(mid)s p r) ++ sufp_%(mid)s (nxtP %(np)d p))).
Proof.
  intros p r Hp H0 Hr.
%(rcomp)s  exfalso; lia.
Qed.

Lemma fm_%(mid)s : forall p r, p < %(np)d -> 0 < r -> r < n0r_%(mid)s p + str_%(mid)s p ->
  kzp_%(mid)s p = false -> fm1_%(mid)s p r + fm2_%(mid)s p r = r + ap_%(mid)s p.
Proof.
  intros p r Hp H0 Hr.
%(rlia)s  exfalso; lia.
Qed.

Lemma vph_ok_%(mid)s : forall t, ~ In t pins_%(mid)s -> vph_%(mid)s t < %(np)d.
Proof. intros [q s] _. destruct q, s; vm_compute; lia. Qed.

Lemma vis_ok_%(mid)s : forall t, ~ In t pins_%(mid)s -> forall r, 0 < r ->
  r < n0r_%(mid)s (vph_%(mid)s t) + str_%(mid)s (vph_%(mid)s t) ->
  nfire tm true true nrules (vsegs_%(mid)s r t) (vis_%(mid)s r t)
    (lr_lhs (rarm_%(mid)s (vph_%(mid)s t) r)) = Some t.
Proof.
  intros t Hnp. destruct t as [q s]; destruct q, s; try (exfalso; apply Hnp; simpl; tauto);
  intros r H0 Hr; vm_compute in Hr.
%(fvis)s
Qed.

Lemma inv0_%(mid)s : PInv FAM %(np)d (%(x0)s, %(m0)d, %(p0)d).
Proof. vm_compute. split; [repeat constructor|]. split; [%(ne)s | lia]. Qed.

Lemma bootl_%(mid)s :
  stepn %(tmb)s %(t0)d InitES = Some (lift (pcfg FAM tankT_%(mid)s sufp_%(mid)s (%(x0)s, %(m0)d, %(p0)d))).
Proof.
  assert (H : match csteps %(tmb)s %(t0)d c0 with
              | Some c => ceqb c (pcfg FAM tankT_%(mid)s sufp_%(mid)s (%(x0)s, %(m0)d, %(p0)d))
              | None => false end = true) by (vm_compute; reflexivity).
  destruct (csteps %(tmb)s %(t0)d c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

'''

ARGS = '''  - vm_compute; lia.
  - lia.
  - intros p Hp. destruct p as [|p]; [vm_compute; repeat constructor|].
%(hz)s    exfalso; lia.
  - exact inv0_%(mid)s.
  - lia.
  - exact iarm_reach_%(mid)s.
  - exact iarm_lhs_%(mid)s.
  - exact iarm_rhs_%(mid)s.
  - lia.
  - exact warm_reach_%(mid)s.
  - exact warm_lhs_%(mid)s.
  - exact warm_rhs_%(mid)s.
  - intros p Hp. destruct p as [|p]; [vm_compute; lia|].
%(hst)s    exfalso; lia.
  - intros p Hp. destruct p as [|p]; [vm_compute; lia|].
%(hst)s    exfalso; lia.
  - exact rarm_reach_%(mid)s.
  - exact rarm_lhs_%(mid)s.
  - exact rarm_rhs_%(mid)s.
  - exact fm_%(mid)s.
  - exact nrules_sound_%(mid)s.
  - exact vph_ok_%(mid)s.
  - exact vis_ok_%(mid)s.
  - exact bootl_%(mid)s.
'''

CALL = '''(%(board)s tm_%(mid)s pins_%(mid)s FAM tankT_%(mid)s %(np)d sufp_%(mid)s kzp_%(mid)s
                 zp_%(mid)s ap_%(mid)s
                 iarm_%(mid)s %(n0i)d %(sti)d warm_%(mid)s %(n0w)d %(stw)d
                 rarm_%(mid)s n0r_%(mid)s str_%(mid)s fm1_%(mid)s fm2_%(mid)s
                 nrules vph_%(mid)s vsegs_%(mid)s vis_%(mid)s %(x0)s %(m0)d %(p0)d)'''

NQH = '''(** The machine-level theorem, at the INSTRUCTION level, through
    [LadderCheckTankPhTr.boardP_neverqhtr]. *)
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
    [LadderCheckTankPhTr.boardP_qhtr]. *)
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
  match r with %(wb)s | _ => warm0_%(mid)s end.
Definition rarm_%(mid)s (p r : nat) : LRule :=
  match p, r with %(rb)s | _, _ => %(r1)s_%(mid)s end.
Definition fm1_%(mid)s (p r : nat) : nat := match p, r with %(b1)s | _, _ => 0 end.
Definition fm2_%(mid)s (p r : nat) : nat := match p, r with %(b2)s | _, _ => 0 end.
Definition vph_%(mid)s (t : Instr) : nat :=
  match t with
  %(phb)s
  end.

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


def pmatch(m, f):
    """`| 0 => .. | 1 => .. | _ => (last)` over the phases"""
    n = nphase(m)
    return ' '.join('| %s => %s' % ('_' if p == n - 1 else str(p), f(p)) for p in range(n))


def emit_closure_tankph(cert, tab, mid):
    m = RUN[0]
    cd = S.two_pass(lambda _c, _t: closure_data(*RUN), cert, tab)
    if isinstance(cd, NoClosure):
        return E.CLOSURE_NONE % cd, None
    n0i, sti, n0w, stw = cd['n0i'], cd['sti'], cd['n0w'], cd['stw']
    el, er = cd['el'], cd['er']
    np_ = nphase(m)
    fills = cd['fills']
    L = [HEAD % dict(
        mid=mid, Tw=m['T'], np=np_, sufs=', '.join('[%s]' % p['suf'] for p in m['phases']),
        n0i=n0i, sti=sti, n0w=n0w, stw=stw, Tc=syms(cd['T']),
        sufb=pmatch(m, lambda p: syms(cells(m['phases'][p]['suf']))),
        kzb=pmatch(m, lambda p: 'true' if m['phases'][p]['kz'] else 'false'),
        zb=pmatch(m, lambda p: clist(m['phases'][p]['z'], str)),
        ab=pmatch(m, lambda p: str(m['phases'][p]['a'])),
        n0rb=pmatch(m, lambda p: str(fills[p][1])),
        strb=pmatch(m, lambda p: str(fills[p][2])))]
    inner, arms = [], []
    for d, r, c0, c1, ch in cd['inter']:
        arms.append(('iarm0_%d_%d' % (d, r), c0, c1, prog_coq(tab, inner, ch), el, er))
    for r, c0, c1, ch in cd['wid']:
        arms.append(('warm%d' % r, c0, c1, prog_coq(tab, inner, ch), el, er))
    offs = {}
    for p, (g, _n0, _st) in enumerate(fills):
        for r, _f1, _f2, c0, c1, ch in g:
            offs[(p, r)] = len(inner)
            arms.append(('rarm%d_%d' % (p, r), c0, c1, prog_coq(tab, inner, ch), True, True))
    L.append(inner_coq(mid, inner))
    for nm, c0, c1, segs, el_, er_ in arms:
        L.append(ARM % dict(nm=nm, mid=mid, lhs=coq_conf(c0), rhs=coq_conf(c1),
                            segs=';\n   '.join(segs), el=str(el_).lower(), er=str(er_).lower()))
    vph = cd['vph']
    seen = cd['seen']
    vis = [(r, i, seen[vph[i]][r][i], vph[i]) for i in sorted(vph) for r in sorted(seen[vph[i]])]
    L.append(TABLES % dict(
        mid=mid, r1='rarm0_%d' % fills[0][0][0][0],
        ib=' '.join('| %d, %d => iarm0_%d_%d_%s' % (d, r, d, r, mid) for d, r, *_ in cd['inter']),
        wb=' '.join('| %d => warm%d_%s' % (r, r, mid) for r, *_ in cd['wid']),
        rb=' '.join('| %d, %d => rarm%d_%d_%s' % (p, r, p, r, mid)
                    for p, (g, _a, _b) in enumerate(fills) for r, *_ in g),
        b1=' '.join('| %d, %d => %d' % (p, r, f1)
                    for p, (g, _a, _b) in enumerate(fills) for r, f1, *_ in g),
        b2=' '.join('| %d, %d => %d' % (p, r, f2)
                    for p, (g, _a, _b) in enumerate(fills) for r, _f1, f2, *_ in g),
        phb='\n  '.join(['| (%s, %s) => %d' % (ST[i[0]], SYM[i[1]], vph[i]) for i in sorted(vph)]
                        + ([] if len(vph) == 8 else ['| _ => 0'])),
        vb='\n  '.join('| %d, (%s, %s) => %s' % (r, ST[i[0]], SYM[i[1]], coq_chain_l(v[1]))
                       for r, i, v, _p in vis),
        sb='\n  '.join('| %d, (%s, %s) => [%s]'
                       % (r, ST[i[0]], SYM[i[1]], '; '.join(coq_seg(sg, offs[(p, r)]) for sg in v[0]))
                       for r, i, v, p in vis)))

    def reach(nm):
        return ('eapply narm_reach; [exact nrules_sound_%s | exact ok_%s_%s]' % (mid, nm, mid))

    def rb(n, body, lo=0, ind='  '):
        return ''.join('%sdestruct r as [|r].\n%s{ %s. }\n'
                       % (ind, ind, 'exfalso; lia' if r < lo else body(r)) for r in range(n))

    def pb(body):
        out = ''
        for p, (g, n0, st) in enumerate(fills):
            out += '  destruct p as [|p].\n  { vm_compute in Hr.\n%s    exfalso; lia. }\n' % (
                rb(n0 + st, lambda r, p=p: body(p, r), lo=1, ind='    '))
        return out

    vm = 'vm_compute; reflexivity'
    t0, x0, m0, p0 = cd['boot']
    fvis = []
    for q_ in range(4):
        for s_ in range(2):
            if (q_, s_) not in cd['want']:
                continue
            g, n0, st = fills[vph[(q_, s_)]]
            fvis.append('  - ' + rb(n0 + st, lambda r: vm, lo=1).lstrip() + '    exfalso; lia.')
    L.append(THM % dict(
        mid=mid, n0i=n0i, sti=sti, n0w=n0w, stw=stw, np=np_,
        isound=rb(n0i + sti, lambda r: reach('iarm0_0_%d' % r)),
        icomp=rb(n0i + sti, lambda r: vm),
        wsound=rb(n0w + stw, lambda r: reach('warm%d' % r)),
        wcomp=rb(n0w + stw, lambda r: vm),
        rsound=pb(lambda p, r: reach('rarm%d_%d' % (p, r))),
        rcomp=pb(lambda p, r: vm),
        rlia=pb(lambda p, r: 'vm_compute; intros; lia'),
        fvis='\n'.join(fvis),
        t0=t0, x0=clist(x0, str), m0=m0, p0=p0,
        ne='left; discriminate' if x0 else 'right; lia',
        tmb=('tm_%s' % mid) if E.TR_QH is not None else 'tm'))
    hz = ''.join('    destruct p as [|p]; [vm_compute; repeat constructor|].\n'
                 for _ in range(np_ - 1))
    hst = ''.join('    destruct p as [|p]; [vm_compute; lia|].\n' for _ in range(np_ - 1))
    common = dict(mid=mid, np=np_, n0i=n0i, sti=sti, n0w=n0w, stw=stw,
                  x0=clist(x0, str), m0=m0, p0=p0, t0=t0)
    args = ARGS % dict(common, hz=hz, hst=hst)
    if E.TR_QH is not None:
        L.append(QH % dict(mid=mid, t0=t0, call=CALL % dict(common, board='boardP_qhtr'),
                           args=args))
    else:
        L.append(NQH % dict(mid=mid, call=CALL % dict(common, board='boardP_neverqhtr'),
                            args=args))
    return ''.join(L), cd


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('spec')
    ap.add_argument('models')
    ap.add_argument('-o', '--out', required=True)
    ap.add_argument('--qh', action='store_true')
    ap.add_argument('--scan', default=os.path.join(HERE, '..', '..', '..',
                                                   'censustr_v9_scan_1e8.txt'))
    args = ap.parse_args()
    m = None
    for l in open(args.models):
        r = json.loads(l)
        if r['spec'] == args.spec:
            m = r
    if m is None:
        raise SystemExit('%s: no model' % args.spec)
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
    boot = boot_of(spec, m, lastf)
    if args.qh:
        E.TR_QH = boot[0]
    tab = E.parse_tm(spec)
    global RUN
    RUN = (m, tab, boot)
    q, hs, side = m['anchor']
    cert = dict(spec=spec, ladder=[], arms=[],
                family=dict(base=2, digits=[[int(ch) for ch in w] for w in m['D']],
                            near_head_prefix=[int(ch) for ch in m['pre']],
                            terminator=[], terminators_by_phase=[[]], code='binary',
                            value_step_per_anchor_visit=1, state='ABCD'[q], head=hs,
                            side=side, other_side_cells=[]),
                fill=dict(widens_by=1, target_prefix=[], target_fill_digit=0,
                          target_suffix=[1], lands_in_phase=0))
    E.emit_closure = emit_closure_tankph
    good, bad, cd = E.emit(cert, args.out)
    print('%s: closure %s' % (args.out, 'BUILT' if cd else 'not built'))
    return 0 if cd else 1


if __name__ == '__main__':
    sys.exit(main())
