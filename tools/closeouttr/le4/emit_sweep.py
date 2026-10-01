#!/usr/bin/env python3
"""UNTRUSTED emitter: a `pos_detect.py` certificate whose carry SWEEPS the run
of top digits after the digit it increments -> a Coq board closed by
[LadderCheckSweepTr] (SCOPING_INSTR 7.4.LE4).

The interior increment of `t^n d t^m e Y` is three one-index programs:

  carry      A d ra      anchor -> the pivot (head on the last cell of d+1),
                         the rest of the counter X opaque;
  excursion  P d k ph rm the pivot -> across t^m to e (kind k = e) or to the
                         terminator (k = b-1) and back to the pivot, the
                         tape unchanged, both tails opaque;
  return     C d k ra    the pivot -> the anchor.

The pivot's state and head and the return's are read off a simulation of
small concrete increments and must be the same for every n, m (else no
board).  The fill arms and the visits are `emit_ladder`'s shapes, derived
with emit_step's arm search; the header and the [Fam] record are
`emit_ladder.emit`'s.

    python3 emit_sweep.py CERT.json -o OUT.v [--qh]
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
                       coq_seg, clist, ST, SYM, _splits, _rstrip0, Arms, nvisits,
                       prog_coq, inner_coq, ARM, BOOTL)

EMPTY = ((), (), 0, 0, ())


def sim_inc(tab, fam, n, d, m, k, ph, steps=200000):
    """(q1, h1, pivot far side, q2, h2) of one increment of
    t^n d t^m e Y (k = e < b-1) or t^n d t^m T (k = b-1), or NoClosure"""
    digs = [list(w) for w in fam['digits']]
    b = fam['base']
    t, z = digs[b - 1], digs[0]
    pre = list(fam['near_head_prefix'])
    tails = fam.get('terminators_by_phase') or [fam['terminator']]
    T = list(tails[ph])
    left = fam['side'] == 'L'
    sg = -1 if left else 1
    if k < b - 1:
        tailw = digs[k] + z + z + T
    else:
        tailw = T
    cells = pre + t * n + digs[d] + t * m + tailw
    tape = {}
    for i, x in enumerate(cells):
        tape[sg * (i + 1)] = x
    for i, x in enumerate(fam['other_side_cells']):
        tape[-sg * (i + 1)] = x
    tape[0] = fam['head']
    q0 = ord(fam['state']) - 65
    q, h = q0, 0
    piv = sg * (len(pre) + len(t) * n + len(digs[d]))
    xs = piv + sg
    want = pre + z * n + digs[d + 1] + t * m + tailw
    inx = lambda p: (p - xs) * sg >= 0  # noqa: E731
    stage, rec = 0, {}
    for _ in range(steps):
        if stage == 2 and h == 0 and q == q0:
            break
        sym = tape.get(h, 0)
        tr = tab.get((q, sym))
        if tr is None:
            raise NoClosure('sweep: halts in a concrete increment')
        w, mv, nq = tr
        nh = h + (1 if mv == 'R' or mv == 1 else -1)
        if stage == 0 and h == piv and inx(nh):
            # the pivot: about to step into X
            far = []
            p = piv - sg
            lim = min(tape) if sg > 0 else max(tape)   # everything written on the far side
            while (p - lim) * sg >= 0:
                far.append(tape.get(p, 0))
                p -= sg
            far = _rstrip0(far)
            rec.update(q1=q, h1=sym, far=far)
            stage = 1
        elif stage == 0 and inx(h):
            raise NoClosure('sweep: the carry enters X before its pivot')
        elif stage == 1 and h == piv and not inx(h):
            rec.update(q2=q, h2=sym)
            for i, x in enumerate(t * m + tailw):
                if tape.get(xs + sg * i, 0) != x:
                    raise NoClosure('sweep: the excursion changes the tape')
            stage = 2
        elif stage == 2 and inx(h):
            raise NoClosure('sweep: a second excursion')
        tape[h] = w
        h = nh
        q = nq
    else:
        raise NoClosure('sweep: no return to the anchor')
    if stage != 2:
        raise NoClosure('sweep: no excursion')
    for i, x in enumerate(want):
        if tape.get(sg * (i + 1), 0) != x:
            raise NoClosure('sweep: the increment is not the successor')
    return rec


def closure_data_sweep(cert, tab):
    fam = cert['family']
    fills = cert.get('fill_by_phase') or [cert['fill']]
    nph = len(fills)
    if nph != 1:
        raise NoClosure('%d phases: emit_sweep states one' % nph)
    if fam.get('code') != 'binary' or fam.get('value_step_per_anchor_visit', 1) != 1:
        raise NoClosure('LadderCheckSweepTr states (Binary, 1)')
    b = fam['base']
    digs = [tuple(w) for w in fam['digits']]
    t, z = digs[b - 1], digs[0]
    pre = tuple(fam['near_head_prefix'])
    tails = [tuple(x) for x in (fam.get('terminators_by_phase') or [fam['terminator']])]
    other = tuple(fam['other_side_cells'])
    q, hs = ord(fam['state']) - 65, fam['head']
    left = fam['side'] == 'L'
    OTHER = (other, (), 0, 0, ())
    E.TR_TAB = tab
    stab = {k: (None if v is None else (v[0], v[1], v[2])) for k, v in tab.items()}

    def conf(sd):
        return (q, sd, hs, OTHER) if left else (q, OTHER, hs, sd)

    def piv(qq, far, hh, ctr):
        return (qq, ctr, hh, far) if left else (qq, far, hh, ctr)

    derive = Arms(tab).derive
    el, er = (not left), left
    # the pivot and the return, per digit and kind, from simulation
    pv_, wus = {}, {}
    for d in range(b - 1):
        for k in range(b):
            for ph in range(nph):
                recs = [sim_inc(stab, fam, n, d, m, k, ph) for n in (0, 1, 2, 3) for m in (0, 1, 2, 4)]
                q1s = set((r['q1'], r['h1']) for r in recs)
                q2s = set((r['q2'], r['h2']) for r in recs)
                if len(q1s) != 1 or len(q2s) != 1:
                    raise NoClosure('sweep: the pivot or the return varies (d=%d k=%d)' % (d, k))
                # the far side at the pivot: rev(W[:-1]) rev(U)^n rev(pre), then
                # the anchor cell and the far side; W is the digit's word (old or
                # new) and U the run's (carried or not yet)
                wu = None
                # W may be a transient word the carry is half-way through writing
                r0 = sim_inc(stab, fam, 0, d, 0, k, ph)
                lw = len(digs[d])
                Wsim = list(reversed(r0['far'][:lw - 1])) + [r0['h1']]
                for W, U in ((digs[d + 1], z), (digs[d], t), (digs[d + 1], t), (digs[d], z),
                             (Wsim, t), (Wsim, z)):
                    ok = True
                    for n in (0, 1, 2, 3):
                        r = sim_inc(stab, fam, n, d, 0, k, ph)
                        exp_ = (list(reversed(W[:-1])) + list(reversed(U)) * n
                                + list(reversed(pre)))
                        if r['far'][:len(exp_)] != exp_ or r['h1'] != W[-1]:
                            ok = False
                            break
                    if ok:
                        wu = (tuple(W), tuple(U))
                        break
                if wu is None:
                    raise NoClosure('sweep: the far side at the pivot is not a run of one word')
                if wus.setdefault(d, wu) != wu:
                    raise NoClosure('sweep: the far side at the pivot depends on the kind')
                pv_[(d, k, ph)] = (q1s.pop(), q2s.pop())
    # the far side beyond the digit and the run: [hs'] ++ other, read at n = 0
    farrest = {}
    for d in range(b - 1):
        r = sim_inc(stab, fam, 0, d, 0, b - 1, 0)
        k0 = len(wus[d][0]) - 1 + len(pre)
        farrest[d] = tuple(_rstrip0(r['far'][k0:]))
    for (d, k, ph), ((q1, h1), _x) in pv_.items():
        if (q1, h1) != pv_[(d, 0, 0)][0]:
            raise NoClosure('sweep: the pivot depends on the kind')

    def far_at(d, ra, s_, alt=0):
        """the pivot's far side for a carry of index ra, stride s_: the ra
        concrete copies after the block (alt 0) or before it (alt 1)"""
        W, U = wus[d]
        near = tuple(reversed(W[:-1]))
        ru = tuple(reversed(U))
        rest = tuple(reversed(pre)) + farrest[d]
        if s_ == 0:
            return (near + ru * ra + rest, (), 0, 0, ())
        if alt:
            return (near + ru * ra, ru * s_, 1, 0, rest)
        return (near, ru * s_, 1, 0, ru * ra + rest)

    def carry_at(n0, st):
        got = []
        for d in range(b - 1):
            (q1, h1), _ = pv_[(d, 0, 0)]
            for ra in range(n0 + st):
                s_ = 0 if ra < n0 else st
                hit = None
                for alt in ((0,) if s_ == 0 else (0, 1)):
                    c0 = conf(blk(pre + t * ra, t, s_, digs[d]))
                    c1 = piv(q1, far_at(d, ra, s_, alt), h1, EMPTY)
                    try:
                        arm = (d, ra, c0, c1, derive(el, er, c0, c1, 'carry d=%d r=%d' % (d, ra)))
                    except NoClosure:
                        continue
                    rets = []
                    for k in range(b):
                        (_q1, _h1), (q2, h2) = pv_[(d, k, 0)]
                        c0r = piv(q2, far_at(d, ra, s_, alt), h2, EMPTY)
                        c1r = conf(blk(pre + z * ra, z, s_, digs[d + 1]))
                        try:
                            rets.append((('C', d, k), ra, c0r, c1r,
                                         derive(el, er, c0r, c1r,
                                                'return d=%d k=%d r=%d' % (d, k, ra))))
                        except NoClosure:
                            rets = None
                            break
                    if rets is not None:
                        hit = [arm] + rets
                        break
                if hit is None:
                    return None
                got.extend(hit)
        return got

    def exc_at(n0, st):
        got = []
        for d in range(b - 1):
            for k in range(b):
                for ph in range(nph):
                    (q1, h1), (q2, h2) = pv_[(d, k, ph)]
                    Ew = digs[k] if k < b - 1 else tails[ph]
                    pel = (k == b - 1) and left
                    per = (k == b - 1) and not left
                    for rm in range(n0 + st):
                        s_ = 0 if rm < n0 else st
                        ctr = blk(t * rm, t, s_, Ew)
                        c0 = piv(q1, EMPTY, h1, ctr)
                        c1 = piv(q2, EMPTY, h2, ctr)
                        try:
                            got.append((d, k, ph, rm, c0, c1, pel, per,
                                        derive(pel, per, c0, c1,
                                               'excursion d=%d k=%d r=%d' % (d, k, rm))))
                        except NoClosure:
                            return None
        return got

    def fill_at(n0, st):
        got = []
        for ph in range(nph):
            f = fills[ph]
            P, S_, mid, sw = f['target_prefix'], f['target_suffix'], f['target_fill_digit'], f['widens_by']
            to = f['lands_in_phase']
            for r in range(1, n0 + st):
                s_ = 0 if r < n0 else st
                c0 = conf(blk(pre + t * r, t, s_, tails[ph]))
                tot = r + sw - len(P) - len(S_)
                hit = None
                for f1 in _splits(tot):
                    c1 = conf(blk(pre + tuple(x for dd in P for x in digs[dd]) + digs[mid] * f1,
                                  digs[mid], s_,
                                  digs[mid] * (tot - f1) + tuple(x for dd in S_ for x in digs[dd])
                                  + tails[to]))
                    try:
                        hit = (r, ph, f1, tot - f1, c0, c1,
                               derive(True, True, c0, c1, 'fill r=%d' % r))
                        break
                    except NoClosure:
                        continue
                if hit is None:
                    return None
                got.append(hit)
        return got

    def first(fn, grid, what):
        for n0, st in grid:
            g = fn(n0, st)
            if g is not None:
                return g, n0, st
        raise NoClosure('%s: no program at any threshold and stride' % what)

    ac, n0a, sta = first(carry_at, ARM_GRID, 'carry/return')
    ex, n0p, stp = first(exc_at, ARM_GRID, 'excursion')
    want = [(q_, s_) for q_ in range(4) for s_ in range(2) if (q_, s_) not in E.TR_PINS]
    fl = nvis = None
    pv0 = 0
    for n0, st in [(n0, st) for n0, st in ARM_GRID if n0 >= 1]:
        g = fill_at(n0, st)
        if g is None:
            continue
        seen = {r: nvisits(tab, want, c0, ch) for r, ph, _f1, _f2, c0, _c1, ch in g if ph == pv0}
        if all(i in seen[r] for r in seen for i in want):
            fl, n0f, stf = g, n0, st
            nvis = {r: {i: seen[r][i] for i in want} for r in seen}
            break
    if fl is None:
        raise NoClosure('fill: no program, or an instruction no fill anchor fires')
    return dict(nest=True, el=el, er=er, ac=ac, n0a=n0a, sta=sta, ex=ex, n0p=n0p,
                stp=stp, fl=fl, n0f=n0f, stf=stf, nvis=nvis, nph=nph, b=b,
                boot=cert['boot'], fill=fl)


HEAD = '''
(** ** The closure: a counter whose carry SWEEPS the run after its digit
    ([LadderCheckSweepTr])

    Carry and return arms at threshold %(n0a)d stride %(sta)d, excursion arms
    at %(n0p)d / %(stp)d, fill arms at %(n0f)d / %(stf)d.  Every arm is a
    [LadderNest] segment program. *)
From BBB4.Checkers Require Import LadderCheckSweepTr.

'''


def emit_closure_sweep(cert, tab, mid):
    cd = S.two_pass(closure_data_sweep, cert, tab)
    if isinstance(cd, NoClosure):
        return E.CLOSURE_NONE % cd, None
    b, nph = cd['b'], cd['nph']
    n0a, sta, n0p, stp, n0f, stf = (cd[x] for x in ('n0a', 'sta', 'n0p', 'stp', 'n0f', 'stf'))
    el, er = cd['el'], cd['er']
    L = [HEAD % dict(n0a=n0a, sta=sta, n0p=n0p, stp=stp, n0f=n0f, stf=stf)]
    inner, arms = [], []
    disp_a, disp_c, disp_p, disp_f = [], [], [], []
    for key, ra, c0, c1, ch in cd['ac']:
        if isinstance(key, tuple):
            _c, d, k = key
            nm = 'carc%d_%d_%d' % (d, k, ra)
            disp_c.append((d, k, ra, nm))
        else:
            d = key
            nm = 'cara%d_%d' % (d, ra)
            disp_a.append((d, ra, nm))
        arms.append((nm, c0, c1, prog_coq(tab, inner, ch), el, er))
    for d, k, ph, rm, c0, c1, pel, per, ch in cd['ex']:
        nm = 'carp%d_%d_%d_%d' % (d, k, ph, rm)
        disp_p.append((d, k, ph, rm, nm))
        arms.append((nm, c0, c1, prog_coq(tab, inner, ch), pel, per))
    offs = {}
    for r, ph, f1, f2, c0, c1, ch in cd['fl']:
        nm = 'farm%d_%d' % (r, ph)
        disp_f.append((r, ph, f1, f2, nm))
        if ph == 0:
            offs[r] = len(inner)
        arms.append((nm, c0, c1, prog_coq(tab, inner, ch), True, True))
    L.append(inner_coq(mid, inner))
    for nm, c0, c1, segs, el_, er_ in arms:
        L.append(ARM % dict(nm=nm, mid=mid, lhs=coq_conf(c0), rhs=coq_conf(c1),
                            segs=';\n   '.join(segs), el=str(el_).lower(),
                            er=str(er_).lower()))
    L.append('''Definition aa_%(mid)s (d r : nat) : LRule :=
  match d, r with %(a)s | _, _ => %(a0)s_%(mid)s end.
Definition ac_%(mid)s (d k r : nat) : LRule :=
  match d, k, r with %(c)s | _, _, _ => %(c0)s_%(mid)s end.
Definition ap_%(mid)s (d k ph r : nat) : LRule :=
  match d, k, ph, r with %(p)s | _, _, _, _ => %(p0)s_%(mid)s end.
Definition af_%(mid)s (r ph : nat) : LRule :=
  match r, ph with %(f)s | _, _ => %(f0)s_%(mid)s end.
Definition fm1_%(mid)s (r ph : nat) : nat := match r, ph with %(f1)s | _, _ => 0 end.
Definition fm2_%(mid)s (r ph : nat) : nat := match r, ph with %(f2)s | _, _ => 0 end.

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
        mid=mid,
        a=' '.join('| %d, %d => %s_%s' % (d, ra, nm, mid) for d, ra, nm in disp_a),
        a0=disp_a[0][2],
        c=' '.join('| %d, %d, %d => %s_%s' % (d, k, ra, nm, mid) for d, k, ra, nm in disp_c),
        c0=disp_c[0][3],
        p=' '.join('| %d, %d, %d, %d => %s_%s' % (d, k, ph, rm, nm, mid)
                   for d, k, ph, rm, nm in disp_p),
        p0=disp_p[0][4],
        f=' '.join('| %d, %d => %s_%s' % (r, ph, nm, mid) for r, ph, _a, _b, nm in disp_f),
        f0=disp_f[0][4],
        f1=' '.join('| %d, %d => %d' % (r, ph, a) for r, ph, a, _b, _nm in disp_f),
        f2=' '.join('| %d, %d => %d' % (r, ph, b_) for r, ph, _a, b_, _nm in disp_f),
        vb='\n  '.join('| %d, (%s, %s) => %s' % (r, ST[i[0]], SYM[i[1]], coq_chain_l(v[1]))
                       for r in sorted(cd['nvis']) for i, v in sorted(cd['nvis'][r].items())),
        sb='\n  '.join('| %d, (%s, %s) => [%s]'
                       % (r, ST[i[0]], SYM[i[1]],
                          '; '.join(coq_seg(sg, offs[r]) for sg in v[0]))
                       for r in sorted(cd['nvis']) for i, v in sorted(cd['nvis'][r].items()))))

    reach = lambda nm: ('eapply narm_reach; [exact nrules_sound_%s | exact ok_%s_%s]'  # noqa: E731
                        % (mid, nm, mid))

    def cases(var, n, body, lo=0):
        """destruct var as 0..n-1, the rest absurd"""
        return ''.join('  destruct %s as [|%s].\n  {\n%s  }\n'
                       % (var, var, body(i) if i >= lo else '  exfalso; lia.\n')
                       for i in range(n)) + '  exfalso; lia.\n'
    VM = '  vm_compute; reflexivity.\n'
    VMS = '  vm_compute; split; reflexivity.\n'
    nd, nk = b - 1, b

    def dk(body):
        return cases('d', nd, lambda d: cases('k', nk, lambda k: body(d, k)))
    pr = ['Proof.']
    T_ = []
    T_.append('''Lemma aaS_%(mid)s : forall d ra, d < fm_b FAM - 1 -> ra < %(n0a)d + %(sta)d ->
  ReachL tm (negb (fm_left FAM)) (fm_left FAM) (lr_lhs (aa_%(mid)s d ra)) (lr_rhs (aa_%(mid)s d ra)).
Proof.
  intros d ra Hd Hr. vm_compute in Hd.
%(body)sQed.
''' % dict(mid=mid, n0a=n0a, sta=sta,
           body=cases('d', nd, lambda d: cases('ra', n0a + sta,
                                              lambda r: '  %s.\n' % reach('cara%d_%d' % (d, r))))))
    T_.append('''Lemma aaL_%(mid)s : forall d ra, d < fm_b FAM - 1 -> ra < %(n0a)d + %(sta)d ->
  lr_lhs (aa_%(mid)s d ra) = cls_conf FAM (cls_side FAM [] (fm_b FAM - 1) ra (astride %(n0a)d %(sta)d ra) [d]).
Proof.
  intros d ra Hd Hr. vm_compute in Hd.
%(body)sQed.

Lemma aaC_%(mid)s : forall d ra, d < fm_b FAM - 1 -> ra < %(n0a)d + %(sta)d ->
  ctrS FAM (lr_rhs (aa_%(mid)s d ra)) = sflat [].
Proof.
  intros d ra Hd Hr. vm_compute in Hd.
%(body)sQed.
''' % dict(mid=mid, n0a=n0a, sta=sta,
           body=cases('d', nd, lambda d: cases('ra', n0a + sta, lambda r: VM))))
    T_.append('''Lemma apS_%(mid)s : forall d k ph rm, d < fm_b FAM - 1 -> k < fm_b FAM -> ph < %(nph)d -> rm < %(n0p)d + %(stp)d ->
  ReachL tm ((k =? fm_b FAM - 1) && fm_left FAM) ((k =? fm_b FAM - 1) && negb (fm_left FAM))
    (lr_lhs (ap_%(mid)s d k ph rm)) (lr_rhs (ap_%(mid)s d k ph rm)).
Proof.
  intros d k ph rm Hd Hk Hp Hr. vm_compute in Hd, Hk.
%(body)sQed.
''' % dict(mid=mid, nph=nph, n0p=n0p, stp=stp,
           body=dk(lambda d, k: cases('ph', nph, lambda ph: cases(
               'rm', n0p + stp, lambda r: '  %s.\n' % reach('carp%d_%d_%d_%d' % (d, k, ph, r)))))))
    T_.append('''Lemma apQ_%(mid)s : forall d k ph rm ra, d < fm_b FAM - 1 -> k < fm_b FAM -> ph < %(nph)d -> rm < %(n0p)d + %(stp)d ->
  ra < %(n0a)d + %(sta)d ->
  c_st (lr_lhs (ap_%(mid)s d k ph rm)) = c_st (lr_rhs (aa_%(mid)s d ra))
  /\\ c_h (lr_lhs (ap_%(mid)s d k ph rm)) = c_h (lr_rhs (aa_%(mid)s d ra)).
Proof.
  intros d k ph rm ra Hd Hk Hp Hr Ha. vm_compute in Hd, Hk.
%(body)sQed.
''' % dict(mid=mid, nph=nph, n0p=n0p, stp=stp, n0a=n0a, sta=sta,
           body=dk(lambda d, k: cases('ph', nph, lambda ph: cases(
               'rm', n0p + stp, lambda r: cases('ra', n0a + sta, lambda a: VMS))))))
    for nm2, stmt in (('apL', '''othS FAM (lr_lhs (ap_%(mid)s d k ph rm)) = sflat []
  /\\ ctrS FAM (lr_lhs (ap_%(mid)s d k ph rm))
     = blk (rep (dig FAM (fm_b FAM - 1)) rm) (dig FAM (fm_b FAM - 1)) (astride %(n0p)d %(stp)d rm) (swE FAM k ph)'''),
                      ('apR', '''othS FAM (lr_rhs (ap_%(mid)s d k ph rm)) = sflat []
  /\\ ctrS FAM (lr_rhs (ap_%(mid)s d k ph rm)) = ctrS FAM (lr_lhs (ap_%(mid)s d k ph rm))''')):
        T_.append(('''Lemma %(nm2)s_%(mid)s : forall d k ph rm, d < fm_b FAM - 1 -> k < fm_b FAM -> ph < %(nph)d -> rm < %(n0p)d + %(stp)d ->
  ''' + stmt + '''.
Proof.
  intros d k ph rm Hd Hk Hp Hr. vm_compute in Hd, Hk.
%(body)sQed.
''') % dict(nm2=nm2, mid=mid, nph=nph, n0p=n0p, stp=stp,
                  body=dk(lambda d, k: cases('ph', nph, lambda ph: cases(
                      'rm', n0p + stp, lambda r: VMS)))))
    T_.append('''Lemma acS_%(mid)s : forall d k ra, d < fm_b FAM - 1 -> k < fm_b FAM -> ra < %(n0a)d + %(sta)d ->
  ReachL tm (negb (fm_left FAM)) (fm_left FAM) (lr_lhs (ac_%(mid)s d k ra)) (lr_rhs (ac_%(mid)s d k ra)).
Proof.
  intros d k ra Hd Hk Hr. vm_compute in Hd, Hk.
%(body)sQed.
''' % dict(mid=mid, n0a=n0a, sta=sta,
           body=dk(lambda d, k: cases('ra', n0a + sta,
                                      lambda r: '  %s.\n' % reach('carc%d_%d_%d' % (d, k, r))))))
    T_.append('''Lemma acQ_%(mid)s : forall d k ra ph rm, d < fm_b FAM - 1 -> k < fm_b FAM -> ra < %(n0a)d + %(sta)d ->
  ph < %(nph)d -> rm < %(n0p)d + %(stp)d ->
  c_st (lr_lhs (ac_%(mid)s d k ra)) = c_st (lr_rhs (ap_%(mid)s d k ph rm))
  /\\ c_h (lr_lhs (ac_%(mid)s d k ra)) = c_h (lr_rhs (ap_%(mid)s d k ph rm)).
Proof.
  intros d k ra ph rm Hd Hk Hr Hp Hm. vm_compute in Hd, Hk.
%(body)sQed.

Lemma acL_%(mid)s : forall d k ra, d < fm_b FAM - 1 -> k < fm_b FAM -> ra < %(n0a)d + %(sta)d ->
  othS FAM (lr_lhs (ac_%(mid)s d k ra)) = othS FAM (lr_rhs (aa_%(mid)s d ra))
  /\\ ctrS FAM (lr_lhs (ac_%(mid)s d k ra)) = sflat [].
Proof.
  intros d k ra Hd Hk Hr. vm_compute in Hd, Hk.
%(body2)sQed.

Lemma acR_%(mid)s : forall d k ra, d < fm_b FAM - 1 -> k < fm_b FAM -> ra < %(n0a)d + %(sta)d ->
  lr_rhs (ac_%(mid)s d k ra) = cls_conf FAM (cls_side FAM [] 0 ra (astride %(n0a)d %(sta)d ra) [S d]).
Proof.
  intros d k ra Hd Hk Hr. vm_compute in Hd, Hk.
%(body3)sQed.
''' % dict(mid=mid, nph=nph, n0p=n0p, stp=stp, n0a=n0a, sta=sta,
           body=dk(lambda d, k: cases('ra', n0a + sta, lambda a: cases(
               'ph', nph, lambda ph: cases('rm', n0p + stp, lambda r: VMS)))),
           body2=dk(lambda d, k: cases('ra', n0a + sta, lambda a: VMS)),
           body3=dk(lambda d, k: cases('ra', n0a + sta, lambda a: VM))))
    fcase = lambda body: cases('r', n0f + stf, lambda r: cases('ph', nph, body), lo=1)  # noqa: E731
    T_.append('''Lemma afS_%(mid)s : forall r ph, 0 < r -> r < %(n0f)d + %(stf)d -> ph < %(nph)d ->
  ReachL tm true true (lr_lhs (af_%(mid)s r ph)) (lr_rhs (af_%(mid)s r ph)).
Proof.
  intros r ph H0 Hr Hp.
%(body)sQed.

Lemma afL_%(mid)s : forall r ph, 0 < r -> r < %(n0f)d + %(stf)d -> ph < %(nph)d ->
  lr_lhs (af_%(mid)s r ph)
    = cls_conf FAM (run_side FAM (fm_b FAM - 1) r (astride %(n0f)d %(stf)d r) 0 ph [] []).
Proof.
  intros r ph H0 Hr Hp.
%(vm)sQed.

Lemma afR_%(mid)s : forall r ph, 0 < r -> r < %(n0f)d + %(stf)d -> ph < %(nph)d ->
  lr_rhs (af_%(mid)s r ph)
    = cls_conf FAM (run_side FAM (f_mid (fam_fill FAM ph)) (fm1_%(mid)s r ph)
                    (astride %(n0f)d %(stf)d r) (fm2_%(mid)s r ph) (f_to (fam_fill FAM ph))
                    (f_pre (fam_fill FAM ph)) (f_suf (fam_fill FAM ph))).
Proof.
  intros r ph H0 Hr Hp.
%(vm)sQed.

Lemma fm12_%(mid)s : forall r ph, 0 < r -> r < %(n0f)d + %(stf)d -> ph < %(nph)d ->
  fm1_%(mid)s r ph + fm2_%(mid)s r ph
  + (length (f_pre (fam_fill FAM ph)) + length (f_suf (fam_fill FAM ph)))
  = r + f_s (fam_fill FAM ph).
Proof.
  intros r ph H0 Hr Hp.
%(lia)sQed.

Lemma vis_ok_%(mid)s : forall r t, ~ In t pins_%(mid)s -> 0 < r -> r < %(n0f)d + %(stf)d ->
  nfire tm true true nrules (vsegs_%(mid)s r t) (vis_%(mid)s r t) (lr_lhs (af_%(mid)s r 0)) = Some t.
Proof.
  intros r t Hnp H0 Hr.
%(fvis)sQed.
''' % dict(mid=mid, n0f=n0f, stf=stf, nph=nph,
           body=fcase(lambda ph: '  %s.\n' % 'X'),
           vm=fcase(lambda ph: VM), lia=fcase(lambda ph: '  vm_compute; lia.\n'),
           fvis=cases('r', n0f + stf,
                      lambda r: '  destruct t as [q s]; destruct q, s; try (exfalso; apply Hnp; simpl; tauto); vm_compute; reflexivity.\n',
                      lo=1)))
    # the fill reach body needs the arm's own name per (r, ph)
    T_[-1] = T_[-1].replace(
        fcase(lambda ph: '  X.\n'),
        cases('r', n0f + stf, lambda r: cases('ph', nph, lambda ph: '  %s.\n'
                                                 % reach('farm%d_%d' % (r, ph))), lo=1))
    boot = cd['boot']
    tmb = ('tm_%s' % mid) if E.TR_QH is not None else 'tm'
    T_.append(BOOTL % dict(mid=mid, tmb=tmb, t0=boot['steps_from_blank'],
                           ds0=clist(boot['digits_lsb_first'], str), ph0=boot.get('phase', 0)))
    L.extend(T_)
    args = '''  - vm_compute; lia.
  - reflexivity.
  - reflexivity.
  - intros ph Hp; vm_compute in Hp; destruct ph; [vm_compute; repeat constructor | lia].
  - intros ph Hp; vm_compute in Hp; destruct ph; [vm_compute; repeat constructor | lia].
  - intros ph Hp; vm_compute in Hp; destruct ph; [vm_compute; lia | lia].
  - intros ph Hp; vm_compute in Hp; destruct ph; [vm_compute; lia | lia].
  - intros ph Hp; vm_compute in Hp; destruct ph; [vm_compute; lia | lia].
  - lia.
  - intros ph Hp; exists 0; vm_compute in Hp; destruct ph; [reflexivity | lia].
  - exact fm12_%(mid)s.
  - repeat constructor.
  - vm_compute; lia.
  - lia.
  - lia.
  - exact aaS_%(mid)s.
  - exact aaL_%(mid)s.
  - exact aaC_%(mid)s.
  - lia.
  - exact apS_%(mid)s.
  - exact apQ_%(mid)s.
  - exact apL_%(mid)s.
  - exact apR_%(mid)s.
  - exact acS_%(mid)s.
  - exact acQ_%(mid)s.
  - exact acL_%(mid)s.
  - exact acR_%(mid)s.
  - lia.
  - lia.
  - exact afS_%(mid)s.
  - exact afL_%(mid)s.
  - exact afR_%(mid)s.
  - exact nrules_sound_%(mid)s.
  - exact vis_ok_%(mid)s.
  - exact bootl_%(mid)s.
''' % dict(mid=mid)
    call = ('(%(board)s tm_%(mid)s pins_%(mid)s FAM 1 aa_%(mid)s %(n0a)d %(sta)d '
            'ap_%(mid)s %(n0p)d %(stp)d ac_%(mid)s af_%(mid)s %(n0f)d %(stf)d '
            'fm1_%(mid)s fm2_%(mid)s 0 nrules vsegs_%(mid)s vis_%(mid)s %(ds0)s %(ph0)d)')
    common = dict(mid=mid, n0a=n0a, sta=sta, n0p=n0p, stp=stp, n0f=n0f, stf=stf,
                  ds0=clist(boot['digits_lsb_first'], str), ph0=boot.get('phase', 0))
    if E.TR_QH is not None:
        t0 = boot['steps_from_blank']
        L.append('''Lemma wit_%(mid)s :
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
''' % dict(mid=mid, t0=t0, call=call % dict(common, board='boardS_qhtr'), args=args))
    else:
        L.append('''Theorem nqhtr_%(mid)s : NeverQuasiHaltsTr tm_%(mid)s.
Proof.
  eapply %(call)s.
%(args)sQed.
''' % dict(mid=mid, call=call % dict(common, board='boardS_neverqhtr'), args=args))
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
    E.emit_closure = emit_closure_sweep
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
