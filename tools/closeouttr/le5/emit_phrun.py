#!/usr/bin/env python3
"""UNTRUSTED emitter: a counter with phases and a run (`phrun2.py`) -> a Coq
board closed by [LadderCheckPhRunTr] (SCOPING_INSTR 7.4.LE5).

From the reader's move table: each phase's move (carry with a widening, or
narrowing with a refill), which phases are RUNLESS (entered only with an
empty run), a linear rank [A |x| + B m + g p] that falls at every carry and
narrowing; then the arms (`emit_step.Arms`), the fires from every refill
arm, the boot.

    python3 emit_phrun.py SPEC DETECT.jsonl -o OUT.v [--qh]
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
                       coq_seg, clist, ST, SYM, _splits, Arms,
                       nvisits, prog_coq, inner_coq, ARM)
import termrun_detect as TD  # noqa: E402
import phrun2 as P2  # noqa: E402


def bits(w):
    return tuple(int(ch) for ch in w)


def table_moves(det):
    """phases (W, V) and their moves, or NoClosure"""
    tab = det['table']
    names = sorted(set(k[2:] for k in tab) | set(v[0][2] for v in tab.values()))
    idx = {w: i for i, w in enumerate(names)}
    mv = {}
    for w in names:
        tm_ = tab.get('T|' + w)
        em = tab.get('E|' + w)
        if tm_:
            k, dl, w2, dm = tm_[0]
            if dm < 0:
                raise NoClosure('phase %r: the run shrinks at its top' % w)
            if dl == -1:
                rf = [o for o in (em or []) if o[0] == 'R']
                if not rf:
                    raise NoClosure('phase %r narrows but no refill seen' % w)
                _r, a, w3, c = rf[0]
                if a < 0 or c < 0:
                    raise NoClosure('phase %r: refill law (%d, %d)' % (w, a, c))
                mv[idx[w]] = ('N', idx[w2], dm, a, idx[w3], c)
            elif dl >= 0:
                if em and ['M', dl, w2, dm] not in [list(o) for o in em]:
                    raise NoClosure('phase %r: an empty x moves otherwise' % w)
                mv[idx[w]] = ('C', idx[w2], dl, dm)
            else:
                raise NoClosure('phase %r: narrows by %d' % (w, -dl))
        elif em:
            cs = [o for o in em if o[0] == 'M' and o[1] >= 0 and o[3] >= 0]
            if not cs:
                raise NoClosure('phase %r: only an empty-x refill seen' % w)
            _k, dl, w2, dm = cs[0]
            mv[idx[w]] = ('C', idx[w2], dl, dm)
        else:
            raise NoClosure('phase %r: no move seen' % w)
    return names, idx, mv


def runless(names, mv, p0, m0):
    nr = {p: True for p in range(len(names))}
    if m0:
        nr[p0] = False
    ch = True
    while ch:
        ch = False
        for p, t in mv.items():
            outs = []
            if t[0] == 'C':
                outs.append((t[1], t[3], nr[p]))
            else:
                outs.append((t[1], t[2], nr[p]))
                outs.append((t[4], t[5], True))
            for q, dm, srcnr in outs:
                if nr[q] and (dm > 0 or not srcnr):
                    nr[q] = False
                    ch = True
    return nr


def rank(names, mv, nr):
    """(A, B, g) or NoClosure: carry A dw + B dm + g q < g p, narrow
    B dm + g q < A + g p"""
    n = len(names)
    for A in range(1, 9):
        for B in range(0, 5):
            # g p >= w + g q + 1, longest path; positive cycle = no rank
            edges = []
            for p, t in mv.items():
                if t[0] == 'C':
                    edges.append((p, t[1], A * t[2] + B * t[3] + 1))
                else:
                    edges.append((p, t[1], B * t[2] - A + 1))
            g = [0] * n
            ok = True
            for it in range(n + 1):
                chg = False
                for p, q, w in edges:
                    if g[p] < w + g[q]:
                        g[p] = w + g[q]
                        chg = True
                if not chg:
                    break
                if it == n:
                    ok = False
            if ok:
                lo = min(g)
                return A, B, [x - lo for x in g]
    raise NoClosure('no linear rank')


def visits(spec, det, steps=400000):
    """[(t, string)] at the reader's anchor"""
    q0, s0, side = det['anchor']
    tm = TD.parse(spec)
    tape, h, q = {}, 0, 0
    lo, hi = 0, -1
    out = []
    for t in range(steps):
        s = tape.get(h, 0)
        tr = tm[(q, s)]
        if tr is None:
            break
        while lo <= hi and not tape.get(lo, 0):
            lo += 1
        while hi >= lo and not tape.get(hi, 0):
            hi -= 1
        if q == q0 and s == s0:
            if side == 'R' and (hi < lo or lo >= h):
                out.append((t, ''.join(str(tape.get(i, 0)) for i in range(h + 1, max(hi, h) + 1))))
            elif side == 'L' and (hi < lo or hi <= h):
                out.append((t, ''.join(str(tape.get(i, 0)) for i in range(h - 1, min(lo, h) - 1, -1))))
        w, d, nq = tr
        tape[h] = w
        if w:
            if hi < lo:
                lo = hi = h
            else:
                lo, hi = min(lo, h), max(hi, h)
        h += d
        q = nq
    return out


def succ_state(st, idx, mv):
    x, w, m = st
    nx = P2.inc(x)
    if nx is not None:
        return (nx, w, m)
    p = idx[w]
    t = mv[p]
    names = {v: k for k, v in idx.items()}
    if t[0] == 'C':
        return ((0,) * (len(x) + t[2]), names[t[1]], m + t[3])
    if x:
        return ((0,) * (len(x) - 1), names[t[1]], m + t[2])
    return ((0,) * (m + t[3]), names[t[4]], t[5])


def find_boot(seq, det, idx, mv, lastf):
    Ds = tuple(det['D'])
    for i in range(len(seq) - 1):
        t, s = seq[i]
        if t <= lastf:
            continue
        for st in P2.parses(s, det['l'], det['pre'], det['suf'], det['T'], Ds):
            if st[1] not in idx:
                continue
            nx = succ_state(st, idx, mv)
            # the next visits, transients skipped
            for j in range(i + 1, min(i + 6, len(seq))):
                if nx in P2.parses(seq[j][1], det['l'], det['pre'], det['suf'], det['T'], Ds):
                    return t, st
    return None


def closure_data_ph(det, tab, names, idx, mv, nr, A, B, g, boot):
    T = bits(det['T'])
    pre = bits(det['pre'])
    D0, D1 = (bits(w) for w in det['D'])
    W = [bits(w.split('|')[0]) for w in names]
    V = [bits(w.split('|')[1]) for w in names]
    NP = len(names)
    q, hs, side = det['anchor']
    left = side == 'L'
    OTHER = ((), (), 0, 0, ())

    def conf(sd):
        return (q, sd, hs, OTHER) if left else (q, OTHER, hs, sd)

    derive = Arms(tab).derive
    el, er = (not left), left

    def flags(p):
        return (True, True) if nr[p] else (el, er)

    def lw(p):
        return W[p] + V[p] if nr[p] else W[p]

    def rw(p, q_, dm):
        return W[q_] + T * dm + V[q_] if nr[p] else W[q_] + T * dm

    look = [D0, D1] + W

    def inter_at(n0, st):
        got = []
        for e in range(2 + NP):
            for r in range(n0 + st):
                s_ = 0 if r < n0 else st
                c0 = conf(blk(pre + D1 * r, D1, s_, D0 + look[e]))
                c1 = conf(blk(pre + D0 * r, D0, s_, D1 + look[e]))
                try:
                    got.append((e, r, c0, c1, el, er,
                                derive(el, er, c0, c1, 'interior e=%d r=%d' % (e, r))))
                except NoClosure:
                    return None
        return got

    def carry_at(n0, st):
        got = []
        for p, t in sorted(mv.items()):
            if t[0] != 'C':
                continue
            _c, q_, dw, dm = t
            a_, b_ = flags(p)
            for r in range(n0 + st):
                s_ = 0 if r < n0 else st
                c0 = conf(blk(pre + D1 * r, D1, s_, lw(p)))
                c1 = conf(blk(pre + D0 * (r + dw), D0, s_, rw(p, q_, dm)))
                try:
                    got.append((p, r, c0, c1, a_, b_, derive(a_, b_, c0, c1, 'carry p=%d r=%d' % (p, r))))
                except NoClosure:
                    return None
        return got

    def nar_at(n0, st):
        got = []
        for p, t in sorted(mv.items()):
            if t[0] != 'N':
                continue
            q_, dm = t[1], t[2]
            a_, b_ = flags(p)
            for r in range(1, n0 + st):
                s_ = 0 if r < n0 else st
                c0 = conf(blk(pre + D1 * r, D1, s_, lw(p)))
                c1 = conf(blk(pre + D0 * (r - 1), D0, s_, rw(p, q_, dm)))
                try:
                    got.append((p, r, c0, c1, a_, b_, derive(a_, b_, c0, c1, 'narrow p=%d r=%d' % (p, r))))
                except NoClosure:
                    return None
        return got

    def refill_at(n0, st):
        got = []
        for p, t in sorted(mv.items()):
            if t[0] != 'N':
                continue
            _n, _q, _dm, a, q2, c = t
            for r in range(0, n0 + st):
                s_ = 0 if r < n0 else st
                c0 = conf(blk(pre + W[p] + T * r, T, s_, V[p]))
                hit = None
                for f1 in _splits(r + a):
                    c1 = conf(blk(pre + D0 * f1, D0, s_, D0 * (r + a - f1) + W[q2] + T * c + V[q2]))
                    try:
                        hit = (p, r, f1, r + a - f1, c0, c1,
                               derive(True, True, c0, c1, 'refill p=%d r=%d' % (p, r)))
                        break
                    except NoClosure:
                        continue
                if hit is None:
                    return None
                got.append(hit)
        return got

    def first(fn, grid):
        for n0, st in grid:
            gg = fn(n0, st)
            if gg is not None:
                return gg, n0, st
        raise NoClosure('%s: no program at any threshold and stride' % fn.__name__)

    inter, n0i, sti = first(inter_at, ARM_GRID)
    carry, n0c, stc = first(carry_at, ARM_GRID)
    grid1 = [(n0, st) for n0, st in ARM_GRID if n0 >= 1]
    narr, n0n, stn = first(nar_at, grid1)
    want = [(q_, s_) for q_ in range(4) for s_ in range(2)
            if (q_, s_) not in E.TR_PINS]
    refill = nvis = None
    for n0, st in ARM_GRID:
        gg = refill_at(n0, st)
        if gg is None:
            continue
        seen = {(p, r): nvisits(tab, want, c0, ch) for p, r, _f1, _f2, c0, _c1, ch in gg}
        if all(i in seen[k] for k in seen for i in want):
            refill, n0r, str_ = gg, n0, st
            nvis = {k: {i: seen[k][i] for i in want} for k in seen}
            break
    if refill is None:
        raise NoClosure('refill: no program, or an instruction some refill arm does not fire')
    return dict(nest=True, inter=inter, n0i=n0i, sti=sti, carry=carry, n0c=n0c, stc=stc,
                narr=narr, n0n=n0n, stn=stn, refill=refill, n0r=n0r, str=str_,
                nvis=nvis, W=W, V=V, T=T, NP=NP, boot=boot, fill=refill)


def syms(cells):
    return '[' + ';'.join('S%d' % x for x in cells) + ']'


def mvcoq(t):
    if t[0] == 'C':
        return 'PCarry %d %d %d' % t[1:]
    return 'PNarrow %d %d %d %d %d' % t[1:]


# a proof over the phases: [destruct p] NP times, the body per phase
def per_phase(NP, body):
    return ''.join('  destruct p as [|p].\n  {\n%s  }\n' % body(p) for p in range(NP)) + \
        '  exfalso; lia.\n'


def per_r(n, body, lo=0, ind='    '):
    return ''.join('%sdestruct r as [|r].\n%s{ %s. }\n'
                   % (ind, ind, 'exfalso; lia' if r < lo else body(r)) for r in range(n)) + \
        '%sexfalso; lia.\n' % ind


HEAD = '''
(** ** The closure: a counter with %(NP)d PHASES and a run ([LadderCheckPhRunTr])

    The counter side is [pre ++ x ++ W p ++ T^m ++ V p], [x] binary over the
    two digit words, [T = %(T)s]; the phases (W | V), their moves and
    whether they are runless:
%(ptab)s
    Rank [%(A)d |x| + %(B)d m + g p].  Interior arms at threshold %(n0i)d
    stride %(sti)d, carries at %(n0c)d / %(stc)d, narrowings at
    %(n0n)d / %(stn)d, refills at %(n0r)d / %(str)d.  Every arm is a
    [LadderNest] segment program. *)
From BBB4.Checkers Require Import LadderCheckPhRunTr.

Definition phW_%(mid)s (p : nat) : list Sym :=
  match p with %(Wb)s | _ => [] end.
Definition phV_%(mid)s (p : nat) : list Sym :=
  match p with %(Vb)s | _ => [] end.
Definition phT_%(mid)s : list Sym := %(Tc)s.
Definition phmv_%(mid)s (p : nat) : PMove :=
  match p with %(Mb)s | _ => PCarry 0 0 0 end.
Definition phnr_%(mid)s (p : nat) : bool :=
  match p with %(Nb)s | _ => false end.
Definition phg_%(mid)s (p : nat) : nat :=
  match p with %(Gb)s | _ => 0 end.

Ltac phok := vm_compute; repeat match goal with |- _ /\\ _ => split | |- _ -> _ => intro end;
  first [reflexivity | discriminate | lia].

'''


def emit_closure_ph(cert, tab, mid):
    det, names, idx, mv, nr, A, B, g, boot = PH
    cd = S.two_pass(lambda _c, _t: closure_data_ph(det, tab, names, idx, mv, nr, A, B, g, boot),
                    cert, tab)
    if isinstance(cd, NoClosure):
        return E.CLOSURE_NONE % cd, None
    NP = cd['NP']
    n0i, sti, n0c, stc, n0n, stn, n0r, str_ = (cd[k] for k in
                                               ('n0i', 'sti', 'n0c', 'stc', 'n0n', 'stn', 'n0r', 'str'))
    ptab = ''.join('    - %d: %s | %s, %s%s\n' % (p, names[p].split('|')[0] or '-',
                                                   names[p].split('|')[1] or '-',
                                                   mvcoq(mv[p]), ' (runless)' if nr[p] else '')
                   for p in range(NP))
    L = [HEAD % dict(mid=mid, NP=NP, T=''.join(map(str, cd['T'])), ptab=ptab, A=A, B=B,
                     n0i=n0i, sti=sti, n0c=n0c, stc=stc, n0n=n0n, stn=stn, n0r=n0r, str=str_,
                     Wb=' '.join('| %d => %s' % (p, syms(cd['W'][p])) for p in range(NP)),
                     Vb=' '.join('| %d => %s' % (p, syms(cd['V'][p])) for p in range(NP)),
                     Tc=syms(cd['T']),
                     Mb=' '.join('| %d => %s' % (p, mvcoq(mv[p])) for p in range(NP)),
                     Nb=' '.join('| %d => %s' % (p, 'true' if nr[p] else 'false') for p in range(NP)),
                     Gb=' '.join('| %d => %d' % (p, g[p]) for p in range(NP)))]
    inner, arms = [], []
    for e, r, c0, c1, a_, b_, ch in cd['inter']:
        arms.append(('iarm_%d_%d' % (e, r), c0, c1, prog_coq(tab, inner, ch), a_, b_))
    for p, r, c0, c1, a_, b_, ch in cd['carry']:
        arms.append(('carm_%d_%d' % (p, r), c0, c1, prog_coq(tab, inner, ch), a_, b_))
    for p, r, c0, c1, a_, b_, ch in cd['narr']:
        arms.append(('narm_%d_%d' % (p, r), c0, c1, prog_coq(tab, inner, ch), a_, b_))
    offs = {}
    for p, r, _f1, _f2, c0, c1, ch in cd['refill']:
        offs[(p, r)] = len(inner)
        arms.append(('rarm_%d_%d' % (p, r), c0, c1, prog_coq(tab, inner, ch), True, True))
    L.append(inner_coq(mid, inner))
    for nm, c0, c1, segs, el_, er_ in arms:
        L.append(ARM % dict(nm=nm, mid=mid, lhs=coq_conf(c0), rhs=coq_conf(c1),
                            segs=';\n   '.join(segs), el=str(el_).lower(),
                            er=str(er_).lower()))
    dflt = arms[0][0]
    L.append('''Definition iarm_%(mid)s (d e r : nat) : LRule :=
  match e, r with %(ib)s | _, _ => %(dflt)s_%(mid)s end.
Definition carm_%(mid)s (p r : nat) : LRule :=
  match p, r with %(cb)s | _, _ => %(dflt)s_%(mid)s end.
Definition narm_%(mid)s (p r : nat) : LRule :=
  match p, r with %(nb)s | _, _ => %(dflt)s_%(mid)s end.
Definition rarm_%(mid)s (p r : nat) : LRule :=
  match p, r with %(rb)s | _, _ => %(dflt)s_%(mid)s end.
Definition fm1_%(mid)s (p r : nat) : nat := match p, r with %(b1)s | _, _ => 0 end.
Definition fm2_%(mid)s (p r : nat) : nat := match p, r with %(b2)s | _, _ => 0 end.

Definition vis_%(mid)s (p r : nat) (t : Instr) : list lstep :=
  match p, r, t with
  %(vb)s
  | _, _, _ => []
  end.

Definition vsegs_%(mid)s (p r : nat) (t : Instr) : list nseg :=
  match p, r, t with
  %(sb)s
  | _, _, _ => []
  end.

''' % dict(
        mid=mid, dflt=dflt,
        ib=' '.join('| %d, %d => iarm_%d_%d_%s' % (e, r, e, r, mid) for e, r, *_ in cd['inter']),
        cb=' '.join('| %d, %d => carm_%d_%d_%s' % (p, r, p, r, mid) for p, r, *_ in cd['carry']),
        nb=' '.join('| %d, %d => narm_%d_%d_%s' % (p, r, p, r, mid) for p, r, *_ in cd['narr']),
        rb=' '.join('| %d, %d => rarm_%d_%d_%s' % (p, r, p, r, mid) for p, r, *_ in cd['refill']),
        b1=' '.join('| %d, %d => %d' % (p, r, f1) for p, r, f1, *_ in cd['refill']),
        b2=' '.join('| %d, %d => %d' % (p, r, f2) for p, r, _f1, f2, *_ in cd['refill']),
        vb='\n  '.join('| %d, %d, (%s, %s) => %s' % (k[0], k[1], ST[i[0]], SYM[i[1]], coq_chain_l(v[1]))
                       for k in sorted(cd['nvis']) for i, v in sorted(cd['nvis'][k].items())),
        sb='\n  '.join('| %d, %d, (%s, %s) => [%s]'
                       % (k[0], k[1], ST[i[0]], SYM[i[1]],
                          '; '.join(coq_seg(sg, offs[k]) for sg in v[0]))
                       for k in sorted(cd['nvis']) for i, v in sorted(cd['nvis'][k].items()))))

    def reach(nm):
        return ('eapply narm_reach; [exact nrules_sound_%s | exact ok_%s_%s]'
                % (mid, nm, mid))

    kinds = {p: mv[p][0] for p in range(NP)}

    def ph_body(kind, rbody, n, lo=0):
        def body(p):
            if kinds[p] != kind:
                return '    exfalso; vm_compute in Hmv; discriminate Hmv.\n'
            return ('    vm_compute in Hmv; injection Hmv as <- <- <-%s.\n'
                    % (' <- <-' if kind == 'N' else '')) + per_r(n, lambda r: rbody(p, r), lo)
        return per_phase(NP, body)

    def ibody():
        out = []
        for e in range(2 + NP):
            out.append('  destruct e as [|e].\n  {\n%s  }\n'
                       % per_r(n0i + sti, lambda r, e=e: '%s', ind='    '))
        return out

    def eb(fmt):
        return ''.join('  destruct e as [|e].\n  {\n%s  }\n'
                       % per_r(n0i + sti, lambda r, e=e: fmt(e, r), ind='    ')
                       for e in range(2 + NP)) + '  exfalso; lia.\n'

    t0, (bx, bw, bm) = cd['boot']
    p0 = idx[bw]
    fp = dict(mid=mid, NP=NP, A=A, B=B, n0i=n0i, sti=sti, n0c=n0c, stc=stc,
              n0n=n0n, stn=stn, n0r=n0r, str=str_)
    PHL = '''Local Notation PHF := (phW_%(mid)s) (only parsing).

Lemma mvc_%(mid)s : forall p q dw dm, p < %(NP)d -> phmv_%(mid)s p = PCarry q dw dm ->
  q < %(NP)d /\\ (phnr_%(mid)s q = true -> phnr_%(mid)s p = true /\\ dm = 0)
  /\\ %(A)d * dw + %(B)d * dm + phg_%(mid)s q < phg_%(mid)s p.
Proof.
  intros p q dw dm Hp Hmv.
%(pc)sQed.

Lemma mvn_%(mid)s : forall p q dm a q' c, p < %(NP)d -> phmv_%(mid)s p = PNarrow q dm a q' c ->
  q < %(NP)d /\\ q' < %(NP)d /\\ (phnr_%(mid)s q = true -> phnr_%(mid)s p = true /\\ dm = 0)
  /\\ (phnr_%(mid)s q' = true -> c = 0) /\\ %(B)d * dm + phg_%(mid)s q < %(A)d + phg_%(mid)s p.
Proof.
  intros p q dm a q' c Hp Hmv.
%(pn)sQed.

Lemma hvc_%(mid)s : forall p q dw dm, p < %(NP)d -> phmv_%(mid)s p = PCarry q dw dm ->
  phnr_%(mid)s p = false -> phV_%(mid)s q = phV_%(mid)s p.
Proof.
  intros p q dw dm Hp Hmv.
%(pc2)sQed.

Lemma hvn_%(mid)s : forall p q dm a q' c, p < %(NP)d -> phmv_%(mid)s p = PNarrow q dm a q' c ->
  phnr_%(mid)s p = false -> phV_%(mid)s q = phV_%(mid)s p.
Proof.
  intros p q dm a q' c Hp Hmv.
%(pn2)sQed.

Lemma iarm_reach_%(mid)s : forall d e r, d < fm_b FAM - 1 -> e < fm_b FAM + %(NP)d -> r < %(n0i)d + %(sti)d ->
  ReachL tm (negb (fm_left FAM)) (fm_left FAM) (lr_lhs (iarm_%(mid)s d e r)) (lr_rhs (iarm_%(mid)s d e r)).
Proof.
  intros d e r Hd He Hr. vm_compute in Hd, He. destruct d as [|d]; [|exfalso; lia].
%(isound)sQed.

Lemma iarm_lhs_%(mid)s : forall d e r, d < fm_b FAM - 1 -> e < fm_b FAM + %(NP)d -> r < %(n0i)d + %(sti)d ->
  lr_lhs (iarm_%(mid)s d e r)
    = cls_conf FAM (blk (fm_pre FAM ++ rep (dig FAM (fm_b FAM - 1)) r) (dig FAM (fm_b FAM - 1))
                     (astride %(n0i)d %(sti)d r) (dig FAM d ++ ilookP FAM phW_%(mid)s e)).
Proof.
  intros d e r Hd He Hr. vm_compute in Hd, He. destruct d as [|d]; [|exfalso; lia].
%(icomp)sQed.

Lemma iarm_rhs_%(mid)s : forall d e r, d < fm_b FAM - 1 -> e < fm_b FAM + %(NP)d -> r < %(n0i)d + %(sti)d ->
  lr_rhs (iarm_%(mid)s d e r)
    = cls_conf FAM (blk (fm_pre FAM ++ rep (dig FAM 0) r) (dig FAM 0)
                     (astride %(n0i)d %(sti)d r) (dig FAM (S d) ++ ilookP FAM phW_%(mid)s e)).
Proof.
  intros d e r Hd He Hr. vm_compute in Hd, He. destruct d as [|d]; [|exfalso; lia].
%(icomp)sQed.

Lemma carm_reach_%(mid)s : forall p q dw dm r, p < %(NP)d -> phmv_%(mid)s p = PCarry q dw dm ->
  r < %(n0c)d + %(stc)d ->
  ReachL tm (if phnr_%(mid)s p then true else negb (fm_left FAM))
            (if phnr_%(mid)s p then true else fm_left FAM)
    (lr_lhs (carm_%(mid)s p r)) (lr_rhs (carm_%(mid)s p r)).
Proof.
  intros p q dw dm r Hp Hmv Hr.
%(csound)sQed.

Lemma carm_lhs_%(mid)s : forall p q dw dm r, p < %(NP)d -> phmv_%(mid)s p = PCarry q dw dm ->
  r < %(n0c)d + %(stc)d ->
  lr_lhs (carm_%(mid)s p r) = cls_conf FAM (blk (fm_pre FAM ++ rep (dig FAM (fm_b FAM - 1)) r)
                                  (dig FAM (fm_b FAM - 1)) (astride %(n0c)d %(stc)d r)
                                  (lwP phW_%(mid)s phV_%(mid)s phnr_%(mid)s p)).
Proof.
  intros p q dw dm r Hp Hmv Hr.
%(ccomp)sQed.

Lemma carm_rhs_%(mid)s : forall p q dw dm r, p < %(NP)d -> phmv_%(mid)s p = PCarry q dw dm ->
  r < %(n0c)d + %(stc)d ->
  lr_rhs (carm_%(mid)s p r) = cls_conf FAM (blk (fm_pre FAM ++ rep (dig FAM 0) (r + dw))
                                  (dig FAM 0) (astride %(n0c)d %(stc)d r)
                                  (rwP phW_%(mid)s phV_%(mid)s phT_%(mid)s phnr_%(mid)s p q dm)).
Proof.
  intros p q dw dm r Hp Hmv Hr.
%(ccomp)sQed.

Lemma narm_reach_%(mid)s : forall p q dm a q' c r, p < %(NP)d -> phmv_%(mid)s p = PNarrow q dm a q' c ->
  0 < r -> r < %(n0n)d + %(stn)d ->
  ReachL tm (if phnr_%(mid)s p then true else negb (fm_left FAM))
            (if phnr_%(mid)s p then true else fm_left FAM)
    (lr_lhs (narm_%(mid)s p r)) (lr_rhs (narm_%(mid)s p r)).
Proof.
  intros p q dm a q' c r Hp Hmv H0 Hr.
%(nsound)sQed.

Lemma narm_lhs_%(mid)s : forall p q dm a q' c r, p < %(NP)d -> phmv_%(mid)s p = PNarrow q dm a q' c ->
  0 < r -> r < %(n0n)d + %(stn)d ->
  lr_lhs (narm_%(mid)s p r) = cls_conf FAM (blk (fm_pre FAM ++ rep (dig FAM (fm_b FAM - 1)) r)
                                  (dig FAM (fm_b FAM - 1)) (astride %(n0n)d %(stn)d r)
                                  (lwP phW_%(mid)s phV_%(mid)s phnr_%(mid)s p)).
Proof.
  intros p q dm a q' c r Hp Hmv H0 Hr.
%(ncomp)sQed.

Lemma narm_rhs_%(mid)s : forall p q dm a q' c r, p < %(NP)d -> phmv_%(mid)s p = PNarrow q dm a q' c ->
  0 < r -> r < %(n0n)d + %(stn)d ->
  lr_rhs (narm_%(mid)s p r) = cls_conf FAM (blk (fm_pre FAM ++ rep (dig FAM 0) (r - 1))
                                  (dig FAM 0) (astride %(n0n)d %(stn)d r)
                                  (rwP phW_%(mid)s phV_%(mid)s phT_%(mid)s phnr_%(mid)s p q dm)).
Proof.
  intros p q dm a q' c r Hp Hmv H0 Hr.
%(ncomp)sQed.

Lemma rarm_reach_%(mid)s : forall p q dm a q' c r, p < %(NP)d -> phmv_%(mid)s p = PNarrow q dm a q' c ->
  r < %(n0r)d + %(str)d ->
  ReachL tm true true (lr_lhs (rarm_%(mid)s p r)) (lr_rhs (rarm_%(mid)s p r)).
Proof.
  intros p q dm a q' c r Hp Hmv Hr.
%(rsound)sQed.

Lemma rarm_lhs_%(mid)s : forall p q dm a q' c r, p < %(NP)d -> phmv_%(mid)s p = PNarrow q dm a q' c ->
  r < %(n0r)d + %(str)d ->
  lr_lhs (rarm_%(mid)s p r) = cls_conf FAM (blk (fm_pre FAM ++ phW_%(mid)s p ++ rep phT_%(mid)s r)
                                  phT_%(mid)s (astride %(n0r)d %(str)d r) (phV_%(mid)s p)).
Proof.
  intros p q dm a q' c r Hp Hmv Hr.
%(rcomp)sQed.

Lemma rarm_rhs_%(mid)s : forall p q dm a q' c r, p < %(NP)d -> phmv_%(mid)s p = PNarrow q dm a q' c ->
  r < %(n0r)d + %(str)d ->
  lr_rhs (rarm_%(mid)s p r) = cls_conf FAM (blk (fm_pre FAM ++ rep (dig FAM 0) (fm1_%(mid)s p r)) (dig FAM 0)
                                  (astride %(n0r)d %(str)d r)
                                  (rep (dig FAM 0) (fm2_%(mid)s p r) ++ phW_%(mid)s q'
                                     ++ rep phT_%(mid)s c ++ phV_%(mid)s q')).
Proof.
  intros p q dm a q' c r Hp Hmv Hr.
%(rcomp)sQed.

Lemma fm_%(mid)s : forall p q dm a q' c r, p < %(NP)d -> phmv_%(mid)s p = PNarrow q dm a q' c ->
  r < %(n0r)d + %(str)d -> fm1_%(mid)s p r + fm2_%(mid)s p r = r + a.
Proof.
  intros p q dm a q' c r Hp Hmv Hr.
%(rlia)sQed.

Lemma vis_ok_%(mid)s : forall p q dm a q' c r t, p < %(NP)d -> phmv_%(mid)s p = PNarrow q dm a q' c ->
  ~ In t pins_%(mid)s -> r < %(n0r)d + %(str)d ->
  nfire tm true true nrules (vsegs_%(mid)s p r t) (vis_%(mid)s p r t)
    (lr_lhs (rarm_%(mid)s p r)) = Some t.
Proof.
  intros p q dm a q' c r t Hp Hmv Hnp Hr.
%(fvis)sQed.

Lemma bootl_%(mid)s :
  stepn %(tmb)s %(t0)d InitES
  = Some (lift (pcfg FAM phW_%(mid)s phV_%(mid)s phT_%(mid)s (%(x0)s, %(p0)d, %(m0)d))).
Proof.
  assert (H : match csteps %(tmb)s %(t0)d c0 with
              | Some c => ceqb c (pcfg FAM phW_%(mid)s phV_%(mid)s phT_%(mid)s (%(x0)s, %(p0)d, %(m0)d))
              | None => false end = true) by (vm_compute; reflexivity).
  destruct (csteps %(tmb)s %(t0)d c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

'''
    ok = '    phok.\n'

    def tabproof(kind):
        def body(p):
            if kinds[p] != kind:
                return '    exfalso; vm_compute in Hmv; discriminate Hmv.\n'
            return ('    vm_compute in Hmv; injection Hmv as <- <- <-%s.\n'
                    % (' <- <-' if kind == 'N' else '')) + ok
        return per_phase(NP, body)

    def tabv(kind):
        def body(p):
            if kinds[p] != kind:
                return '    exfalso; vm_compute in Hmv; discriminate Hmv.\n'
            return ('    vm_compute in Hmv; injection Hmv as <- <- <-%s.\n'
                    % (' <- <-' if kind == 'N' else '')) + \
                '    vm_compute; first [reflexivity | discriminate].\n'
        return per_phase(NP, body)

    cmp = 'vm_compute; reflexivity'
    L.append(PHL % dict(
        fp,
        pc=tabproof('C'), pn=tabproof('N'), pc2=tabv('C'), pn2=tabv('N'),
        isound=eb(lambda e, r: reach('iarm_%d_%d' % (e, r))),
        icomp=eb(lambda e, r: cmp),
        csound=ph_body('C', lambda p, r: reach('carm_%d_%d' % (p, r)), n0c + stc),
        ccomp=ph_body('C', lambda p, r: cmp, n0c + stc),
        nsound=ph_body('N', lambda p, r: reach('narm_%d_%d' % (p, r)), n0n + stn, 1),
        ncomp=ph_body('N', lambda p, r: cmp, n0n + stn, 1),
        rsound=ph_body('N', lambda p, r: reach('rarm_%d_%d' % (p, r)), n0r + str_),
        rcomp=ph_body('N', lambda p, r: cmp, n0r + str_),
        rlia=ph_body('N', lambda p, r: 'vm_compute; lia', n0r + str_),
        fvis=ph_body('N', lambda p, r: 'destruct t as [q s]; destruct q, s; '
                     'try (exfalso; apply Hnp; simpl; tauto); vm_compute; reflexivity',
                     n0r + str_),
        t0=t0, x0=clist(bx, str), p0=p0, m0=bm,
        tmb=('tm_%s' % mid) if E.TR_QH is not None else 'tm'))
    args = '''  - vm_compute; lia.
  - exact mvc_%(mid)s.
  - exact mvn_%(mid)s.
  - exact hvc_%(mid)s.
  - exact hvn_%(mid)s.
  - repeat constructor.
  - lia.
  - reflexivity.
  - lia.
  - exact iarm_reach_%(mid)s.
  - exact iarm_lhs_%(mid)s.
  - exact iarm_rhs_%(mid)s.
  - lia.
  - exact carm_reach_%(mid)s.
  - exact carm_lhs_%(mid)s.
  - exact carm_rhs_%(mid)s.
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
''' % dict(mid=mid)
    call = '''(%(board)s tm_%(mid)s pins_%(mid)s FAM %(NP)d phW_%(mid)s phV_%(mid)s phT_%(mid)s
                 phmv_%(mid)s phnr_%(mid)s %(A)d %(B)d phg_%(mid)s
                 iarm_%(mid)s %(n0i)d %(sti)d carm_%(mid)s %(n0c)d %(stc)d
                 narm_%(mid)s %(n0n)d %(stn)d rarm_%(mid)s %(n0r)d %(str)d
                 fm1_%(mid)s fm2_%(mid)s nrules vsegs_%(mid)s vis_%(mid)s %(x0)s %(p0)d %(m0)d)'''
    common = dict(fp, x0=clist(bx, str), p0=p0, m0=bm)
    if E.TR_QH is not None:
        L.append('''Lemma wit_%(mid)s :
  existsb (fun tg => cfires tm_%(mid)s c0 %(t0)d tg) pins_%(mid)s = true.
Proof. vm_compute. reflexivity. Qed.

Lemma bnd_%(mid)s : (%(t0)d <=? 32779478) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

(** The machine-level theorem, on the QUASIHALTING side, through
    [LadderCheckPhRunTr.boardP_qhtr]. *)
Theorem qhtr_%(mid)s :
  NonHalt tm_%(mid)s /\\ QHBoundTr 32779478 tm_%(mid)s /\\ QuasiHaltsTr tm_%(mid)s.
Proof.
  eapply %(call)s.
%(args)s  - exact wit_%(mid)s.
  - exact bnd_%(mid)s.
Qed.
''' % dict(mid=mid, t0=t0, call=call % dict(common, board='boardP_qhtr'), args=args))
    else:
        L.append('''(** The machine-level theorem, at the INSTRUCTION level, through
    [LadderCheckPhRunTr.boardP_neverqhtr]. *)
Theorem nqhtr_%(mid)s : NeverQuasiHaltsTr tm_%(mid)s.
Proof.
  eapply %(call)s.
%(args)sQed.
''' % dict(mid=mid, call=call % dict(common, board='boardP_neverqhtr'), args=args))
    return ''.join(L), cd


PH = None


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
        raise SystemExit('%s: no phase-run reading' % args.spec)
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
    names, idx, mv = table_moves(det)
    seq = visits(spec, det)
    bt = find_boot(seq, det, idx, mv, lastf)
    if bt is None:
        raise SystemExit('%s: no boot past %d' % (spec, lastf))
    t0, st0 = bt
    nr = runless(names, mv, idx[st0[1]], st0[2])
    for p, t in mv.items():
        if not nr[p] and V_of(names, t[1]) != V_of(names, p):
            raise NoClosure('phase %r has a run but its move rewrites V' % names[p])
    A, B, g = rank(names, mv, nr)
    if args.qh:
        E.TR_QH = t0
    tab = E.parse_tm(spec)
    global PH
    PH = (det, names, idx, mv, nr, A, B, g, (t0, st0))
    q, hs, side = det['anchor']
    d0, d1 = det['D']
    cert = dict(spec=spec, ladder=[], arms=[],
                family=dict(base=2, digits=[[int(ch) for ch in d0], [int(ch) for ch in d1]],
                            near_head_prefix=[int(ch) for ch in det['pre']],
                            terminator=[], terminators_by_phase=[[]], code='binary',
                            value_step_per_anchor_visit=1, state='ABCD'[q], head=hs,
                            side=side, other_side_cells=[]),
                fill=dict(widens_by=1, target_prefix=[], target_fill_digit=0,
                          target_suffix=[1], lands_in_phase=0))
    E.emit_closure = emit_closure_ph
    good, bad, cd = E.emit(cert, args.out)
    print('%s: closure %s' % (args.out, 'BUILT' if cd else 'not built'))
    return 0 if cd else 1


def V_of(names, p):
    return names[p].split('|')[1]


if __name__ == '__main__':
    sys.exit(main())
