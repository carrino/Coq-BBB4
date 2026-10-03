#!/usr/bin/env python3
"""LE9 (UNTRUSTED): arm families on TWO-SIDED forms, both tails opaque
(SCOPING_INSTR 7.4.LE9), for [Counters.TwoSideArmTr].

A form is (q, h, L, R): L and R are item lists nearest-first, items
('c', cells), ('r', word, base) for word^(base + n), ('X',) for the opaque
tail (last item only).  At most one side carries a block; an arm's two
forms carry it on the same side, or on opposite sides when the pass carries
it across the head ([armfam2_lr] / [armfam2_rl]).  Coq statements are in the exact shape of
[armfam2_r] / [armfam2_l] / [arm2_flat]:

    (q, (L1 ++ XL, h, P1 ++ rep w (b + n) ++ W1 ++ XR))

so a use site normalises its goal to that shape.
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'le3'))
sys.path.insert(0, os.path.join(HERE, '..', 'le8'))
import emit_step as S  # noqa: E402
from emit_step import (NoClosure, blk, ARM_GRID, coq_conf, prog_coq, ST, SYM,  # noqa: E402
                       coq_chain_l, coq_seg)
from emit_nest import nvisits_f  # noqa: E402
from csim import step as cstep, norm  # noqa: E402

ARM2 = '''Definition %(nm)s : LRule :=
  mkLRule (%(lhs)s)
          (%(rhs)s) 0 1.
Definition ch_%(nm)s : list nseg :=
  [%(segs)s].
Lemma ok_%(nm)s :
  check_narm tm %(el)s %(er)s nrules %(nm)s ch_%(nm)s = true.
Proof. vm_compute. reflexivity. Qed.

'''


def syms(cells):
    return '[' + ';'.join('S%d' % c for c in cells) + ']'


def has_x(items):
    return bool(items) and items[-1][0] == 'X'


def rep_of(items):
    rs = [i for i, it in enumerate(items) if it[0] == 'r']
    return rs[0] if rs else None


def flat(items):
    return tuple(c for it in items if it[0] == 'c' for c in it[1])


def parts(items):
    """(P cells, word, base, W cells) of a side with one block"""
    i = rep_of(items)
    P = tuple(c for it in items[:i] for c in it[1])
    W = tuple(c for it in items[i + 1:] if it[0] == 'c' for c in it[1])
    return P, tuple(items[i][1]), items[i][2], W


def inst(items, n, X):
    out = []
    for it in items:
        if it[0] == 'c':
            out += list(it[1])
        elif it[0] == 'r':
            out += list(it[1]) * (it[2] + n)
        else:
            out += list(X)
    return tuple(out)


class Gen2:
    def __init__(self, tab, mid, pins, ctab):
        self.tab = tab          # emit_ladder table, pins applied
        self.ctab = ctab        # csim table, pins applied (validation)
        self.mid = mid
        self.arms = S.Arms(tab)
        self.inner = []
        self.out = []
        self.n = 0
        self.want = [(q, s) for q in range(4) for s in range(2) if (q, s) not in pins]
        self.fams = {}          # lemma name -> data for fire witnesses

    def fresh(self, b):
        self.n += 1
        return '%s%d_%s' % (b, self.n, self.mid)

    def validate(self, f0, f1, what):
        tails = [((0,) * 6, (0,) * 6), ((0, 1, 0, 0, 1, 1), (0, 0, 1, 1, 0, 1))]
        for n in range(0, 5):
            for XL, XR in (tails if (has_x(f0[2]) or has_x(f0[3])) else tails[:1]):
                c = (f0[0], inst(f0[2], n, XL), f0[1], inst(f0[3], n, XR))
                t = norm((f1[0], inst(f1[2], n, XL), f1[1], inst(f1[3], n, XR)))
                for _ in range(200000):
                    c = cstep(self.ctab, c)
                    if c is None:
                        raise NoClosure('%s: halts at n=%d' % (what, n))
                    if c[0] == t[0] and c[2] == t[2] and norm(c) == t:
                        break
                else:
                    raise NoClosure('%s: target not reached at n=%d' % (what, n))

    def side_s(self, items, r, s_):
        if rep_of(items) is None:
            return (flat(items), (), 0, 0, ())
        P, w, b, W = parts(items)
        return blk(P + w * (b + r), w, s_, W)

    def conf(self, f, r, s_):
        return (f[0], self.side_s(f[2], r, s_), f[1], self.side_s(f[3], r, s_))

    def coq_side(self, items, var):
        """the Coq cells of a side in armfam2 shape"""
        X = 'XL' if var == 'L' else 'XR'
        tail = X if has_x(items) else '[]'
        if rep_of(items) is None:
            return '%s ++ %s' % (syms(flat(items)), tail)
        P, w, b, W = parts(items)
        cnt = 'n' if b == 0 else '%d + n' % b
        return '%s ++ rep %s (%s) ++ %s ++ %s' % (syms(P), syms(w), cnt, syms(W), tail)

    def coq_form(self, f):
        return '(%s, (%s, %s, %s))' % (ST[f[0]], self.coq_side(f[2], 'L'), SYM[f[1]],
                                       self.coq_side(f[3], 'R'))

    def arm(self, f0, f1, what):
        """a lemma [forall n XL XR, Reach1 tm f0 f1] (flags permitting)"""
        self.validate(f0, f1, what)
        el, er = not has_x(f0[2]), not has_x(f0[3])
        side = 'R' if rep_of(f0[3]) is not None else ('L' if rep_of(f0[2]) is not None else None)
        side1 = 'R' if rep_of(f1[3]) is not None else ('L' if rep_of(f1[2]) is not None else None)
        if side1 != side and None in (side, side1):
            raise NoClosure('%s: only one of the two forms carries a block' % what)
        flagL = '(fun H => False_ind _ (diff_false_true H))' if not el else '(fun _ => eq_refl)'
        flagR = '(fun H => False_ind _ (diff_false_true H))' if not er else '(fun _ => eq_refl)'
        xl = 'XL' if not el else '[]'
        xr = 'XR' if not er else '[]'
        if side is None:
            c0, c1 = self.conf(f0, 0, 0), self.conf(f1, 0, 0)
            ch = self.arms.derive(el, er, c0, c1, what)
            nm = self.fresh('tf')
            self.out.append(ARM2 % dict(nm=nm, lhs=coq_conf(c0), rhs=coq_conf(c1),
                                        segs=';\n   '.join(prog_coq(self.tab, self.inner, ch)),
                                        el=str(el).lower(), er=str(er).lower()))
            lem = self.fresh('tp')
            self.out.append('''Lemma %(lem)s : forall (n : nat) (XL XR : list Sym),
  Reach1 tm %(f0)s %(f1)s.
Proof.
  intros n XL XR.
  exact (arm2_flat tm %(el)s %(er)s %(nm)s _ _ _ _ _ _ _ _
           ltac:(eapply narm_reach; [exact nrules_sound_%(mid)s | exact ok_%(nm)s])
           eq_refl eq_refl %(xl)s %(xr)s %(fl)s %(fr)s).
Qed.

''' % dict(lem=lem, f0=self.coq_form(f0), f1=self.coq_form(f1), el=str(el).lower(),
           er=str(er).lower(), nm=nm, mid=self.mid, xl=xl, xr=xr, fl=flagL, fr=flagR))
            self.fams[lem] = dict(kind='flat', f0=f0, c0=c0, ch=ch, el=el, er=er, nm=nm)
            return lem
        got = None
        for n0, st in ARM_GRID:
            arms = []
            ok = True
            for r in range(n0 + st):
                s_ = 0 if r < n0 else st
                c0, c1 = self.conf(f0, r, s_), self.conf(f1, r, s_)
                try:
                    arms.append((r, c0, c1, self.arms.derive(el, er, c0, c1, '%s r=%d' % (what, r))))
                except NoClosure:
                    ok = False
                    break
            if ok:
                got = (arms, n0, st)
                break
        if got is None:
            raise NoClosure('%s: no arm family at any threshold and stride' % what)
        arms, n0, st = got
        base = self.fresh('tfa')
        for r, c0, c1, ch in arms:
            self.out.append(ARM2 % dict(nm='%s_%d' % (base, r), lhs=coq_conf(c0), rhs=coq_conf(c1),
                                        segs=';\n   '.join(prog_coq(self.tab, self.inner, ch)),
                                        el=str(el).lower(), er=str(er).lower()))
        self.out.append('Definition %s (r : nat) : LRule :=\n  match r with %s | _ => %s_%d end.\n\n'
                        % (base, ' '.join('| %d => %s_%d' % (r, base, r) for r, *_ in arms),
                           base, arms[0][0]))
        br = lambda body: ''.join('  destruct r as [|r].\n  { %s. }\n' % body(r)  # noqa: E731
                                  for r in range(n0 + st))

        def sdesc(f, sd):
            items = f[2] if sd == 'L' else f[3]
            if rep_of(items) is None:
                return 'sflat %s' % syms(flat(items))
            P, w, b, W = parts(items)
            return '(blk (%s ++ rep %s r) %s (astride %d %d r) %s)' % (syms(P + w * b), syms(w), syms(w),
                                                                        n0, st, syms(W))

        def cdesc(f):
            return 'mkC %s (%s) %s (%s)' % (ST[f[0]], sdesc(f, 'L'), SYM[f[1]], sdesc(f, 'R'))
        self.out.append('''Lemma %(b)s_reach : forall r, r < %(n0)d + %(st)d ->
  ReachL tm %(el)s %(er)s (lr_lhs (%(b)s r)) (lr_rhs (%(b)s r)).
Proof. intros r Hr.
%(snd)s  exfalso; lia.
Qed.

Lemma %(b)s_lhs : forall r, r < %(n0)d + %(st)d -> lr_lhs (%(b)s r) = %(lhs)s.
Proof. intros r Hr.
%(cmp)s  exfalso; lia.
Qed.

Lemma %(b)s_rhs : forall r, r < %(n0)d + %(st)d -> lr_rhs (%(b)s r) = %(rhs)s.
Proof. intros r Hr.
%(cmp)s  exfalso; lia.
Qed.

''' % dict(b=base, n0=n0, st=st, el=str(el).lower(), er=str(er).lower(),
           lhs=cdesc(f0), rhs=cdesc(f1),
           snd=br(lambda r: 'eapply narm_reach; [exact nrules_sound_%s | exact ok_%s_%d]'
                  % (self.mid, base, r)),
           cmp=br(lambda r: 'vm_compute; reflexivity')))
        # the block's base folds into P: armfam2 counts the block from P ++ rep w b
        lem = self.fresh('tpa')
        lemma = {('R', 'R'): 'armfam2_r', ('L', 'L'): 'armfam2_l',
                 ('L', 'R'): 'armfam2_lr', ('R', 'L'): 'armfam2_rl'}[(side, side1)]
        self.out.append('''Lemma %(lem)s : forall (n : nat) (XL XR : list Sym), Reach1 tm %(f0)s %(f1)s.
Proof.
  intros n XL XR.
  pose proof (%(lemma)s tm %(el)s %(er)s %(n0)d %(st)d %(b)s _ _ _ _ _ _ _ _ _ _ _ _
           ltac:(lia) %(b)s_reach %(b)s_lhs %(b)s_rhs n %(xl)s %(xr)s %(fl)s %(fr)s) as H.
  rewrite <- ?app_assoc, <- ?rep_add in H. rewrite ?(Nat.add_comm n). exact H.
Qed.

''' % dict(lem=lem, f0=self.coq_form(f0), f1=self.coq_form(f1), lemma=lemma,
           el=str(el).lower(), er=str(er).lower(), n0=n0, st=st, b=base, xl=xl, xr=xr,
           fl=flagL, fr=flagR))
        self.fams[lem] = dict(kind='fam', f0=f0, base=base, n0=n0, st=st, el=el, er=er,
                              arms=arms, side=side)
        return lem

    def fires(self, lem, mine=None):
        """fire lemmas [forall n XL XR, Fires tm f0 t] for the instructions every
        arm of [lem]'s family fires; returns {instr: lemma name}"""
        fd = self.fams[lem]
        el, er = fd['el'], fd['er']
        flagL = '(fun H => False_ind _ (diff_false_true H))' if not el else '(fun _ => eq_refl)'
        flagR = '(fun H => False_ind _ (diff_false_true H))' if not er else '(fun _ => eq_refl)'
        xl = 'XL' if not el else '[]'
        xr = 'XR' if not er else '[]'
        if fd['kind'] == 'flat':
            vis = {0: nvisits_f(self.tab, self.want, el, er, fd['c0'], fd['ch'])}
        else:
            vis = {r: nvisits_f(self.tab, self.want, el, er, c0, ch) for r, c0, c1, ch in fd['arms']}
        got = [w for w in self.want if all(w in vis[r] for r in vis) and (mine is None or w in mine)]
        out = {}
        if not got:
            return out
        b = fd.get('base', fd.get('nm'))
        self.out.append('''Definition %(b)s_vis (r : nat) (t : Instr) : list lstep :=
  match r, t with
  %(vb)s
  | _, _ => []
  end.

Definition %(b)s_vsegs (r : nat) (t : Instr) : list nseg :=
  match r, t with
  %(sb)s
  | _, _ => []
  end.

''' % dict(b=b, vb='\n  '.join('| %d, (%s, %s) => %s' % (r, ST[w[0]], SYM[w[1]], coq_chain_l(vis[r][w][1]))
                                for r in sorted(vis) for w in got),
           sb='\n  '.join('| %d, (%s, %s) => [%s]' % (r, ST[w[0]], SYM[w[1]],
                                                     '; '.join(coq_seg(sg, 0) for sg in vis[r][w][0]))
                          for r in sorted(vis) for w in got)))
        for w in got:
            nm = 'fire_%s%d_%s_%s' % ('ABCD'[w[0]], w[1], lem, self.mid)
            q_, s_ = ST[w[0]], SYM[w[1]]
            if fd['kind'] == 'flat':
                self.out.append('''Lemma %(nm)s : forall (n : nat) (XL XR : list Sym), Fires tm %(f0)s (%(q)s, %(s)s).
Proof.
  intros n XL XR.
  exact (fire2_flat tm %(el)s %(er)s nrules (%(b)s_vsegs 0 (%(q)s, %(s)s)) (%(b)s_vis 0 (%(q)s, %(s)s))
           (lr_lhs %(b)s) _ _ _ _ _ nrules_sound_%(mid)s ltac:(vm_compute; reflexivity) eq_refl
           %(xl)s %(xr)s %(fl)s %(fr)s).
Qed.

''' % dict(nm=nm, f0=self.coq_form(fd['f0']), q=q_, s=s_, el=str(el).lower(), er=str(er).lower(),
           b=b, mid=self.mid, xl=xl, xr=xr, fl=flagL, fr=flagR))
            else:
                n0, st = fd['n0'], fd['st']
                br = ''.join('  destruct r as [|r].\n  { vm_compute; reflexivity. }\n' for _ in range(n0 + st))
                lemma = 'fire2_r' if fd['side'] == 'R' else 'fire2_l'
                self.out.append('''Lemma %(nm)s_vis : forall r, r < %(n0)d + %(st)d ->
  nfire tm %(el)s %(er)s nrules (%(b)s_vsegs r (%(q)s, %(s)s)) (%(b)s_vis r (%(q)s, %(s)s))
    (lr_lhs (%(b)s r)) = Some (%(q)s, %(s)s).
Proof. intros r Hr.
%(br)s  exfalso; lia.
Qed.

Lemma %(nm)s : forall (n : nat) (XL XR : list Sym), Fires tm %(f0)s (%(q)s, %(s)s).
Proof.
  intros n XL XR.
  pose proof (%(lemma)s tm %(el)s %(er)s nrules %(n0)d %(st)d (fun r => %(b)s_vsegs r (%(q)s, %(s)s))
           (fun r => %(b)s_vis r (%(q)s, %(s)s)) (fun r => lr_lhs (%(b)s r)) _ _ _ _ _ _ _
           ltac:(lia) nrules_sound_%(mid)s %(nm)s_vis %(b)s_lhs n %(xl)s %(xr)s %(fl)s %(fr)s) as H.
  rewrite <- ?app_assoc, <- ?rep_add in H. rewrite ?(Nat.add_comm n). exact H.
Qed.

''' % dict(nm=nm, n0=n0, st=st, el=str(el).lower(), er=str(er).lower(), b=b, q=q_, s=s_, br=br,
           mid=self.mid, f0=self.coq_form(fd['f0']), lemma=lemma, xl=xl, xr=xr, fl=flagL, fr=flagR))
            out[w] = nm
        return out
