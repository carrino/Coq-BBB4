#!/usr/bin/env python3
"""UNTRUSTED emitter (SCOPING_INSTR 7.4.LE8): a binary counter whose carry
runs whole INNER COUNTS -> a Coq board closed by [NestCountTr.BoardBinTr].

A PLAN (json, one per row, read by hand off the traces; `le8/plans/`) names

* the outer counter: anchor state, side ('R': the counter to the right of
  the head, the head on its first cell), the far side's cells, the digit
  words Z (0) and O (1), LSB at the head, the terminator T;
* the inner levels: anchor, side, far side, digit words; a level's carry
  ([cfg (O^j Z Y) -> cfg (Z^j O Y)]) is one arm family unless the plan
  gives pieces;
* the outer carry [cfg (O^k Z X) -> cfg (Z^k O X)]: the small k one by one
  and, for k = K0 + n, a list of PIECES between symbolic forms -- an arm
  (a [LadderNest] segment program per arm index, threshold and stride as
  in the LE3-LE6 emitters) or an inner count at width [b + n].

A form is a configuration with one symbolic count n: items ('c', cells),
('r', word, b) for word^(b + n), and ('X',) for the opaque tail.  Every
piece is validated by running the machine (n = 0..5, three random tails)
before anything is derived; the kernel re-checks everything anyway.

    python3 emit_nest.py PLAN.json -o OUT.v
"""
import argparse
import itertools
import json
import os
import random
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'le3'))
sys.path.insert(0, HERE)
import emit_step as S  # noqa: E402
from emit_step import (E, NoClosure, blk, ARM_GRID, coq_conf, coq_seg,  # noqa: E402
                       coq_chain_l, clist, ST, SYM, Arms, prog_coq, inner_coq, ARM)
from csim import step as cstep, norm  # noqa: E402

LC = E.LC
nest = E.nest

ARM2 = '''Definition %(nm)s : LRule :=
  mkLRule (%(lhs)s)
          (%(rhs)s) 0 1.
Definition ch_%(nm)s : list nseg :=
  [%(segs)s].
Lemma ok_%(nm)s :
  check_narm tm %(el)s %(er)s nrules %(nm)s ch_%(nm)s = true.
Proof. vm_compute. reflexivity. Qed.

'''
ST_OF = {'A': 0, 'B': 1, 'C': 2, 'D': 3}


# ---------------------------------------------------------------- forms

def F(q, side, fix, items):
    return dict(q=ST_OF[q] if isinstance(q, str) else q, side=side, fix=tuple(fix),
                items=[tuple(it) if it[0] != 'r' else ('r', tuple(it[1]), it[2]) for it in items])


def hasX(f):
    return any(it[0] == 'X' for it in f['items'])


def reps(f):
    return [it for it in f['items'] if it[0] == 'r']


def inst_cells(f, n, X):
    out = []
    for it in f['items']:
        if it[0] == 'c':
            out += list(it[1])
        elif it[0] == 'r':
            out += list(it[1]) * (it[2] + n)
        else:
            out += list(X)
    return out


def inst_conf(f, n, X):
    cells = inst_cells(f, n, X)
    h, rest = (cells[0], tuple(cells[1:])) if cells else (0, ())
    if f['side'] == 'R':
        return (f['q'], f['fix'], h, rest)
    return (f['q'], rest, h, f['fix'])


def shift(f, c):
    return dict(f, items=[('r', it[1], it[2] + c) if it[0] == 'r' else it for it in f['items']])


def at0(f):
    """the form at n = 0, flat"""
    return dict(f, items=[('c', tuple(it[1]) * it[2]) if it[0] == 'r' else it for it in f['items']])


def syms(cells):
    return clist(cells, lambda c: 'S%d' % c)


def coq_cells(f):
    parts = []
    for it in f['items']:
        if it[0] == 'c':
            if it[1]:
                parts.append(syms(it[1]))
        elif it[0] == 'r':
            parts.append('rep %s (%s)' % (syms(it[1]), 'n' if it[2] == 0 else '%d + n' % it[2]))
        else:
            parts.append('X')
    return ' ++ '.join(parts) if parts else '[]'


def coq_form(f):
    if f['side'] == 'R':
        return '(cfgR %s %s (%s))' % (ST[f['q']], syms(f['fix']), coq_cells(f))
    return '(cfgL %s (%s) %s)' % (ST[f['q']], coq_cells(f), syms(f['fix']))


def binders(f):
    vs = []
    if any(it[0] == 'r' for it in f['items']):
        vs.append('n')
    if hasX(f):
        vs.append('X')
    return vs


# ---------------------------------------------------------------- validation

def reaches(tab, c0, c1, maxn=400000):
    t1 = norm(c1)
    if norm(c0) == t1:
        return 0
    c = c0
    for i in range(maxn):
        c = cstep(tab, c)
        if c is None:
            return None
        if c[0] == t1[0] and c[2] == t1[2] and norm(c) == t1:
            return i + 1
    return None


def validate(tab, f0, f1, what, ns=range(0, 6)):
    rnd = random.Random(7)
    tails = [(), (1, 1, 0, 1), tuple(rnd.choice((0, 1)) for _ in range(9)) + (1,)]
    for n in ns:
        for X in (tails if hasX(f0) else [()]):
            got = reaches(tab, inst_conf(f0, n, X), inst_conf(f1, n, X))
            if got is None:
                raise NoClosure('%s: the machine does not reach the target at n=%d X=%r'
                                % (what, n, X))


# ---------------------------------------------------------------- arms

def decomp(f):
    """head prefix H, word w, cells after C2 (the form has one rep item)"""
    its = f['items']
    i = [k for k, it in enumerate(its) if it[0] == 'r'][0]
    C1 = [c for it in its[:i] for c in it[1]]
    w, b = its[i][1], its[i][2]
    C2 = [c for it in its[i + 1:] if it[0] == 'c' for c in it[1]]
    return C1 + list(w) * b, w, C2


def flat_cells(f):
    return [c for it in f['items'] if it[0] == 'c' for c in it[1]]


def flatside(cells):
    return (tuple(cells), (), 0, 0, ())


class Gen:
    def __init__(self, tab, mid, pins):
        self.tab = tab
        self.mid = mid
        self.arms = Arms(tab)
        self.inner = []          # nested inner rules
        self.out = []            # Coq text
        self.nlem = 0
        self.want = [(q_, s_) for q_ in range(4) for s_ in range(2) if (q_, s_) not in pins]
        self.firefams = []       # (lemma name, form F, family data) usable for fire witnesses

    def fresh(self, base):
        self.nlem += 1
        return '%s%d_%s' % (base, self.nlem, self.mid)

    def flags(self, f):
        x = hasX(f)
        if f['side'] == 'R':
            return True, not x
        return not x, True

    # one flat arm
    def arm_flat(self, f0, f1, what):
        el, er = self.flags(f0)
        c0 = self.sconf_flat(f0)
        c1 = self.sconf_flat(f1)
        ch = self.arms.derive(el, er, c0, c1, what)
        nm = self.fresh('af')
        segs = prog_coq(self.tab, self.inner, ch)
        self.out.append(ARM2 % dict(nm=nm, lhs=coq_conf(c0), rhs=coq_conf(c1),
                                    segs=';\n   '.join(segs), el=str(el).lower(),
                                    er=str(er).lower()))
        lem = self.fresh('pf')
        lemma = 'arm1_r' if f0['side'] == 'R' else 'arm1_l'
        flag = '(fun H => False_ind _ (diff_false_true H))' if hasX(f0) else '(fun _ => eq_refl)'
        xarg = 'X' if hasX(f0) else '[]'
        self.out.append('''Lemma %(lem)s : forall (n : nat) (X : list Sym),
  Reach1 tm %(f0)s %(f1)s.
Proof.
  intros n X.
  exact (%(lemma)s tm %(el)s %(er)s %(nm)s _ _ _ _ _ _ _ _
           ltac:(eapply narm_reach; [exact nrules_sound_%(mid)s | exact ok_%(nm)s])
           eq_refl eq_refl %(xarg)s %(flag)s).
Qed.

''' % dict(lem=lem, f0=coq_form(f0), f1=coq_form(f1),
           lemma=lemma, el=str(el).lower(), er=str(er).lower(), nm=nm, mid=self.mid,
           xarg=xarg, flag=flag))
        return lem, ('flat', c0, ch, el, er)

    def sconf_flat(self, f):
        cells = flat_cells(f) if not reps(f) else None
        assert cells is not None
        h, rest = (cells[0], cells[1:]) if cells else (0, [])
        if f['side'] == 'R':
            return (f['q'], flatside(f['fix']), h, flatside(rest))
        return (f['q'], flatside(rest), h, flatside(f['fix']))

    def fam_conf(self, f, r, s_):
        H, w, C2 = decomp(f)
        h, P = H[0], H[1:]
        sd = blk(tuple(P) + tuple(w) * r, w, s_, tuple(C2))
        if f['side'] == 'R':
            return (f['q'], flatside(f['fix']), h, sd)
        return (f['q'], sd, h, flatside(f['fix']))

    def needs_split(self, f):
        return bool(reps(f)) and not decomp(f)[0]

    def arm(self, f0, f1, what):
        """a lemma [forall n X, Reach1 tm f0 f1]; returns its name"""
        if not reps(f0) and not reps(f1):
            return self.arm_flat(f0, f1, what)[0]
        if self.needs_split(f0) or self.needs_split(f1):
            l0 = self.arm(at0(f0), at0(f1), what + ' (n = 0)')
            lS = self.arm(shift(f0, 1), shift(f1, 1), what + ' (n > 0)')
            lem = self.fresh('ps')
            self.out.append('''Lemma %(lem)s : forall (n : nat) (X : list Sym), Reach1 tm %(f0)s %(f1)s.
Proof. intros [|n] X; [exact (%(l0)s 0 X) | exact (%(lS)s n X)]. Qed.

''' % dict(lem=lem, f0=coq_form(f0), f1=coq_form(f1), l0=l0, lS=lS))
            return lem
        return self.arm_fam(f0, f1, what)

    def arm_fam(self, f0, f1, what):
        el, er = self.flags(f0)
        got = None
        for n0, st in ARM_GRID:
            arms = []
            ok = True
            for r in range(n0 + st):
                s_ = 0 if r < n0 else st
                c0, c1 = self.fam_conf(f0, r, s_), self.fam_conf(f1, r, s_)
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
        base = self.fresh('fa')
        for r, c0, c1, ch in arms:
            nm = '%s_%d' % (base, r)
            segs = prog_coq(self.tab, self.inner, ch)
            self.out.append(ARM2 % dict(nm=nm, lhs=coq_conf(c0), rhs=coq_conf(c1),
                                        segs=';\n   '.join(segs), el=str(el).lower(),
                                        er=str(er).lower()))
        self.out.append('Definition %s (r : nat) : LRule :=\n  match r with %s | _ => %s_%d end.\n\n'
                        % (base, ' '.join('| %d => %s_%d' % (r, base, r) for r, *_ in arms),
                           base, arms[0][0]))
        br = lambda body: ''.join('  destruct r as [|r].\n  { %s. }\n' % body(r)  # noqa: E731
                                  for r in range(n0 + st))
        H0, w0, C20 = decomp(f0)
        H1, w1, C21 = decomp(f1)
        lhsd = self.side_coq(f0, H0, w0, C20, n0, st)
        rhsd = self.side_coq(f1, H1, w1, C21, n0, st)
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

''' % dict(b=base, n0=n0, st=st, el=str(el).lower(), er=str(er).lower(), lhs=lhsd, rhs=rhsd,
           snd=br(lambda r: 'eapply narm_reach; [exact nrules_sound_%s | exact ok_%s_%d]'
                  % (self.mid, base, r)),
           cmp=br(lambda r: 'vm_compute; reflexivity')))
        lem = self.fresh('pa')
        lemma = 'armfam_r' if f0['side'] == 'R' else 'armfam_l'
        flag = '(fun H => False_ind _ (diff_false_true H))' if hasX(f0) else '(fun _ => eq_refl)'
        self.out.append('''Lemma %(lem)s : forall (n : nat) (X : list Sym), Reach1 tm %(f0)s %(f1)s.
Proof.
  intros n X.
  exact (%(lemma)s tm %(el)s %(er)s %(n0)d %(st)d %(b)s _ _ _ _ _ _ _ _ _ _ _ _
           ltac:(lia) %(b)s_reach %(b)s_lhs %(b)s_rhs n %(xarg)s %(flag)s).
Qed.

''' % dict(lem=lem, f0=coq_form(f0), f1=coq_form(f1), lemma=lemma, el=str(el).lower(),
           er=str(er).lower(), n0=n0, st=st, b=base, xarg='X' if hasX(f0) else '[]', flag=flag))
        self.firefams.append(dict(form=f0, base=base, n0=n0, st=st, el=el, er=er,
                                  arms=arms))
        return lem

    def side_coq(self, f, H, w, C2, n0, st):
        h, P = H[0], H[1:]
        sd = 'blk (%s ++ rep %s r) %s (astride %d %d r) %s' % (syms(P), syms(w), syms(w), n0, st,
                                                               syms(C2))
        if f['side'] == 'R':
            return 'mkC %s (sflat %s) %s (%s)' % (ST[f['q']], syms(f['fix']), SYM[h], sd)
        return 'mkC %s (%s) %s (sflat %s)' % (ST[f['q']], sd, SYM[h], syms(f['fix']))


# ---------------------------------------------------------------- the plan

def mk_coq(c):
    pre = syms(c.get('pre', []))
    if c['side'] == 'R':
        return '(fun l => cfgR %s %s (%s ++ l))' % (ST[ST_OF[c['q']]], syms(c['fix']), pre)
    return '(fun l => cfgL %s (%s ++ l) %s)' % (ST[ST_OF[c['q']]], pre, syms(c['fix']))


def cform(c, items):
    pre = tuple(c.get('pre', []))
    its = ([('c', pre)] if pre else []) + list(items)
    return F(c['q'], c['side'], c['fix'], its)


def pform(f):
    return F(f['q'], f['side'], f['fix'], f['items'])


def emit_closure_nest(cert, tab, mid):
    plan = cert['plan']
    pins = E.TR_PINS
    g = Gen(tab, mid, pins)
    try:
        body = build(g, plan, cert)
    except NoClosure as e:
        return E.CLOSURE_NONE % e, None
    head = """
(** ** The closure: a counter whose carry or overflow runs inner counts ([NestCountTr])

    Plan %(name)s (tools/closeouttr/le8/plans/).  Every count is
    [count_from_carry] (induction on the width); every carry and overflow is
    a chain of [LadderNest] arm families and inner counts; the board is
    [BoardCountTr] (a lap = a whole count of the width and one overflow). *)
From BBB4.Checkers Require Import LadderNest LadderCheckNestTr.
From BBB4.Counters Require Import NestCountTr.

""" % dict(name=plan.get('name', mid))
    return head + inner_coq(mid, g.inner) + ''.join(g.out) + body, dict(fill=None)


class Chain:
    """a list of forms with the pieces between them"""

    def __init__(self, name, forms, pieces):
        self.name, self.forms, self.pieces = name, forms, pieces


def emit_chain(g, vtab, name, forms, kinds):
    mid = g.mid
    pl = []
    for i, kd in enumerate(kinds):
        a, b = forms[i], forms[i + 1]
        validate(vtab, a, b, '%s piece %d' % (name, i))
        if kd[0] == 'arm':
            pl.append(('arm', g.arm(a, b, '%s piece %d' % (name, i)), i))
        else:
            lvname = kd[1]
            c = g.counters[lvname]
            npre = len(c.get('pre', []))
            it = a['items']
            k0 = 1 if npre else 0
            assert it[k0][0] == 'r', 'a count piece starts at the digits'
            cnt = 'n' if it[k0][2] == 0 else '%d + n' % it[k0][2]
            Y = coq_cells(dict(a, items=it[k0 + 1:]))
            pl.append(('count', 'count_%s_%s (%s) (%s)' % (lvname, mid, cnt, Y), i))

    def chain(i0, i1):
        lines = []
        for i in range(i0, i1):
            kd, ref, _ = pl[i]
            t = ('(reach1_0 tm _ _ (%s n X))' % ref) if kd == 'arm' else '(%s)' % ref
            lines.append('  apply (reach0_trans tm _ %s _ %s).' % (coq_form(forms[i + 1]), t))
        lines.append('  apply reach0_refl.')
        return '\n'.join(lines)
    arms = [i for i, (kd, _, _) in enumerate(pl) if kd == 'arm']
    if not arms:
        raise NoClosure('%s: a chain with no arm' % name)
    a = arms[0]
    g.out.append("""Lemma %(nm)s : forall (n : nat) (X : list Sym), Reach1 tm %(f0)s %(fm)s.
Proof.
  intros n X.
  apply (reach01 tm _ %(fa)s _).
  {
%(pre)s
  }
  apply (reach10 tm _ %(fb)s _ (%(ra)s n X)).
%(suf)s
Qed.

""" % dict(nm=name, f0=coq_form(forms[0]), fm=coq_form(forms[-1]), fa=coq_form(forms[a]),
           fb=coq_form(forms[a + 1]), ra=pl[a][1], pre=chain(0, a), suf=chain(a + 1, len(pl))))
    for i in range(1, len(forms) - 1):
        g.out.append("""Lemma %(nm)s_pre%(i)d : forall (n : nat) (X : list Sym), Reach0 tm %(f0)s %(fi)s.
Proof.
  intros n X.
%(ch)s
Qed.

""" % dict(nm=name, i=i, f0=coq_form(forms[0]), fi=coq_form(forms[i]), ch=chain(0, i)))
    return Chain(name, forms, pl)


def chain_fires(g, ch, fires):
    """fire lemmas [forall n X, Fires (forms[0] at 1 + n)] for every wanted
    instruction an arm family of the chain fires; fills `fires`"""
    tab, mid = g.tab, g.mid
    for i, f in enumerate(ch.forms[:-1]):
        for fd in g.firefams:
            if 'vis' in fd and fd.get('chain') != ch.name:
                continue
            ff = fd['form']
            for c in (0, 1):
                if shift(f, c) == ff:
                    fd.setdefault('at', (i, c))
                    fd['chain'] = ch.name
    for fd in g.firefams:
        if fd.get('chain') != ch.name or 'vis' in fd:
            continue
        el, er = fd['el'], fd['er']
        fd['vis'] = {r: nvisits_f(tab, g.want, el, er, c0, chp) for r, c0, c1, chp in fd['arms']}
        ok = [w for w in g.want if all(w in fd['vis'][r] for r in fd['vis'])]
        mine = [w for w in ok if w not in fires]
        if not mine:
            continue
        b = fd['base']
        i, c = fd['at']
        g.out.append("""Definition %(b)s_vis (r : nat) (t : Instr) : list lstep :=
  match r, t with
  %(vb)s
  | _, _ => []
  end.

Definition %(b)s_vsegs (r : nat) (t : Instr) : list nseg :=
  match r, t with
  %(sb)s
  | _, _ => []
  end.

""" % dict(b=b, vb='\n  '.join('| %d, (%s, %s) => %s' % (r, ST[w[0]], SYM[w[1]], coq_chain_l(fd['vis'][r][w][1]))
                                for r in sorted(fd['vis']) for w in mine),
           sb='\n  '.join('| %d, (%s, %s) => [%s]' % (r, ST[w[0]], SYM[w[1]],
                                                     '; '.join(coq_seg(sg, 0) for sg in fd['vis'][r][w][0]))
                          for r in sorted(fd['vis']) for w in mine)))
        n0, st = fd['n0'], fd['st']
        flag = '(fun H => False_ind _ (diff_false_true H))' if hasX(fd['form']) else '(fun _ => eq_refl)'
        lemma = 'fire_of_nfire_r' if fd['form']['side'] == 'R' else 'fire_of_nfire_l'
        br = ''.join('  destruct r as [|r].\n  { vm_compute; reflexivity. }\n' for _ in range(n0 + st))
        for w in mine:
            nm = 'fire_%s%d_%s' % ('ABCD'[w[0]], w[1], ch.name)
            fires[w] = nm
            g.out.append("""Lemma %(nm)s_vis : forall r, r < %(n0)d + %(st)d ->
  nfire tm %(el)s %(er)s nrules (%(b)s_vsegs r (%(q)s, %(s)s)) (%(b)s_vis r (%(q)s, %(s)s))
    (lr_lhs (%(b)s r)) = Some (%(q)s, %(s)s).
Proof. intros r Hr.
%(br)s  exfalso; lia.
Qed.

Lemma %(nm)s : forall (n : nat) (X : list Sym), Fires tm %(f0)s (%(q)s, %(s)s).
Proof.
  intros n X.
%(fb)s  exact (%(lemma)s tm %(el)s %(er)s nrules %(n0)d %(st)d (fun r => %(b)s_vsegs r (%(q)s, %(s)s))
           (fun r => %(b)s_vis r (%(q)s, %(s)s)) (fun r => lr_lhs (%(b)s r)) _ _ _ _ _ _ _
           ltac:(lia) nrules_sound_%(mid)s %(nm)s_vis %(b)s_lhs (%(nn)s) %(xa)s %(flag)s).
Qed.

""" % dict(nm=nm, n0=n0, st=st, el=str(el).lower(), er=str(er).lower(), b=b, q=ST[w[0]],
           s=SYM[w[1]], br=br, mid=mid, f0=coq_form(shift(ch.forms[0], 1)),
           fb=('  apply (fire_back tm _ _ _ (%s_pre%d (1 + n) X)).\n' % (ch.name, i)) if i else '',
           lemma=lemma, flag=flag, xa='X' if hasX(fd['form']) else '[]',
           nn=('%d + n' % (1 - c)) if 1 - c else 'n'))


def counter_carry(g, vtab, name, c):
    """carry_<name> and count_<name> for a counter or level"""
    mid = g.mid
    Z, O = tuple(c['Z']), tuple(c['O'])
    mk = mk_coq(c)
    cs = c.get('carry')
    chains = []
    if cs is None:
        f0 = cform(c, [('r', O, 0), ('c', Z), ('X',)])
        f1 = cform(c, [('r', Z, 0), ('c', O), ('X',)])
        validate(vtab, f0, f1, '%s carry' % name)
        car = g.arm(f0, f1, '%s carry' % name)
        prf = 'exact (%s k Y).' % car
    else:
        K0 = cs['K0']
        small = []
        for k in range(K0):
            f0 = cform(c, [('c', O * k + Z), ('X',)])
            f1 = cform(c, [('c', Z * k + O), ('X',)])
            validate(vtab, f0, f1, '%s carry k=%d' % (name, k))
            small.append(g.arm(f0, f1, '%s carry k=%d' % (name, k)))
        forms = [cform(c, [('r', O, K0), ('c', Z), ('X',)])]
        kinds = []
        for pc in cs['pieces']:
            forms.append(pform(pc[-1]))
            kinds.append(pc[:-1])
        last = cform(c, [('r', Z, K0), ('c', O), ('X',)])
        if forms[-1] != last:
            forms.append(last)
            kinds.append(['arm'])
        ch = emit_chain(g, vtab, 'chain_%s_%s' % (name, mid), forms, kinds)
        chains.append(ch)
        prf = ''.join('destruct k as [|k]; [exact (%s 0 Y)|].\n  ' % l for l in small) + \
            'exact (%s k Y).' % ch.name
    g.out.append("""Lemma carry_%(nm)s_%(mid)s : forall k Y,
  Reach1 tm (%(mk)s (rep %(O)s k ++ %(Z)s ++ Y)) (%(mk)s (rep %(Z)s k ++ %(O)s ++ Y)).
Proof.
  intros k Y.
  %(prf)s
Qed.

Lemma count_%(nm)s_%(mid)s : forall k Y,
  Reach0 tm (%(mk)s (rep %(Z)s k ++ Y)) (%(mk)s (rep %(O)s k ++ Y)).
Proof. exact (count_from_carry tm %(mk)s %(Z)s %(O)s carry_%(nm)s_%(mid)s). Qed.

""" % dict(nm=name, mid=mid, mk=mk, O=syms(O), Z=syms(Z), prf=prf))
    return chains


def build(g, plan, cert):
    from csim import parse as cparse
    vtab = cparse(plan['spec'])    # validation runs on csim's table
    mid = g.mid
    o = plan['outer']
    g.counters = dict(plan.get('levels', {}))
    g.counters['O'] = o
    for name, lv in plan.get('levels', {}).items():
        counter_carry(g, vtab, name, lv)
    carry_chains = counter_carry(g, vtab, 'O', o)
    Zo, Oo, To = tuple(o['Z']), tuple(o['O']), tuple(o['T'])
    mko = mk_coq(o)
    ov = plan['ovf']
    fires = {}
    pad = all(v == 0 for v in Zo) and not To
    if pad:
        g.out.append("""Lemma HZ_%(mid)s : forall l, lift (%(mk)s (l ++ %(Z)s ++ %(T)s)) = lift (%(mk)s (l ++ %(T)s)).
Proof.
  intros l. cbv beta. rewrite !app_nil_r, !app_assoc.
  exact (%(padl)s %(nz)d _ _ _).
Qed.

""" % dict(mid=mid, mk=mko, Z=syms(Zo), T=syms(To), nz=len(Zo),
           padl='lift_cfgR_padn' if o['side'] == 'R' else 'lift_cfgL_padn'))
    if ov.get('via') == 'carry':
        if not pad:
            raise NoClosure('overflow via the carry needs blank zeros and no terminator')
        if not carry_chains:
            raise NoClosure('overflow via the carry: the carry is one family; give it as a chain')
        Wo, d = Oo, 1
        Lmin = plan['outer']['carry']['K0'] + 1
        chain_fires(g, carry_chains[0], fires)
        ovf_prf = 'exact (ovf_of_carry tm %s %s %s %s carry_O_%s HZ_%s (%%(Lb)d + n)).' % (
            mko, syms(Zo), syms(Oo), syms(To), mid, mid)
        fire_prf = lambda nm: ('exact (fire_ovf_of_carry tm %s %s %s %s HZ_%s %d _ %s (%%(Lb)d - %d + n)).'
                               % (mko, syms(Zo), syms(Oo), syms(To), mid, Lmin, nm, Lmin))
    else:
        Wo, d, L0 = tuple(ov['W']), ov['d'], ov['L0']
        forms = [cform(o, [('r', Oo, L0), ('c', Wo + To)])]
        kinds = []
        for pc in ov['pieces']:
            forms.append(pform(pc[-1]))
            kinds.append(pc[:-1])
        last = cform(o, [('r', Zo, L0 + d), ('c', Wo + To)])
        if forms[-1] != last:
            forms.append(last)
            kinds.append(['arm'])
        ch = emit_chain(g, vtab, 'ovf_%s' % mid, forms, kinds)
        chain_fires(g, ch, fires)
        Lmin = L0 + 1
        ovf_prf = ('replace (%%(Lb)d + n + %d) with (%d + (%%(Lb)d - %d + n)) by lia.\n'
                   '  exact (ovf_%s (%%(Lb)d - %d + n) []).' % (d, L0 + d, L0, mid, L0))
        fire_prf = lambda nm: 'exact (%s (%%(Lb)d - %d + n) []).' % (nm, Lmin)
    missing = [w for w in g.want if w not in fires]
    if missing:
        raise NoClosure('no fire witness for %s'
                        % ' '.join('ABCD'[q] + str(s_) for q, s_ in missing))
    # the boot: a visit to Z^L W T with L >= Lmin
    got = boot_count(plan['spec'], o, Wo, To, Lmin)
    if got is None:
        raise NoClosure('no boot at Z^L W T')
    t0, Lb = got
    fc = []
    for q in range(4):
        for s_ in range(2):
            if (q, s_) in fires:
                fc.append('    ' + (fire_prf(fires[(q, s_)]) % dict(Lb=Lb)))
            else:
                fc.append('    exfalso; apply Hnp; simpl; tauto.')
    return """Lemma hovf_%(mid)s : forall n,
  Reach1 tm (%(mk)s (rep %(O)s (%(Lb)d + n) ++ %(W)s ++ %(T)s)) (%(mk)s (rep %(Z)s (%(Lb)d + n + %(d)d) ++ %(W)s ++ %(T)s)).
Proof.
  intros n.
  %(ovf)s
Qed.

Lemma hfire_%(mid)s : forall t, ~ In t pins_%(mid)s -> forall n,
  Fires tm (%(mk)s (rep %(O)s (%(Lb)d + n) ++ %(W)s ++ %(T)s)) t.
Proof.
  intros [q s] Hnp n. destruct q, s.
%(fc)s
Qed.

Lemma bootl_%(mid)s :
  stepn tm %(t0)d InitES = Some (lift (ccfg %(mk)s %(Z)s %(W)s %(T)s %(d)d %(Lb)d 0)).
Proof.
  assert (H : match csteps tm %(t0)d c0 with
              | Some c => ceqb c (ccfg %(mk)s %(Z)s %(W)s %(T)s %(d)d %(Lb)d 0)
              | None => false end = true) by (vm_compute; reflexivity).
  destruct (csteps tm %(t0)d c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

Theorem nqhtr_%(mid)s : NeverQuasiHaltsTr tm_%(mid)s.
Proof.
  exact (boardC_neverqhtr tm_%(mid)s pins_%(mid)s %(mk)s %(Z)s %(O)s %(W)s %(T)s %(d)d %(Lb)d
           count_O_%(mid)s hovf_%(mid)s hfire_%(mid)s %(t0)d bootl_%(mid)s).
Qed.
""" % dict(mid=mid, mk=mko, Z=syms(Zo), O=syms(Oo), W=syms(Wo), T=syms(To), d=d, Lb=Lb,
           ovf=ovf_prf % dict(Lb=Lb), fc='\n'.join(fc), t0=t0)


def boot_count(spec, o, W, T, Lmin, steps=300000):
    """the first time the outer counter reads Z^L W T with L >= Lmin; (t, L)"""
    from csim import parse, step
    tab = parse(spec)
    Z = list(o['Z'])
    pre = list(o.get('pre', []))
    q0 = ST_OF[o['q']]
    c = (0, (), 0, ())
    for t in range(steps):
        q, L, h, R = norm(c)
        if q == q0 and (L if o['side'] == 'R' else R) == tuple(o['fix']):
            cells = [h] + list(R if o['side'] == 'R' else L)
            if cells[:len(pre)] == pre:
                cells = cells[len(pre):]
                tail = list(W) + list(T)
                n = 0
                while cells[:len(Z)] == Z or (not any(cells) and any(tail)):
                    if cells[:len(Z)] != Z:
                        cells = cells + [0] * len(Z)
                    cells = cells[len(Z):]
                    n += 1
                    if n > 200:
                        break
                if n >= Lmin and (cells + [0] * len(tail))[:len(tail)] == tail and not any(cells[len(tail):]):
                    return t, n
        c = step(tab, c)
    return None


def nvisits_f(tab, want, el, er, fl, prog):
    """emit_step.nvisits with the arm's own tail flags"""
    if not (isinstance(prog, tuple) and prog[:1] == ('NEST',)):
        prog = ('NEST', [('NCh', prog)], [])
    _t, segs, rules = prog
    rr = [(a, b_) for a, b_, _c in rules]
    seen = {}
    for k in range(len(segs) + 1):
        got = nest.nrun(tab, el, er, rr, segs[:k], fl)
        if got is None:
            break
        ck = got[0]
        chs = ([segs[k][1][:i] for i in range(len(segs[k][1]) + 1)]
               if k < len(segs) and segs[k][0] == 'NCh' else [[]])
        for base in chs:
            for kind in ('SWin', 'SWinL', 'SWinR'):
                for n in range(0, 600):
                    g = LC.srun(tab, el, er, base + [(kind, n)], ck)
                    if g is None:
                        break
                    seen.setdefault((g[0][0], g[0][2]),
                                    (list(segs[:k]), base + [(kind, n)]))
            if all(i in seen for i in want):
                return seen
    return seen


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('plan')
    ap.add_argument('-o', '--out', required=True)
    ap.add_argument('--nested', action='store_true', help='allow nested arm programs (slow)')
    a = ap.parse_args()
    plan = json.load(open(a.plan))
    if isinstance(plan, list):
        plan = plan[0]
    if 'plan' in plan:          # a batch certificate carrying the plan
        plan = plan['plan']
    spec = plan['spec']
    o = plan['outer']
    cert = dict(spec=spec, closed=True, kind='nest', plan=plan,
                family=dict(state=o['q'], head=0, side=o['side'], other_side_cells=o['fix'],
                            digits=[o['Z'], o['O']], near_head_prefix=[], terminator=o['T'],
                            terminators_by_phase=[o['T']], n_phases=1, base=2, digit_len=len(o['Z']),
                            code='binary', value_step_per_anchor_visit=1, numeration='nest'),
                fill=dict(widens_by=1, target_prefix=[], target_fill_digit=0, target_suffix=[],
                          lands_in_phase=0),
                arms=[], ladder=[],
                boot=dict(steps_from_blank=0, digits_lsb_first=[], phase=0, cells=[]))
    S.NEST_OK[0] = '--nested' in sys.argv
    E.emit_closure = emit_closure_nest
    E.TR_PINS = E.unfired(spec, 10 ** 6)
    good, bad, cd = E.emit(cert, a.out)
    print('%s: closure %s' % (a.out, 'BUILT' if cd else 'not built'))
    return 0 if cd else 1


if __name__ == '__main__':
    sys.exit(main())
