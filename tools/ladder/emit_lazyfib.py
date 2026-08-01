#!/usr/bin/env python3
"""UNTRUSTED emitter: a LAZY-fibonacci row -> a Coq board for LadderCheck 12.

LADDER_PLAN 4v/4w measured six core rows whose counter reads in the kernel's
own fibonacci numeration (`LadderFam.fibw` = 1,1,2,3,5,8) and stands on the
LAZY representative of it -- LSB-first, `d0 = 1`, no two zeros adjacent, top
digit 1 -- where `LadderFam.fibdec` and `LadderCheck.fibokb` pick the greedy
one.  `LadderCheck` section 3d is the class law for that representative and
section 12 the board it feeds; this file builds the board's data.

It does NOT go through `valfam`: those rows' family is not a fit but a
measurement (`tools/ladder/fiblazy.py`, 23,614 values per row, zero
failures), and it is the same on all six --

    anchor    (StB or StC, head S1), the counter on the RIGHT, far side empty
    digits    one cell per digit, [[S0];[S1]]
    prefix    none;  terminator  none
    code      FibL, step 1, one phase (the fill is a function of the width)

-- so the family is read off the machine here rather than fitted.  Everything
emitted is re-checked by the Coq kernel: a wrong chain, a wrong step count or
a wrong split makes the board fail to compile.

Usage:  emit_lazyfib.py SPEC [-o OUT.v]
"""
import argparse
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, '..', 'counters'))

from ladderarm import parse_tm                                       # noqa: E402
import lapcert as LC                                                 # noqa: E402
from emit_ladder import (ST, SYM, mach_id, clist, syms, coq_conf,     # noqa: E402
                         coq_chain, coq_chain_l, coq_table, blk,
                         last_visit, _gray_visits, NoClosure, AVOID_ARM,
                         _rbranches)

DIGS = [(0,), (1,)]          # the digit words: one cell each


def flc(i):
    """[LadderCheck.flc i] as (u, t, w, u', t', w').  The run unit is a WORD:
    the lazy increment sends the low run [1^(2m)] to the alternating
    [(1 0)^m], which no repeat of a single digit spells."""
    return [([], [1, 1], [0], [], [1, 0], [1]),
            ([1], [1, 1], [0], [1], [1, 0], [1])][i]


def lazb(ds):
    """[LadderCheck.fiblazb]: LSB-first, [d0 = 1], no two ZEROS adjacent, and
    the top digit [1]."""
    if not ds or ds[0] != 1 or ds[-1] != 1:
        return False
    return all(not (ds[i] == 0 and ds[i + 1] == 0) for i in range(len(ds) - 1))


def lazfill(k):
    """[LadderFam.lazfill k]: the smallest string of width [k + 1]."""
    m = k // 2
    return ([1] if k % 2 else []) + [1, 0] * m + [1]


def cells_of(ds):
    out = []
    for d in ds:
        out.extend(DIGS[d])
    return tuple(out)


def ctape_seq(tab, n):
    """The exact [cconf] after each of [n] steps from the blank tape.

    [CTape.ctape_move] does not normalise -- a blank the head materialises by
    stepping back over it is [S0 :: r] and not [r] -- and [RuleSound] and the
    boot are equations on [cconf], so the boot has to be read this way and
    not through any run-length view."""
    l, h, r, q = [], 0, [], 0
    out = [(q, tuple(l), h, tuple(r))]
    for _ in range(n):
        e = tab.get((q, h))
        if e is None:
            break
        w, d, q2 = e
        if d > 0:
            l, h, r = [w] + l, (r[0] if r else 0), r[1:]
        else:
            r, h, l = [w] + r, (l[0] if l else 0), l[1:]
        q = q2
        out.append((q, tuple(l), h, tuple(r)))
    return out


def find_anchor(tab, steps=4000):
    """The anchor and the boot: the first index at which the machine stands
    on a MEMBER with nothing on the far side.

    The far side must be EXACTLY empty and the counter side must end in a
    [1], because [fam_cfg] spells the anchor with no trailing blank and a
    member never ends in a [0]."""
    seq = ctape_seq(tab, steps)
    for t, (q, l, h, r) in enumerate(seq):
        if l != () or h != 1:
            continue
        ds = list(r)
        if lazb(ds):
            return q, h, t, ds
    raise NoClosure('no anchor: no index below %d has an empty far side and '
                    'a lazy member on the right' % steps)


def derive(tab, e0, e1, c0, c1, what):
    ch = LC.derive_chain(tab, e0, e1, c0, c1, maxdepth=32, nmax=120, lift=True)
    if ch is None:
        raise NoClosure('%s: no chain' % what)
    got = LC.srun(tab, e0, e1, ch, c0)
    if got is None or got[0] != c1:
        raise NoClosure('%s: chain lands off the rhs' % what)
    if got[2] == 0:
        raise NoClosure('%s: zero-step rule' % what)
    return ch, got[1], got[2]


def conf(q, h, sd):
    """The counter is the RIGHT side on all six rows and the far side is
    empty, which is [cls_conf] at [fm_left = false], [fm_other = []]."""
    return (q, ((), (), 0, 0, ()), h, sd)


def interior_at(tab, q, h, n0, stride):
    got = []
    for i in range(2):
        u, t, w, u2, t2, w2 = flc(i)
        for r in range(n0 + stride):
            s = 0 if r < n0 else stride
            c0 = conf(q, h, blk(cells_of(u) + cells_of(t) * r,
                                cells_of(t), s, cells_of(w)))
            c1 = conf(q, h, blk(cells_of(u2) + cells_of(t2) * r,
                                cells_of(t2), s, cells_of(w2)))
            if c0 == c1:
                return None
            try:
                ch, ca, cb = derive(tab, False, True, c0, c1,
                                    'interior class %d r=%d' % (i, r))
            except NoClosure:
                return None
            got.append((i, r, s, c0, c1, ch, ca, cb))
    return got


def fill_at(tab, q, h, n0):
    """The fill arms.  The stride is TWO and it has to be: [lazfill]'s shape
    is chosen by the width's PARITY, so an arm serving widths [r, r+s, ...]
    can only have one shape if [s] is even."""
    got = []
    W = cells_of([1, 0])
    for r in range(1, n0 + 2):
        s = 0 if r < n0 else 2
        half = r // 2
        fpre = [1] if r % 2 else []
        hit = None
        for w1 in range(r + 1):
            lhs = conf(q, h, blk(DIGS[1] * w1, DIGS[1], s, DIGS[1] * (r - w1)))
            for m1 in range(half + 1):
                rhs = conf(q, h, blk(cells_of(fpre) + W * m1, W, s // 2,
                                     W * (half - m1) + cells_of([1])))
                if lhs == rhs:
                    continue
                try:
                    ch, ca, cb = derive(tab, True, True, lhs, rhs,
                                        'fill r=%d' % r)
                except NoClosure:
                    continue
                hit = (r, s, w1, r - w1, m1, half - m1, lhs, rhs, ch, ca, cb)
                break
            if hit:
                break
        if hit is None:
            return None
        got.append(hit)
    return got


def build(spec, steps=4000):
    tab = parse_tm(spec)
    q, h, t0, ds0 = find_anchor(tab, steps)

    inter = n0i = sti = None
    for n0 in range(0, 4):
        for st in range(1, 5):
            hit = interior_at(tab, q, h, n0, st)
            if hit is not None:
                inter, n0i, sti = hit, n0, st
                break
        if inter is not None:
            break
    if inter is None:
        raise NoClosure('interior class arm: no chain at any threshold 0..3 '
                        'and stride 1..4')

    fill = n0f = None
    for n0 in range(1, 5):
        hit = fill_at(tab, q, h, n0)
        if hit is not None:
            fill, n0f = hit, n0
            break
    if fill is None:
        raise NoClosure('fill arm: no chain at any threshold 1..4 or copy '
                        'split (the stride is pinned at 2 by the parity)')

    # The liveness: the states that recur.  On these rows StA fires once, at
    # step 0, and nothing targets it, so it is the quiet state and the board
    # is the QUASIHALTING twin.
    targets = set()
    for (qq, ss), e in tab.items():
        if e is not None:
            targets.add(e[2])
    missing = [i for i in range(4) if i not in targets]
    if len(missing) != 1:
        raise NoClosure('%d states are the target of no transition; the board '
                        'names exactly ONE quiet state' % len(missing))
    qa = missing[0]
    if qa != 0:
        raise NoClosure('the quiet state is %s, not the start state' % ST[qa])
    sq = last_visit(tab, qa, t0)
    if sq is None:
        raise NoClosure('%s never enters %s below the boot anchor' % (spec, ST[qa]))
    want = [i for i in range(4) if i != qa]

    vis = {}
    for (r, _s, _w1, _w2, _m1, _m2, lhs, _rhs, fch, _ca, _cb) in fill:
        seen = _gray_visits(tab, lhs, fch, want)
        gap = [ST[i] for i in want if i not in seen]
        if gap:
            raise NoClosure('the fill anchor at width index %d reaches no %s'
                            % (r, ','.join(gap)))
        vis[r] = {i: seen[i] for i in want}

    return dict(spec=spec, q=q, h=h, t0=t0, ds0=ds0, inter=inter,
                n0i=n0i, sti=sti, fill=fill, n0f=n0f, vis=vis, want=want,
                qa=qa, sq=sq)


# ------------------------------------------------------------------ the Coq --

HEAD = '''(** * LDR_%(mid)s: machine %(spec)s, boarded by the LAZY FIBONACCI ladder.

    Emitted by [tools/ladder/emit_lazyfib.py] (UNTRUSTED); every line below is
    re-checked by the kernel.

    The counter reads in the kernel's own fibonacci numeration -- the digit at
    index [i] carries weight [1, 1, 2, 3, 5, 8, ...] -- and stands on its LAZY
    representative: LSB-first, [d0 = 1], NO TWO ZEROS ADJACENT, top digit [1].
    That is a different canonical form from [LadderCheck] section 3c's, not a
    different numeration; LADDER_PLAN 4v and 4w measured it twice, by
    independent routes, over 23,614 values of this row.

    The board is [LadderCheck.boardL_iqh] (section 12).  This row QUASIHALTS:
    [StA] fires once, at step 0, and is the target of no transition, so the
    theorem is the [iqh] triple and not [NeverQuasiHaltsSt].

    [Print Assumptions] = [functional_extensionality_dep] only. *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Census Require Import TNF_QH.
From BBB4.Counters Require Import WTape LapGlueQuiet.
From BBB4.Checkers Require Import LapDecider LapAvoid LadderKernel LadderFam.
From BBB4.Checkers Require Import LadderCheck.
Import ListNotations.

Definition mk (w : Sym) (d : Dir) (n : St) : option Trans :=
  Some (mkTrans w d n).

(** %(spec)s *)
Definition tm_%(mid)s : TM := fun q s => match q, s with
%(table)s end.
Local Notation tm := tm_%(mid)s.

(** ** The family, as DATA

    One cell per digit, no prefix, no terminator, the counter on the RIGHT
    with an empty far side, code [FibL] and step 1.  [fm_fills] is EMPTY: at
    [FibL] the fill is [lazfill], a function of the width, so there is no
    [Fill] record to carry and the family is one-phase whatever the width
    does.  [fam_fill] falls through to [carry_fill], whose [f_to] is 0, which
    is the only field [fam_succ] still reads. *)
Definition fam_%(mid)s : Fam :=
  mkFam 2 [[S0];[S1]] [] [[]] FibL 1 [] %(anchor)s %(head)s false [].
Local Notation FAM := fam_%(mid)s.

(** ** The ladder, as DATA

    Empty: every arm below derives from the machine's own window, cycle and
    rotation steps, with no earlier rule invoked. *)
Definition lad_%(mid)s : list (LRule * list rstep) := [].
Local Notation lad := lad_%(mid)s.

Definition rules_%(mid)s : list LRule := map fst lad.
Local Notation rules := rules_%(mid)s.

Lemma ladder_ok_%(mid)s : check_ladder tm [] lad = true.
Proof. vm_compute. reflexivity. Qed.

Lemma rules_sound_%(mid)s : Forall (RuleSound tm false false) rules.
Proof. apply rule_sound_nil. exact ladder_ok_%(mid)s. Qed.

'''

IARM = '''Definition iarm%(i)d_%(r)d_%(mid)s : LRule :=
  mkLRule (%(lhs)s)
          (%(rhs)s) %(ca)d %(cb)d.
Definition ch_iarm%(i)d_%(r)d_%(mid)s : list rstep := %(ch)s.
Lemma ok_iarm%(i)d_%(r)d_%(mid)s :
  check_arm tm (negb false) false rules iarm%(i)d_%(r)d_%(mid)s
            ch_iarm%(i)d_%(r)d_%(mid)s = true.
Proof. vm_compute. reflexivity. Qed.

'''

FARM = '''Definition farm%(r)d_%(mid)s : LRule :=
  mkLRule (%(lhs)s)
          (%(rhs)s) %(ca)d %(cb)d.
Definition ch_farm%(r)d_%(mid)s : list rstep := %(ch)s.
Lemma ok_farm%(r)d_%(mid)s :
  check_arm tm true true rules farm%(r)d_%(mid)s ch_farm%(r)d_%(mid)s = true.
Proof. vm_compute. reflexivity. Qed.

'''

DISP = '''(** ** The arms, as DATA

    Two interior classes (section 3d's, split on the PARITY of the low run of
    ones) at threshold %(n0i)d stride %(sti)d, and one fill arm per WIDTH
    index at threshold %(n0f)d stride 2 -- the stride the parity pins. *)
Definition iarm_%(mid)s (i r : nat) : LRule :=
  match i, r with
  %(ibr)s
  | _, _ => iarm0_0_%(mid)s   (* unreachable: i < 2 and r < N0i + sti *)
  end.

Definition farm_%(mid)s (r : nat) : LRule :=
  match r with
  %(fbr)s
  | _ => farm%(r0)d_%(mid)s   (* unreachable: 1 <= r < N0f + 2 *)
  end.

Definition fw1_%(mid)s (r : nat) : nat := match r with %(b1)s | _ => 0 end.
Definition fw2_%(mid)s (r : nat) : nat := match r with %(b2)s | _ => 0 end.
Definition fm1_%(mid)s (r : nat) : nat := match r with %(b3)s | _ => 0 end.
Definition fm2_%(mid)s (r : nat) : nat := match r with %(b4)s | _ => 0 end.

(** One chain per state per fill arm.  [vis_of_run] turns each into a visit
    and [topsL_cofinal] says the tops keep coming, which is all the liveness
    needs. *)
Definition vis_%(mid)s (r : nat) (q : St) : list lstep :=
  match r, q with
  %(vb)s
  | _, _ => []
  end.

'''

THM = '''Lemma iarm_sound_%(mid)s : forall i r,
  i < 2 -> r < %(n0i)d + %(sti)d ->
  RuleSound tm (negb (fm_left FAM)) (fm_left FAM) (iarm_%(mid)s i r).
Proof.
  intros i r Hi Hr.
%(isound)s  exfalso; lia.
Qed.

Lemma iarm_lhs_%(mid)s : forall i r, i < 2 -> r < %(n0i)d + %(sti)d ->
  lr_lhs (iarm_%(mid)s i r)
    = cls_conf FAM (cls_sideW FAM (cw_u (flc i)) (cw_t (flc i)) r
                      (astride %(n0i)d %(sti)d r) (cw_w (flc i))).
Proof.
  intros i r Hi Hr.
%(icomp)s  exfalso; lia.
Qed.

Lemma iarm_rhs_%(mid)s : forall i r, i < 2 -> r < %(n0i)d + %(sti)d ->
  lr_rhs (iarm_%(mid)s i r)
    = cls_conf FAM (cls_sideW FAM (cw_u' (flc i)) (cw_t' (flc i)) r
                      (astride %(n0i)d %(sti)d r) (cw_w' (flc i))).
Proof.
  intros i r Hi Hr.
%(icomp)s  exfalso; lia.
Qed.

Lemma iarm_cb_%(mid)s : forall i r, i < 2 -> r < %(n0i)d + %(sti)d ->
  0 < lr_cb (iarm_%(mid)s i r).
Proof.
  intros i r Hi Hr.
%(ilia)s  exfalso; lia.
Qed.

Lemma farm_sound_%(mid)s : forall r, 1 <= r -> r < %(n0f)d + 2 ->
  RuleSound tm true true (farm_%(mid)s r).
Proof.
  intros r H1 Hr.
%(fsound)s  exfalso; lia.
Qed.

Lemma farm_lhs_%(mid)s : forall r, 1 <= r -> r < %(n0f)d + 2 ->
  lr_lhs (farm_%(mid)s r)
    = cls_conf FAM (run_sideW FAM [1] (fw1_%(mid)s r)
                      (astride %(n0f)d 2 r) (fw2_%(mid)s r) 0 [] []).
Proof.
  intros r H1 Hr.
%(fcomp)s  exfalso; lia.
Qed.

Lemma farm_rhs_%(mid)s : forall r, 1 <= r -> r < %(n0f)d + 2 ->
  lr_rhs (farm_%(mid)s r)
    = cls_conf FAM (run_sideW FAM [1;0] (fm1_%(mid)s r)
                      (Nat.div2 (astride %(n0f)d 2 r)) (fm2_%(mid)s r) 0
                      (if Nat.even r then [] else [1]) [1]).
Proof.
  intros r H1 Hr.
%(fcomp)s  exfalso; lia.
Qed.

Lemma farm_cb_%(mid)s : forall r, 1 <= r -> r < %(n0f)d + 2 ->
  0 < lr_cb (farm_%(mid)s r).
Proof.
  intros r H1 Hr.
%(flia)s  exfalso; lia.
Qed.

Lemma fw_%(mid)s : forall r, 1 <= r -> r < %(n0f)d + 2 ->
  fw1_%(mid)s r + fw2_%(mid)s r = r.
Proof.
  intros r H1 Hr.
%(flia)s  exfalso; lia.
Qed.

Lemma fm_%(mid)s : forall r, 1 <= r -> r < %(n0f)d + 2 ->
  fm1_%(mid)s r + fm2_%(mid)s r = Nat.div2 r.
Proof.
  intros r H1 Hr.
%(flia)s  exfalso; lia.
Qed.

Lemma boot_%(mid)s :
  csteps tm %(t0)d c0 = Some (fam_cfg FAM (%(ds0)s, 0, 0)).
Proof. vm_compute. reflexivity. Qed.

Lemma vis_ok_%(mid)s : forall r q, q <> %(qa)s -> 1 <= r ->
  r < %(n0f)d + 2 ->
  srun_st tm true true (vis_%(mid)s r q) (lr_lhs (farm_%(mid)s r)) = Some q.
Proof.
  intros r q Hq H1 Hr.
%(fvis)s  exfalso; lia.
Qed.

(** *** The arms avoid the quiet state

    Recomputed from the SAME chains the kernel already replays: a chain whose
    trace touches [%(qa)s] evaluates to [false] and this file fails to
    compile. *)
%(avarms)s
Lemma iarm_avoid_%(mid)s : forall i r,
  i < 2 -> r < %(n0i)d + %(sti)d ->
  RuleAvoid tm (negb (fm_left FAM)) (fm_left FAM) %(qa)s (iarm_%(mid)s i r).
Proof.
  intros i r Hi Hr.
%(bav)s  exfalso; lia.
Qed.

Lemma farm_avoid_%(mid)s : forall r, 1 <= r -> r < %(n0f)d + 2 ->
  RuleAvoid tm true true %(qa)s (farm_%(mid)s r).
Proof.
  intros r H1 Hr.
%(fav)s  exfalso; lia.
Qed.

(** *** The quiet state's last visit, and the window from it to the anchor *)
Lemma qvis_%(mid)s : VisitsAt tm %(qa)s %(sq)d.
Proof. apply bootvis_chk_sound. vm_compute. reflexivity. Qed.

Lemma qwin_%(mid)s : forall n c, %(sq)d < n < %(t0)d ->
  stepn tm n InitES = Some c -> fst c <> %(qa)s.
Proof.
  intros n c Hn Hstep.
  exact (bootquiet_chk_sound tm %(qa)s %(sq1)d %(win)d
           ltac:(vm_compute; reflexivity) n c ltac:(lia) Hstep).
Qed.

(** The machine-level theorem.  The counter laps forever over the lazy
    fibonacci numeration and every state but [%(qa)s] recurs; [%(qa)s] stops
    firing after index %(sq)d -- it is entered once, at step 0, and is the
    target of no transition.  [boardL_iqh] returns the exact bound and it is
    weakened to the census tier's 2000. *)
Definition iqh (tm : TM) : Prop :=
  NonHalt tm /\\ QHBound 2000 tm /\\ QuasiHaltsSt tm.

Theorem iqh_%(mid)s : iqh tm.
Proof.
  assert (H : NonHalt tm /\\ QHBound (S %(sq)d) tm /\\ QuasiHaltsSt tm).
  { apply (boardL_iqh tm FAM iarm_%(mid)s %(n0i)d %(sti)d
                      farm_%(mid)s %(n0f)d
                      fw1_%(mid)s fw2_%(mid)s fm1_%(mid)s fm2_%(mid)s
                      %(ds0)s %(t0)d %(qa)s %(sq)d vis_%(mid)s).
    - vm_compute; reflexivity.
    - vm_compute; reflexivity.
    - vm_compute; reflexivity.
    - vm_compute; reflexivity.
    - repeat constructor.
    - vm_compute; lia.
    - vm_compute; reflexivity.
    - exact boot_%(mid)s.
    - lia.
    - exact iarm_sound_%(mid)s.
    - exact iarm_lhs_%(mid)s.
    - exact iarm_rhs_%(mid)s.
    - exact iarm_cb_%(mid)s.
    - lia.
    - exact fw_%(mid)s.
    - exact fm_%(mid)s.
    - exact farm_sound_%(mid)s.
    - exact farm_lhs_%(mid)s.
    - exact farm_rhs_%(mid)s.
    - exact farm_cb_%(mid)s.
    - exact iarm_avoid_%(mid)s.
    - exact farm_avoid_%(mid)s.
    - exact vis_ok_%(mid)s.
    - exact qvis_%(mid)s.
    - exact qwin_%(mid)s. }
  destruct H as (Hn & Hb & Hq).
  split; [exact Hn | split; [| exact Hq]].
  apply (qhbound_mono (S %(sq)d) 2000); [lia | exact Hb].
Qed.
'''


def emit(cd, out):
    spec = cd['spec']
    mid = mach_id(spec)
    n0i, sti, n0f = cd['n0i'], cd['sti'], cd['n0f']
    nA, nF = n0i + sti, n0f + 2
    L = [HEAD % dict(mid=mid, spec=spec, table=coq_table(spec),
                     anchor=ST[cd['q']], head=SYM[cd['h']])]
    for i, r, _s, c0, c1, ch, ca, cb in cd['inter']:
        L.append(IARM % dict(i=i, r=r, mid=mid, lhs=coq_conf(c0),
                             rhs=coq_conf(c1), ca=ca, cb=cb,
                             ch=coq_chain(ch)))
    for r, _s, _w1, _w2, _m1, _m2, lhs, rhs, ch, ca, cb in cd['fill']:
        L.append(FARM % dict(r=r, mid=mid, lhs=coq_conf(lhs),
                             rhs=coq_conf(rhs), ca=ca, cb=cb,
                             ch=coq_chain(ch)))
    L.append(DISP % dict(
        mid=mid, r0=cd['fill'][0][0], n0i=n0i, sti=sti, n0f=n0f,
        ibr='\n  '.join('| %d, %d => iarm%d_%d_%s' % (i, r, i, r, mid)
                        for i, r, *_ in cd['inter']),
        fbr='\n  '.join('| %d => farm%d_%s' % (r, r, mid)
                        for r, *_ in cd['fill']),
        b1=' '.join('| %d => %d' % (r, w1) for r, _s, w1, *_ in cd['fill']),
        b2=' '.join('| %d => %d' % (r, w2)
                    for r, _s, _w1, w2, *_ in cd['fill']),
        b3=' '.join('| %d => %d' % (r, m1)
                    for r, _s, _w1, _w2, m1, *_ in cd['fill']),
        b4=' '.join('| %d => %d' % (r, m2)
                    for r, _s, _w1, _w2, _m1, m2, *_ in cd['fill']),
        vb='\n  '.join('| %d, %s => %s' % (r, ST[i], coq_chain_l(ch))
                       for r in sorted(cd['vis'])
                       for i, ch in sorted(cd['vis'][r].items()))))

    def ibranches(body):
        out2 = []
        for i in range(2):
            rb = []
            for r in range(nA):
                rb.append('    destruct r as [|r].\n    { %s. }\n'
                          % (body % dict(i=i, r=r, mid=mid)))
            out2.append('  destruct i as [|i].\n  {\n%s    exfalso; lia.\n  }\n'
                        % ''.join(rb))
        return ''.join(out2)

    def fbranches(body):
        return _rbranches(nF, lambda r: (body % dict(r=r, mid=mid)) + '.', lo=1)

    qa, sq = ST[cd['qa']], cd['sq']
    av = []
    for i, r, _s, *_ in cd['inter']:
        av.append(AVOID_ARM % dict(nm='iarm%d_%d' % (i, r), mid=mid, qa=qa,
                                   el='(negb (fm_left FAM))',
                                   er='(fm_left FAM)'))
    for r, *_ in cd['fill']:
        av.append(AVOID_ARM % dict(nm='farm%d' % r, mid=mid, qa=qa,
                                   el='true', er='true'))
    L.append(THM % dict(
        mid=mid, n0i=n0i, sti=sti, n0f=n0f, t0=cd['t0'],
        ds0=clist(cd['ds0'], str), qa=qa, sq=sq, sq1=sq + 1,
        win=cd['t0'] - sq - 1, avarms=''.join(av),
        isound=ibranches('eapply arm_sound; [exact rules_sound_%(mid)s '
                         '| exact ok_iarm%(i)d_%(r)d_%(mid)s]'),
        icomp=ibranches('vm_compute; reflexivity'),
        ilia=ibranches('vm_compute; lia'),
        fsound=fbranches('eapply arm_sound; [exact rules_sound_%(mid)s '
                         '| exact ok_farm%(r)d_%(mid)s]'),
        fcomp=fbranches('vm_compute; reflexivity'),
        flia=fbranches('vm_compute; lia'),
        bav=ibranches('exact av_iarm%(i)d_%(r)d_%(mid)s'),
        fav=fbranches('exact av_farm%(r)d_%(mid)s'),
        fvis=fbranches('destruct q; '
                       'try (exfalso; apply Hq; reflexivity); '
                       'vm_compute; reflexivity')))
    open(out, 'w').write(''.join(L))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('spec')
    ap.add_argument('-o', '--out')
    ap.add_argument('--steps', type=int, default=4000)
    a = ap.parse_args()
    try:
        cd = build(a.spec, a.steps)
    except NoClosure as e:
        print('%s: NO BOARD -- %s' % (a.spec, e))
        return 1
    print('%s: anchor %s h=%s R, boot at %d on %s, %d interior arms '
          '(N0=%d st=%d), %d fill arms (N0=%d st=2), quiet %s last at %d'
          % (a.spec, ST[cd['q']], SYM[cd['h']], cd['t0'], cd['ds0'],
             len(cd['inter']), cd['n0i'], cd['sti'], len(cd['fill']),
             cd['n0f'], ST[cd['qa']], cd['sq']))
    out = a.out or ('theories/Machines/Ladder/LDR_%s.v' % mach_id(a.spec))
    emit(cd, out)
    print('  -> %s' % out)
    return 0


if __name__ == '__main__':
    sys.exit(main())
