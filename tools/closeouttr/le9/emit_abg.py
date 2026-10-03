#!/usr/bin/env python3
"""UNTRUSTED emitter (SCOPING_INSTR 7.4.LE9): two binary counters at a pivot
cell, stepped in turn, each with its own words, prefix and PHASED top ->
a Coq board closed by [AbsStepTr].  The general form of [emit_ab.py].

At the pivot (state qB reading hB):

    [PLc ++ bcells ZL OL x ++ TL px | hB | PRc ++ bcells ZR OR z ++ TR pz]

A round: the right counter steps (qB hB -> qD hD, the prefixes PLc / PRc
turning PLd / PRd), then the left (back).  A side with tails T_0..T_(m-1)
tops as 1^j T_p -> 0^j T_(p+1) (p < m - 1) and 1^j T_(m-1) -> 0^(j+1) T_0;
a plain widening counter is m = 1 with T_0 its top digit.

Liveness: each instruction is read off a half of every round, or of the
next round (a carry over >= 0 ones, or over >= 1 ones, recurs within one
round).

    python3 emit_abg.py SPEC -o OUT.v
"""
import argparse
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, '..', 'le8'))
import gen2 as G2  # noqa: E402
from gen2 import NoClosure, ST, SYM, syms  # noqa: E402
from emit_step import inner_coq  # noqa: E402
from csim import parse as csim_parse  # noqa: E402

E = G2.S.E
A, B, C, D = 0, 1, 2, 3

ROWS = {
    # pivot B1 / C0, the right prefix 1 / 0; left 11110 / 10110, four tails;
    # right 00 / 11 widening
    '1RB1LC_1LA0RD_0LB0LC_1RB1RD': dict(
        qB=B, hB=1, qD=C, hD=0, PLc=(), PLd=(), PRc=(1,), PRd=(0,),
        ZL=(1, 1, 1, 1, 0), OL=(1, 0, 1, 1, 0),
        TL=((1,), (1, 0, 1), (1, 1, 0, 1, 0, 1), (1, 0, 0, 1, 0, 1)), lastL='O',
        ZR=(0, 0), OR=(1, 1), TR=((1, 1),)),
    # the same tapes, pivot B1 / D0
    '1RB1RA_1LC0RA_1RB1LD_0LB0LD': dict(
        qB=B, hB=1, qD=D, hD=0, PLc=(), PLd=(), PRc=(1,), PRd=(0,),
        ZL=(1, 1, 1, 1, 0), OL=(1, 0, 1, 1, 0),
        TL=((1,), (1, 0, 1), (1, 1, 0, 1, 0, 1), (1, 0, 0, 1, 0, 1)), lastL='O',
        ZR=(0, 0), OR=(1, 1), TR=((1, 1),)),
}


def arms_of(r):
    qB, hB, qD, hD = r['qB'], r['hB'], r['qD'], r['hD']
    PLc, PLd, PRc, PRd = r['PLc'], r['PLd'], r['PRc'], r['PRd']
    ZL, OL, ZR, OR, TL, TR = r['ZL'], r['OL'], r['ZR'], r['OR'], r['TL'], r['TR']
    X = ('X',)
    out = []
    for b, sfx in ((0, ''), (1, '_1')):
        out.append(('rc' + sfx, (qB, hB, [('c', PLc), X], [('c', PRc), ('r', OR, b), ('c', ZR), X]),
                                (qD, hD, [('c', PLd), X], [('c', PRd), ('r', ZR, b), ('c', OR), X])))
        for p, T in enumerate(TR):
            T2 = TR[p + 1] if p + 1 < len(TR) else (OR if r.get('lastR') == 'O' else ZR) + TR[0]
            out.append(('rt%d%s' % (p, sfx), (qB, hB, [('c', PLc), X], [('c', PRc), ('r', OR, b), ('c', T)]),
                                             (qD, hD, [('c', PLd), X], [('c', PRd), ('r', ZR, b), ('c', T2)])))
        out.append(('lc' + sfx, (qD, hD, [('c', PLd), ('r', OL, b), ('c', ZL), X], [('c', PRd), X]),
                                (qB, hB, [('c', PLc), ('r', ZL, b), ('c', OL), X], [('c', PRc), X])))
        for p, T in enumerate(TL):
            T2 = TL[p + 1] if p + 1 < len(TL) else (OL if r.get('lastL') == 'O' else ZL) + TL[0]
            out.append(('lt%d%s' % (p, sfx), (qD, hD, [('c', PLd), ('r', OL, b), ('c', T)], [('c', PRd), X]),
                                             (qB, hB, [('c', PLc), ('r', ZL, b), ('c', T2)], [('c', PRc), X])))
    return out


def boot(spec, r, steps=400000):
    """(t, x, px, z, pz): the first pivot visit past 2000 steps whose tape
    reads as the two counters"""
    tab = E.parse_tm(spec)
    s2 = lambda w: ''.join(map(str, w))  # noqa: E731

    def side(st, P, Z, O, Ts):
        if not st.startswith(P):
            return None
        st = st[len(P):]
        Ts = [s2(T).rstrip('0') for T in Ts]
        x = []
        while True:
            # the shortest reading: a tail as soon as the rest is one
            if st in Ts and x:
                return x, Ts.index(st)
            if len(st) >= len(Z) and st[:len(Z)] in (Z, O):
                x.append(st[:len(Z)] == O)
                st = st[len(Z):]
            else:
                return None
    PL, PR = s2(r['PLc']), s2(r['PRc'])
    ZL, OL, ZR, OR = s2(r['ZL']), s2(r['OL']), s2(r['ZR']), s2(r['OR'])
    tape, h, q = {}, 0, 0
    for t in range(steps):
        s = tape.get(h, 0)
        if q == r['qB'] and s == r['hB'] and t > 2000:
            cs = sorted(i for i, v in tape.items() if v)
            L = ''.join(str(tape.get(i, 0)) for i in range(h - 1, cs[0] - 1, -1)).rstrip('0')
            R = ''.join(str(tape.get(i, 0)) for i in range(h + 1, cs[-1] + 1)).rstrip('0')
            a = side(L, PL, ZL, OL, r['TL'])
            b = side(R, PR, ZR, OR, r['TR'])
            if a and b:
                return t, a[0], a[1], b[0], b[1]
        w, d, nq = tab[(q, s)]
        tape[h] = w
        h += d
        q = nq
    raise NoClosure('no boot')


def tails_def(name, mid, Ts):
    if len(Ts) == 1:
        return 'Definition %s_%s (p : nat) : list Sym := %s.\n' % (name, mid, syms(Ts[0]))
    cs = ' '.join('| %d => %s' % (i, syms(T)) for i, T in enumerate(Ts[:-1]))
    return 'Definition %s_%s (p : nat) : list Sym := match p with %s | _ => %s end.\n' % (
        name, mid, cs, syms(Ts[-1]))


def inc_def(name, mid, m, last='Z'):
    cs = ' '.join('| %d => (repeat false (length x), %d)' % (i, i + 1) for i in range(m - 1))
    top = '(repeat false (length x) ++ [true], 0)' if last == 'O' else '(repeat false (S (length x)), 0)'
    body = ('match p with %s | _ => %s end' % (cs, top)) if m > 1 else top
    return ('Definition %s_%s (x : list bool) (p : nat) : list bool * nat :=\n'
            '  if alltrue x then %s else (binc x, p).\n') % (name, mid, body)


COQ_HEAD = r"""
(** *** The two counters at the pivot *)
%(tLdef)s%(tRdef)s%(incLdef)s%(incRdef)s
Definition aC_%(mid)s (s : (list bool * nat) * (list bool * nat)) : cconf :=
  let '((x, px), (z, pz)) := s in
  (%(qB)s, (%(PLc)s ++ bcells %(ZL)s %(OL)s x ++ tL_%(mid)s px, %(hB)s,
       %(PRc)s ++ bcells %(ZR)s %(OR)s z ++ tR_%(mid)s pz)).
Definition aD_%(mid)s (x : list bool) (px : nat) (z : list bool) (pz : nat) : cconf :=
  (%(qD)s, (%(PLd)s ++ bcells %(ZL)s %(OL)s x ++ tL_%(mid)s px, %(hD)s,
       %(PRd)s ++ bcells %(ZR)s %(OR)s z ++ tR_%(mid)s pz)).
Definition aF_%(mid)s (s : (list bool * nat) * (list bool * nat)) : (list bool * nat) * (list bool * nat) :=
  let '((x, px), (z, pz)) := s in (incL_%(mid)s x px, incR_%(mid)s z pz).
Definition aI_%(mid)s (s : (list bool * nat) * (list bool * nat)) : Prop :=
  let '((x, px), (z, pz)) := s in 1 <= length x /\ px < %(mL)d /\ 1 <= length z /\ pz < %(mR)d.

Lemma inc_len_%(mid)s : forall (y : list bool) n, 1 <= length y -> 1 <= length (repeat false (n + length y)).
Proof. intros y n H. rewrite repeat_length. lia. Qed.

(** *** The right half: the right counter steps *)
Lemma ahRc_%(mid)s : forall x px j s pz,
  Reach1 tm (aC_%(mid)s ((x, px), (repeat true j ++ false :: s, pz)))
            (aD_%(mid)s x px (repeat false j ++ true :: s) pz).
Proof.
  intros x px j s pz. unfold aC_%(mid)s, aD_%(mid)s. rewrite bcells_tt, bcells_ff.
  change (bcells %(ZR)s %(OR)s (false :: s)) with (%(ZR)s ++ bcells %(ZR)s %(OR)s s).
  change (bcells %(ZR)s %(OR)s (true :: s)) with (%(OR)s ++ bcells %(ZR)s %(OR)s s).
  rewrite <- ?app_assoc.
  exact (%(rc)s j (bcells %(ZL)s %(OL)s x ++ tL_%(mid)s px) (bcells %(ZR)s %(OR)s s ++ tR_%(mid)s pz)).
Qed.
"""

RT_MID = r"""
Lemma ahRt%(p)d_%(mid)s : forall x px j,
  Reach1 tm (aC_%(mid)s ((x, px), (repeat true j, %(p)d))) (aD_%(mid)s x px (repeat false j) %(p1)d).
Proof.
  intros x px j. unfold aC_%(mid)s, aD_%(mid)s. cbn [tR_%(mid)s]. rewrite bcells_rep_true, bcells_rep_false.
  pose proof (%(rt)s j (bcells %(ZL)s %(OL)s x ++ tL_%(mid)s px) []) as H. rewrite ?app_nil_r in H. exact H.
Qed.
"""
RT_LAST = r"""
Lemma ahRt%(p)d_%(mid)s : forall x px j,
  Reach1 tm (aC_%(mid)s ((x, px), (repeat true j, %(p)d))) (aD_%(mid)s x px (repeat false (S j)) 0).
Proof.
  intros x px j. unfold aC_%(mid)s, aD_%(mid)s. cbn [tR_%(mid)s]. rewrite bcells_rep_true, bcells_rep_false.
  rewrite rep_S_r, <- !app_assoc.
  pose proof (%(rt)s j (bcells %(ZL)s %(OL)s x ++ tL_%(mid)s px) []) as H. rewrite ?app_nil_r in H. exact H.
Qed.
"""
LT_MID = r"""
Lemma ahLt%(p)d_%(mid)s : forall k z pz,
  Reach1 tm (aD_%(mid)s (repeat true k) %(p)d z pz) (aC_%(mid)s ((repeat false k, %(p1)d), (z, pz))).
Proof.
  intros k z pz. unfold aC_%(mid)s, aD_%(mid)s. cbn [tL_%(mid)s]. rewrite bcells_rep_true, bcells_rep_false.
  pose proof (%(lt)s k [] (bcells %(ZR)s %(OR)s z ++ tR_%(mid)s pz)) as H. rewrite ?app_nil_r in H. exact H.
Qed.
"""
LT_LAST = r"""
Lemma ahLt%(p)d_%(mid)s : forall k z pz,
  Reach1 tm (aD_%(mid)s (repeat true k) %(p)d z pz) (aC_%(mid)s ((repeat false (S k), 0), (z, pz))).
Proof.
  intros k z pz. unfold aC_%(mid)s, aD_%(mid)s. cbn [tL_%(mid)s]. rewrite bcells_rep_true, bcells_rep_false.
  rewrite rep_S_r, <- !app_assoc.
  pose proof (%(lt)s k [] (bcells %(ZR)s %(OR)s z ++ tR_%(mid)s pz)) as H. rewrite ?app_nil_r in H. exact H.
Qed.
"""

RT_LASTO = r"""
Lemma ahRt%(p)d_%(mid)s : forall x px j,
  Reach1 tm (aC_%(mid)s ((x, px), (repeat true j, %(p)d))) (aD_%(mid)s x px (repeat false j ++ [true]) 0).
Proof.
  intros x px j. unfold aC_%(mid)s, aD_%(mid)s. cbn [tR_%(mid)s]. rewrite bcells_rep_true, bcells_ff.
  change (bcells %(ZR)s %(OR)s [true]) with %(OR)s. rewrite <- ?app_assoc.
  pose proof (%(rt)s j (bcells %(ZL)s %(OL)s x ++ tL_%(mid)s px) []) as H. rewrite ?app_nil_r in H. exact H.
Qed.
"""
LT_LASTO = r"""
Lemma ahLt%(p)d_%(mid)s : forall k z pz,
  Reach1 tm (aD_%(mid)s (repeat true k) %(p)d z pz) (aC_%(mid)s ((repeat false k ++ [true], 0), (z, pz))).
Proof.
  intros k z pz. unfold aC_%(mid)s, aD_%(mid)s. cbn [tL_%(mid)s]. rewrite bcells_rep_true, bcells_ff.
  change (bcells %(ZL)s %(OL)s [true]) with %(OL)s. rewrite <- ?app_assoc.
  pose proof (%(lt)s k [] (bcells %(ZR)s %(OR)s z ++ tR_%(mid)s pz)) as H. rewrite ?app_nil_r in H. exact H.
Qed.
"""

LTOP = r"""
(** *** The left counter's tops: reached by counting, and in every phase *)
Definition nextL_%(mid)s (p : nat) : nat := %(nextbody)s.
Fixpoint nextLk_%(mid)s (k p : nat) : nat :=
  match k with 0 => p | S k' => nextLk_%(mid)s k' (nextL_%(mid)s p) end.

Lemma incL_top_%(mid)s : forall x p, alltrue x = true -> 1 <= length x -> p < %(mL)d ->
  snd (incL_%(mid)s x p) = nextL_%(mid)s p /\ alltrue (fst (incL_%(mid)s x p)) = false.
Proof.
  intros x p E Hx Hp. unfold incL_%(mid)s. rewrite E.
  destruct x as [|b x]; [cbn in Hx; lia|].
  do %(mL)d (destruct p as [|p]; [cbn [fst snd length repeat app alltrue forallb andb]; split; reflexivity|]).
  lia.
Qed.

Lemma Ltop_%(mid)s : forall v x px z pz, aI_%(mid)s ((x, px), (z, pz)) -> 2 ^ length x - bval x <= v ->
  exists n x' z' pz', fiter _ aF_%(mid)s n ((x, px), (z, pz)) = ((x', px), (z', pz')) /\
    alltrue x' = true /\ aI_%(mid)s ((x', px), (z', pz')).
Proof.
  induction v as [|v IH]; intros x px z pz Hi Hv.
  - pose proof (bval_lt x). lia.
  - destruct (alltrue x) eqn:E; [exists 0, x, z, pz; split; [reflexivity | split; assumption]|].
    destruct (binc_val x E) as [H1 H2].
    assert (Hs : aF_%(mid)s ((x, px), (z, pz)) = ((binc x, px), (fst (incR_%(mid)s z pz), snd (incR_%(mid)s z pz))))
      by (unfold aF_%(mid)s, incL_%(mid)s; rewrite E, <- surjective_pairing; reflexivity).
    pose proof (aHI_%(mid)s _ Hi) as Hi'. rewrite Hs in Hi'.
    destruct (IH (binc x) px _ _ Hi') as (n & x' & z' & pz' & Hn & Ht & Hi2).
    { rewrite H1, H2. pose proof (bval_lt x). lia. }
    exists (S n), x', z', pz'. split; [cbn [fiter]; rewrite Hs; exact Hn | split; assumption].
Qed.

Lemma Lnext_%(mid)s : forall x px z pz, aI_%(mid)s ((x, px), (z, pz)) -> alltrue x = true ->
  exists n x' z' pz', fiter _ aF_%(mid)s n ((x, px), (z, pz)) = ((x', nextL_%(mid)s px), (z', pz')) /\
    alltrue x' = true /\ aI_%(mid)s ((x', nextL_%(mid)s px), (z', pz')).
Proof.
  intros x px z pz Hi E. pose proof Hi as (Hx & Hpx & _ & _).
  destruct (incL_top_%(mid)s x px E Hx Hpx) as [Hp _].
  assert (Hs : aF_%(mid)s ((x, px), (z, pz)) =
                 ((fst (incL_%(mid)s x px), nextL_%(mid)s px), (fst (incR_%(mid)s z pz), snd (incR_%(mid)s z pz))))
    by (unfold aF_%(mid)s; rewrite <- Hp, <- !surjective_pairing; reflexivity).
  pose proof (aHI_%(mid)s _ Hi) as Hi'. rewrite Hs in Hi'.
  destruct (Ltop_%(mid)s _ _ _ _ _ Hi' (le_n _)) as (n & x' & z' & pz' & Hn & Ht & Hi2).
  exists (S n), x', z', pz'. split; [cbn [fiter]; rewrite Hs; exact Hn | split; assumption].
Qed.

Lemma Literk_%(mid)s : forall k x px z pz, aI_%(mid)s ((x, px), (z, pz)) -> alltrue x = true ->
  exists n x' z' pz', fiter _ aF_%(mid)s n ((x, px), (z, pz)) = ((x', nextLk_%(mid)s k px), (z', pz')) /\
    alltrue x' = true /\ aI_%(mid)s ((x', nextLk_%(mid)s k px), (z', pz')).
Proof.
  induction k as [|k IH]; intros x px z pz Hi E.
  - exists 0, x, z, pz. split; [reflexivity | split; assumption].
  - destruct (Lnext_%(mid)s x px z pz Hi E) as (n1 & x1 & z1 & pz1 & H1 & E1 & Hi1).
    destruct (IH x1 _ z1 pz1 Hi1 E1) as (n2 & x2 & z2 & pz2 & H2 & E2 & Hi2).
    exists (n1 + n2), x2, z2, pz2. rewrite fiter_add, H1. split; [exact H2 | split; assumption].
Qed.

(** fired by the left half at the left counter's top in phase %(g)d *)
Lemma afLT_%(mid)s : forall t,
  (forall k z pz, Fires tm (aD_%(mid)s (repeat true k) %(g)d z pz) t) ->
  forall s, aI_%(mid)s s -> exists n, Fires tm (aC_%(mid)s (fiter _ aF_%(mid)s n s)) t.
Proof.
  intros t H [[x px] [z pz]] Hi.
  destruct (Ltop_%(mid)s _ x px z pz Hi (le_n _)) as (n1 & x1 & z1 & pz1 & H1 & E1 & Hi1).
  assert (Hk : exists k, nextLk_%(mid)s k px = %(g)d).
  { pose proof Hi as (_ & Hpx & _ & _).
%(kcases)s
    lia. }
  destruct Hk as (k & Hk).
  destruct (Literk_%(mid)s k x1 px z1 pz1 Hi1 E1) as (n2 & x2 & z2 & pz2 & H2 & E2 & Hi2).
  rewrite Hk in H2, Hi2.
  exists (n1 + n2). rewrite fiter_add, H1, H2.
  pose proof Hi2 as (_ & _ & _ & Hpz2).
  apply (fire_back tm _ (aD_%(mid)s x2 %(g)d (fst (incR_%(mid)s z2 pz2)) (snd (incR_%(mid)s z2 pz2)))).
  { apply reach1_0, ahR_%(mid)s, Hpz2. }
  rewrite (alltrue_eq x2 E2). apply H.
Qed.
"""

COQ_BODY = r"""
Lemma ahR_%(mid)s : forall x px z pz, pz < %(mR)d ->
  Reach1 tm (aC_%(mid)s ((x, px), (z, pz))) (aD_%(mid)s x px (fst (incR_%(mid)s z pz)) (snd (incR_%(mid)s z pz))).
Proof.
  intros x px z pz Hp. unfold incR_%(mid)s.
  destruct (alltrue z) eqn:E.
  - assert (Hz : exists j, z = repeat true j) by (exists (length z); apply alltrue_eq, E).
    destruct Hz as (j & ->). rewrite repeat_length.
%(rcases)s
  - destruct (ttdecomp z) as [(j & s & ->) | (j & ->)].
    2:{ rewrite alltrue_repeat in E. discriminate. }
    cbn [fst snd]. rewrite binc_int. apply ahRc_%(mid)s.
Qed.

(** *** The left half: the left counter steps *)
Lemma ahLc_%(mid)s : forall k r px z pz,
  Reach1 tm (aD_%(mid)s (repeat true k ++ false :: r) px z pz)
            (aC_%(mid)s ((repeat false k ++ true :: r, px), (z, pz))).
Proof.
  intros k r px z pz. unfold aC_%(mid)s, aD_%(mid)s. rewrite bcells_tt, bcells_ff.
  change (bcells %(ZL)s %(OL)s (false :: r)) with (%(ZL)s ++ bcells %(ZL)s %(OL)s r).
  change (bcells %(ZL)s %(OL)s (true :: r)) with (%(OL)s ++ bcells %(ZL)s %(OL)s r).
  rewrite <- ?app_assoc.
  exact (%(lc)s k (bcells %(ZL)s %(OL)s r ++ tL_%(mid)s px) (bcells %(ZR)s %(OR)s z ++ tR_%(mid)s pz)).
Qed.
%(ltlemmas)s
Lemma ahL_%(mid)s : forall x px z pz, px < %(mL)d ->
  Reach1 tm (aD_%(mid)s x px z pz) (aC_%(mid)s (incL_%(mid)s x px, (z, pz))).
Proof.
  intros x px z pz Hp. unfold incL_%(mid)s.
  destruct (alltrue x) eqn:E.
  - assert (Hx : exists k, x = repeat true k) by (exists (length x); apply alltrue_eq, E).
    destruct Hx as (k & ->). rewrite repeat_length.
%(lcases)s
  - destruct (ttdecomp x) as [(k & r & ->) | (k & ->)].
    2:{ rewrite alltrue_repeat in E. discriminate. }
    rewrite binc_int. apply ahLc_%(mid)s.
Qed.

Lemma inc_inv_%(mid)s : forall (y : list bool) p m, 1 <= length y -> p < m ->
  (m = %(mL)d \/ m = %(mR)d) ->
  forall f : list bool -> nat -> list bool * nat,
  (f = incL_%(mid)s /\ m = %(mL)d \/ f = incR_%(mid)s /\ m = %(mR)d) ->
  1 <= length (fst (f y p)) /\ snd (f y p) < m.
Proof.
  intros y p m Hy Hp _ f Hf.
  destruct Hf as [(-> & ->) | (-> & ->)]; [unfold incL_%(mid)s | unfold incR_%(mid)s];
    (destruct (alltrue y) eqn:E;
     [ do %(mmax)d (destruct p as [|p]; [cbn [fst snd]; rewrite ?app_length, ?repeat_length; cbn; split; lia|]);
       cbn [fst snd]; rewrite ?app_length, ?repeat_length; cbn; split; lia
     | cbn [fst snd]; destruct (binc_val y E) as [_ H2]; rewrite H2; split; assumption ]).
Qed.

Lemma aHI_%(mid)s : forall s, aI_%(mid)s s -> aI_%(mid)s (aF_%(mid)s s).
Proof.
  intros [[x px] [z pz]] (Hx & Hpx & Hz & Hpz). unfold aF_%(mid)s.
  destruct (inc_inv_%(mid)s x px %(mL)d Hx Hpx (or_introl eq_refl) incL_%(mid)s (or_introl (conj eq_refl eq_refl)))
    as [H1 H2].
  destruct (inc_inv_%(mid)s z pz %(mR)d Hz Hpz (or_intror eq_refl) incR_%(mid)s (or_intror (conj eq_refl eq_refl)))
    as [H3 H4].
  destruct (incL_%(mid)s x px) as [x' px']. destruct (incR_%(mid)s z pz) as [z' pz'].
  cbn in *. repeat split; assumption.
Qed.

Lemma aHstep_%(mid)s : forall s, aI_%(mid)s s -> Reach1 tm (aC_%(mid)s s) (aC_%(mid)s (aF_%(mid)s s)).
Proof.
  intros [[x px] [z pz]] (Hx & Hpx & Hz & Hpz). unfold aF_%(mid)s.
  apply (reach10 tm _ (aD_%(mid)s x px (fst (incR_%(mid)s z pz)) (snd (incR_%(mid)s z pz)))).
  - apply ahR_%(mid)s, Hpz.
  - apply reach1_0. rewrite (surjective_pairing (incR_%(mid)s z pz)). apply ahL_%(mid)s, Hpx.
Qed.

(** *** Where each instruction fires *)
(** the right half of this round *)
Lemma afR_%(mid)s : forall t,
  (forall x px j s pz, Fires tm (aC_%(mid)s ((x, px), (repeat true j ++ false :: s, pz))) t) ->
  (forall x px j pz, pz < %(mR)d -> Fires tm (aC_%(mid)s ((x, px), (repeat true j, pz))) t) ->
  forall s, aI_%(mid)s s -> Fires tm (aC_%(mid)s s) t.
Proof.
  intros t Hc Ht [[x px] [z pz]] (_ & _ & _ & Hp).
  destruct (ttdecomp z) as [(j & s & ->) | (j & ->)]; [apply Hc | apply Ht, Hp].
Qed.

(** the left half of this round *)
Lemma afL_%(mid)s : forall t,
  (forall k r px z pz, Fires tm (aD_%(mid)s (repeat true k ++ false :: r) px z pz) t) ->
  (forall k px z pz, px < %(mL)d -> Fires tm (aD_%(mid)s (repeat true k) px z pz) t) ->
  forall s, aI_%(mid)s s -> Fires tm (aC_%(mid)s s) t.
Proof.
  intros t Hc Ht [[x px] [z pz]] (_ & Hpx & _ & Hpz).
  apply (fire_back tm _ (aD_%(mid)s x px (fst (incR_%(mid)s z pz)) (snd (incR_%(mid)s z pz)))).
  { apply reach1_0, ahR_%(mid)s, Hpz. }
  destruct (ttdecomp x) as [(k & r & ->) | (k & ->)]; [apply Hc | apply Ht, Hpx].
Qed.

(** after a top the counter reads 0^(j+1)..., so a carry is at most a round away *)
Lemma top_next_%(mid)s : forall y p m (f : list bool -> nat -> list bool * nat),
  (f = incL_%(mid)s /\ m = %(mL)d \/ f = incR_%(mid)s /\ m = %(mR)d) ->
  1 <= length y -> p < m -> alltrue y = true ->
  exists r, fst (f y p) = false :: r.
Proof.
  intros y p m f Hf Hy Hp E.
  destruct Hf as [(-> & ->) | (-> & ->)]; [unfold incL_%(mid)s | unfold incR_%(mid)s]; rewrite E;
    (destruct y as [|b y]; [cbn in Hy; lia|]);
    (do %(mmax)d (destruct p as [|p]; [cbn [fst snd length repeat app]; eexists; reflexivity|]);
     cbn [fst snd length repeat app]; eexists; reflexivity).
Qed.

(** a carry of the right counter: this round or the next *)
Lemma afRc_%(mid)s : forall t,
  (forall x px j s pz, Fires tm (aC_%(mid)s ((x, px), (repeat true j ++ false :: s, pz))) t) ->
  forall s, aI_%(mid)s s -> exists n, Fires tm (aC_%(mid)s (fiter _ aF_%(mid)s n s)) t.
Proof.
  intros t Hc [[x px] [z pz]] (Hx & Hpx & Hz & Hpz).
  destruct (alltrue z) eqn:E.
  - exists 1. cbn [fiter]. unfold aF_%(mid)s.
    destruct (top_next_%(mid)s z pz %(mR)d incR_%(mid)s (or_intror (conj eq_refl eq_refl)) Hz Hpz E) as (r & Hr).
    rewrite (surjective_pairing (incR_%(mid)s z pz)), (surjective_pairing (incL_%(mid)s x px)), Hr.
    exact (Hc _ _ 0 r _).
  - exists 0. destruct (ttdecomp z) as [(j & s & ->) | (j & ->)]; [apply Hc|].
    rewrite alltrue_repeat in E. discriminate.
Qed.

(** a carry of the left counter: this round or the next *)
Lemma afLc_%(mid)s : forall t,
  (forall k r px z pz, Fires tm (aD_%(mid)s (repeat true k ++ false :: r) px z pz) t) ->
  forall s, aI_%(mid)s s -> exists n, Fires tm (aC_%(mid)s (fiter _ aF_%(mid)s n s)) t.
Proof.
  intros t Hc [[x px] [z pz]] (Hx & Hpx & Hz & Hpz).
  assert (Hback : forall x' px' z' pz', pz' < %(mR)d -> (exists r, x' = false :: r) ->
            Fires tm (aC_%(mid)s ((x', px'), (z', pz'))) t).
  { intros x' px' z' pz' Hp' (r & ->).
    apply (fire_back tm _ (aD_%(mid)s (false :: r) px' (fst (incR_%(mid)s z' pz')) (snd (incR_%(mid)s z' pz')))).
    { apply reach1_0, ahR_%(mid)s, Hp'. }
    exact (Hc 0 r _ _ _). }
  destruct (alltrue x) eqn:E.
  - exists 1. cbn [fiter]. unfold aF_%(mid)s.
    pose proof (aHI_%(mid)s ((x, px), (z, pz)) (conj Hx (conj Hpx (conj Hz Hpz)))) as HI.
    unfold aF_%(mid)s in HI.
    destruct (top_next_%(mid)s x px %(mL)d incL_%(mid)s (or_introl (conj eq_refl eq_refl)) Hx Hpx E) as (r & Hr).
    rewrite (surjective_pairing (incR_%(mid)s z pz)), (surjective_pairing (incL_%(mid)s x px)) in HI |- *.
    apply Hback; [apply HI | exists r; exact Hr].
  - exists 0. destruct (ttdecomp x) as [(k & r & ->) | (k & ->)].
    2:{ rewrite alltrue_repeat in E. discriminate. }
    apply (fire_back tm _ (aD_%(mid)s (repeat true k ++ false :: r) px (fst (incR_%(mid)s z pz)) (snd (incR_%(mid)s z pz)))).
    { apply reach1_0, ahR_%(mid)s, Hpz. }
    apply Hc.
Qed.

%(ltop)s
Lemma aHfire_%(mid)s : forall t, ~ In t pins_%(mid)s -> forall s, aI_%(mid)s s ->
  exists n, Fires tm (aC_%(mid)s (fiter _ aF_%(mid)s n s)) t.
Proof.
  intros t Hnp st Hs.
  destruct t as [q h]; destruct q, h; try (exfalso; apply Hnp; simpl; tauto).
%(firecases)s
Qed.
"""

H_RC = """intros x px j s pz. unfold aC_%(mid)s. rewrite bcells_tt.
      change (bcells %(ZR)s %(OR)s (false :: s)) with (%(ZR)s ++ bcells %(ZR)s %(OR)s s).
      rewrite <- ?app_assoc. exact (%(f)s j (bcells %(ZL)s %(OL)s x ++ tL_%(mid)s px) (bcells %(ZR)s %(OR)s s ++ tR_%(mid)s pz))."""
H_LC = """intros k r px z pz. unfold aD_%(mid)s. rewrite bcells_tt.
      change (bcells %(ZL)s %(OL)s (false :: r)) with (%(ZL)s ++ bcells %(ZL)s %(OL)s r).
      rewrite <- ?app_assoc. exact (%(f)s k (bcells %(ZL)s %(OL)s r ++ tL_%(mid)s px) (bcells %(ZR)s %(OR)s z ++ tR_%(mid)s pz))."""
H_RT_CASE = """destruct pz as [|pz]; [unfold aC_%(mid)s; cbn [tR_%(mid)s]; rewrite bcells_rep_true;
        pose proof (%(f)s j (bcells %(ZL)s %(OL)s x ++ tL_%(mid)s px) []) as H; rewrite ?app_nil_r in H; exact H|]."""
H_LT_CASE = """destruct px as [|px]; [unfold aD_%(mid)s; cbn [tL_%(mid)s]; rewrite bcells_rep_true;
        pose proof (%(f)s k [] (bcells %(ZR)s %(OR)s z ++ tR_%(mid)s pz)) as H; rewrite ?app_nil_r in H; exact H|]."""


def emit_closure_abg(cert, tab, mid):
    r = cert['row']
    ctab = {k: (None if k in E.TR_PINS else v) for k, v in csim_parse(cert['spec']).items()}
    g = G2.Gen2(tab, mid, E.TR_PINS, ctab)
    names, fires = {}, {}
    try:
        for key, a, b in arms_of(r):
            names[key] = g.arm(a, b, key)
    except NoClosure as e:
        return E.CLOSURE_NONE % e, None
    for key in names:
        fires[key] = g.fires(names[key])
    mL, mR = len(r['TL']), len(r['TR'])
    P = dict(mid=mid, qB=ST[r['qB']], hB=SYM[r['hB']], qD=ST[r['qD']], hD=SYM[r['hD']],
             PLc=syms(r['PLc']), PLd=syms(r['PLd']), PRc=syms(r['PRc']), PRd=syms(r['PRd']),
             ZL=syms(r['ZL']), OL=syms(r['OL']), ZR=syms(r['ZR']), OR=syms(r['OR']),
             mL=mL, mR=mR, mmax=max(mL, mR), rc=names['rc'], lc=names['lc'])
    P['tLdef'] = tails_def('tL', mid, r['TL'])
    P['tRdef'] = tails_def('tR', mid, r['TR'])
    P['incLdef'] = inc_def('incL', mid, mL, r.get('lastL', 'Z'))
    P['incRdef'] = inc_def('incR', mid, mR, r.get('lastR', 'Z'))
    head = COQ_HEAD % P
    for p in range(mR):
        T = RT_MID if p + 1 < mR else (RT_LASTO if r.get('lastR') == 'O' else RT_LAST)
        head += T % dict(P, p=p, p1=p + 1, rt=names['rt%d' % p])
    lts = ''
    for p in range(mL):
        T = LT_MID if p + 1 < mL else (LT_LASTO if r.get('lastL') == 'O' else LT_LAST)
        lts += T % dict(P, p=p, p1=p + 1, lt=names['lt%d' % p])
    rcases = ''.join('    destruct pz as [|pz]; [apply ahRt%d_%s|].\n' % (p, mid) for p in range(mR)) + '    lia.'
    lcases = ''.join('    destruct px as [|px]; [apply ahLt%d_%s|].\n' % (p, mid) for p in range(mL)) + '    lia.'
    cases = []
    need_ltop = []
    for w in g.want:
        inn = lambda *ks: all(w in fires[k] for k in ks)  # noqa: E731
        f = lambda k: fires[k][w]  # noqa: E731
        rts = ['rt%d' % p for p in range(mR)]
        lts_ = ['lt%d' % p for p in range(mL)]
        if inn('rc', *rts):
            c = ('  - exists 0. apply afR_%(mid)s; [| |exact Hs].\n    + ' + H_RC % dict(P, f=f('rc'))
                 + '\n    + intros x px j pz Hp.\n      '
                 + '\n      '.join(H_RT_CASE % dict(P, f=f(k)) for k in rts) + '\n      lia.') % P
        elif inn('lc', *lts_):
            c = ('  - exists 0. apply afL_%(mid)s; [| |exact Hs].\n    + ' + H_LC % dict(P, f=f('lc'))
                 + '\n    + intros k px z pz Hp.\n      '
                 + '\n      '.join(H_LT_CASE % dict(P, f=f(k)) for k in lts_) + '\n      lia.') % P
        elif inn('rc'):
            c = ('  - apply afRc_%(mid)s; [|exact Hs].\n    ' + H_RC % dict(P, f=f('rc'))) % P
        elif inn('lc'):
            c = ('  - apply afLc_%(mid)s; [|exact Hs].\n    ' + H_LC % dict(P, f=f('lc'))) % P
        elif any(inn('lt%d' % p) for p in range(mL)):
            gp = [p for p in range(mL) if inn('lt%d' % p)][0]
            need_ltop.append(gp)
            if len(set(need_ltop)) > 1:
                return E.CLOSURE_NONE % NoClosure('two top phases needed'), None
            c = ('  - apply afLT_%(mid)s; [|exact Hs].\n'
                 '    intros k z pz. unfold aD_%(mid)s. cbn [tL_%(mid)s]. rewrite bcells_rep_true.\n'
                 '    pose proof (%(f)s k [] (bcells %(ZR)s %(OR)s z ++ tR_%(mid)s pz)) as H.'
                 ' rewrite ?app_nil_r in H. exact H.') % dict(P, f=f('lt%d' % gp))
        else:
            return E.CLOSURE_NONE % NoClosure('no fire strategy for %s%d' % ('ABCD'[w[0]], w[1])), None
        cases.append(c)
    ltop = ''
    if need_ltop:
        gp = need_ltop[0]
        nb = ('match p with %s | _ => 0 end' % ' '.join('| %d => %d' % (i, i + 1) for i in range(mL - 1))
              if mL > 1 else '0')
        kc = ''.join('    destruct Hpx as [|px' + str(i) + ' Hpx]; [exists %d; reflexivity|].\n' % ((gp - (mL - 1 - i)) % mL)
                     for i in range(0))  # placeholder, replaced below
        kc = '\n'.join('    destruct px as [|px]; [exists %d; reflexivity|].' % ((gp - p) % mL) for p in range(mL))
        ltop = LTOP % dict(P, g=gp, nextbody=nb, kcases=kc)
    body = head + COQ_BODY % dict(P, rcases=rcases, lcases=lcases, ltlemmas=lts, ltop=ltop,
                                  firecases='\n'.join(cases))
    t0, x0, px0, z0, pz0 = cert['boot']
    bl = lambda v: '[' + ';'.join('true' if b else 'false' for b in v) + ']'  # noqa: E731
    s0 = '((%s, %d), (%s, %d))' % (bl(x0), px0, bl(z0), pz0)
    body += """
Lemma aboot_%(mid)s :
  stepn tm %(t0)d InitES = Some (lift (aC_%(mid)s %(s0)s)).
Proof.
  assert (H : match csteps tm %(t0)d c0 with
              | Some c => ceqb c (aC_%(mid)s %(s0)s)
              | None => false end = true) by (vm_compute; reflexivity).
  destruct (csteps tm %(t0)d c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** The machine-level theorem, at the INSTRUCTION level, through
    [AbsStepTr.absstep_neverqhtr]. *)
Theorem nqhtr_%(mid)s : NeverQuasiHaltsTr tm_%(mid)s.
Proof.
  exact (absstep_neverqhtr tm_%(mid)s pins_%(mid)s _ aC_%(mid)s aF_%(mid)s aI_%(mid)s
           aHI_%(mid)s aHstep_%(mid)s aHfire_%(mid)s %(s0)s
           ltac:(cbn; repeat split; lia) %(t0)d aboot_%(mid)s).
Qed.
""" % dict(mid=mid, t0=t0, s0=s0)
    hd = """
(** ** The closure: two counters at a pivot, stepped in turn, phased tops
    ([AbsStepTr], [TwoSideArmTr]) *)
From BBB4.Checkers Require Import LadderNest LadderCheckNestTr.
From BBB4.Counters Require Import NestCountTr PhBinCountTr TwoSideArmTr AbsStepTr.

"""
    return hd + inner_coq(mid, g.inner) + ''.join(g.out) + body, dict(nest=True)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('spec')
    ap.add_argument('-o', '--out', required=True)
    a = ap.parse_args()
    spec = a.spec
    r = ROWS[spec]
    E.TR_PINS = E.unfired(spec, 10 ** 6)
    bt = boot(spec, r)
    cert = dict(spec=spec, closed=True, ladder=[], arms=[], row=r, boot=bt,
                family=dict(state='ABCD'[r['qB']], head=r['hB'], side='R', other_side_cells=[],
                            digits=[list(r['ZR']), list(r['OR'])], near_head_prefix=[], terminator=[],
                            terminators_by_phase=[[]], n_phases=1, base=2, digit_len=2,
                            code='binary', value_step_per_anchor_visit=1),
                fill=dict(widens_by=1, target_prefix=[], target_fill_digit=0, target_suffix=[],
                          lands_in_phase=0))
    E.emit_closure = emit_closure_abg
    good, bad, cd = E.emit(cert, a.out)
    print('%s: closure %s' % (a.out, 'BUILT' if cd else 'not built'))
    return 0 if cd else 1


if __name__ == '__main__':
    sys.exit(main())
