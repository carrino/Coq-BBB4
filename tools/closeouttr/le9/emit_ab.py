#!/usr/bin/env python3
"""UNTRUSTED emitter (SCOPING_INSTR 7.4.LE9): LE7's OUT-OF-STEP mirrors, two
binary counters one each side of a pivot cell, incremented in turn -> a Coq
board closed by [AbsStepTr].

At the pivot, in state qB reading hB, the tape is

    [cells_L x | hB | cells_R z ++ T p]

x over ZL / OL (its top digit is the left end), z over ZR / OR, T p the
right end in phase p (0 or 1).  A round is two halves through the pivot:
the right counter steps (qB hB -> qD hD), then the left (qD hD -> qB hB).
The right counter's top is two-phase: 1^j T0 -> 0^j T1 -> (one round) ...
1^j T1 -> 0^(j+1) T0; the left's top widens, 1^k -> 0^k 1.  The two
counters are NOT the same number (LE7's "out of step at every anchor"), so
the abstract state is the pair (x, z) and the phase.

Each half is one arm family ([TwoSideArmTr], the other side an opaque tail);
the liveness reads each instruction off the halves of every round, or of the
round after (the right top at phase 1, or a right counter ending in 0).

    python3 emit_ab.py SPEC -o OUT.v
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
    # pivot B0 / D1; left 00 / 01 (top digit 01 is the left end); right 00 / 11,
    # right end 1 (phase 0) or 011 (phase 1)
    '1RB1LD_1RC0RB_1RD1RC_1LA0LD': dict(qB=B, hB=0, qD=D, hD=1, ZL=(0, 0), OL=(0, 1),
                                        ZR=(0, 0), OR=(1, 1), T0=(1,), T1=(0, 1, 1)),
    # pivot D0 / B1; both counters' tops widen them (no right end)
    '1RB1RA_1LC0LB_1RD1LB_1RA0RD': dict(qB=D, hB=0, qD=B, hD=1, ZL=(0, 0), OL=(0, 1),
                                        ZR=(0, 0), OR=(1, 1), T0=(), T1=(), rwiden=True),
}


def arms_of(r):
    qB, hB, qD, hD = r['qB'], r['hB'], r['qD'], r['hD']
    ZL, OL, ZR, OR, T0, T1 = r['ZL'], r['OL'], r['ZR'], r['OR'], r['T0'], r['T1']
    X = ('X',)
    out = []
    for b, sfx in ((0, ''), (1, '1')):
        out += [
            ('rc' + sfx, (qB, hB, [X], [('r', OR, b), ('c', ZR), X]),
                         (qD, hD, [X], [('r', ZR, b), ('c', OR), X]))]
        if r.get('rwiden'):
            out += [
                ('rt' + sfx, (qB, hB, [X], [('r', OR, b)]),
                             (qD, hD, [X], [('r', ZR, b), ('c', OR)]))]
        else:
            out += [
                ('rt0' + sfx, (qB, hB, [X], [('r', OR, b), ('c', T0)]),
                              (qD, hD, [X], [('r', ZR, b), ('c', T1)])),
                ('rt1' + sfx, (qB, hB, [X], [('r', OR, b), ('c', T1)]),
                              (qD, hD, [X], [('r', ZR, b), ('c', ZR + T0)]))]
        out += [
            ('lc' + sfx, (qD, hD, [('r', OL, b), ('c', ZL), X], [X]),
                         (qB, hB, [('r', ZL, b), ('c', OL), X], [X])),
            ('lt' + sfx, (qD, hD, [('r', OL, b)], [X]),
                         (qB, hB, [('r', ZL, b), ('c', OL)], [X])),
        ]
    return out


def boot(spec, r, steps=400000):
    """(t, x, z, p): the first pivot visit past 2000 steps whose tape reads as
    the two counters"""
    tab = E.parse_tm(spec)
    s2 = lambda w: ''.join(map(str, w))  # noqa: E731
    ZL, OL, ZR, OR = s2(r['ZL']), s2(r['OL']), s2(r['ZR']), s2(r['OR'])
    T0, T1 = s2(r['T0']), s2(r['T1'])

    def rd(st, Z, O):
        x = []
        while len(st) >= len(Z) and st[:len(Z)] in (Z, O):
            x.append(st[:len(Z)] == O)
            st = st[len(Z):]
        return x, st
    tape, h, q = {}, 0, 0
    for t in range(steps):
        s = tape.get(h, 0)
        if q == r['qB'] and s == r['hB'] and t > 2000:
            cs = sorted(i for i, v in tape.items() if v)
            L = ''.join(str(tape.get(i, 0)) for i in range(h - 1, cs[0] - 1, -1)).rstrip('0')
            R = ''.join(str(tape.get(i, 0)) for i in range(h + 1, cs[-1] + 1)).rstrip('0')
            x, tl = rd(L, ZL, OL)
            z, tr = rd(R, ZR, OR)
            if not tl and x and x[-1] and z and tr in (T0, T1):
                return t, x, z, (0 if tr == T0 else 1)
        w, d, nq = tab[(q, s)]
        tape[h] = w
        h += d
        q = nq
    raise NoClosure('no boot')


COQ = r"""
(** *** The two counters at the pivot *)
%(aTdef)s
Definition aC_%(mid)s (s : list bool * list bool * nat) : cconf :=
  let '(x, z, p) := s in
  (%(qB)s, (bcells %(ZL)s %(OL)s x, %(hB)s, bcells %(ZR)s %(OR)s z ++ aT_%(mid)s p)).
Definition aD_%(mid)s (x z : list bool) (p : nat) : cconf :=
  (%(qD)s, (bcells %(ZL)s %(OL)s x, %(hD)s, bcells %(ZR)s %(OR)s z ++ aT_%(mid)s p)).

%(rincdef)sDefinition xinc_%(mid)s (x : list bool) : list bool :=
  if alltrue x then repeat false (length x) ++ [true] else binc x.
Definition aF_%(mid)s (s : list bool * list bool * nat) : list bool * list bool * nat :=
  let '(x, z, p) := s in (xinc_%(mid)s x, fst (rinc_%(mid)s z p), snd (rinc_%(mid)s z p)).
Definition aI_%(mid)s (s : list bool * list bool * nat) : Prop :=
  let '(x, z, p) := s in 1 <= length z /\ p <= 1.

(** *** The right half: the right counter steps *)
Lemma ahRc_%(mid)s : forall x j s p,
  Reach1 tm (aC_%(mid)s (x, repeat true j ++ false :: s, p))
            (aD_%(mid)s x (repeat false j ++ true :: s) p).
Proof.
  intros x j s p. unfold aC_%(mid)s, aD_%(mid)s. rewrite bcells_tt, bcells_ff.
  change (bcells %(ZR)s %(OR)s (false :: s)) with (%(ZR)s ++ bcells %(ZR)s %(OR)s s).
  change (bcells %(ZR)s %(OR)s (true :: s)) with (%(OR)s ++ bcells %(ZR)s %(OR)s s).
  rewrite <- ?app_assoc.
  exact (%(rc)s j (bcells %(ZL)s %(OL)s x) (bcells %(ZR)s %(OR)s s ++ aT_%(mid)s p)).
Qed.

%(rtop)s
(** *** The left half: the left counter steps *)
Lemma ahLc_%(mid)s : forall k r z p,
  Reach1 tm (aD_%(mid)s (repeat true k ++ false :: r) z p)
            (aC_%(mid)s (repeat false k ++ true :: r, z, p)).
Proof.
  intros k r z p. unfold aC_%(mid)s, aD_%(mid)s. rewrite bcells_tt, bcells_ff.
  change (bcells %(ZL)s %(OL)s (false :: r)) with (%(ZL)s ++ bcells %(ZL)s %(OL)s r).
  change (bcells %(ZL)s %(OL)s (true :: r)) with (%(OL)s ++ bcells %(ZL)s %(OL)s r).
  rewrite <- ?app_assoc.
  exact (%(lc)s k (bcells %(ZL)s %(OL)s r) (bcells %(ZR)s %(OR)s z ++ aT_%(mid)s p)).
Qed.

Lemma ahLt_%(mid)s : forall k z p,
  Reach1 tm (aD_%(mid)s (repeat true k) z p) (aC_%(mid)s (repeat false k ++ [true], z, p)).
Proof.
  intros k z p. unfold aC_%(mid)s, aD_%(mid)s. rewrite bcells_rep_true, bcells_ff.
  change (bcells %(ZL)s %(OL)s [true]) with (%(OL)s ++ []).
  pose proof (%(lt)s k [] (bcells %(ZR)s %(OR)s z ++ aT_%(mid)s p)) as H.
  rewrite ?app_nil_r in H. rewrite ?app_nil_r. exact H.
Qed.

Lemma ahL_%(mid)s : forall x z p,
  Reach1 tm (aD_%(mid)s x z p) (aC_%(mid)s (xinc_%(mid)s x, z, p)).
Proof.
  intros x z p. unfold xinc_%(mid)s.
  destruct (alltrue x) eqn:E.
  - assert (Hx : exists k, x = repeat true k) by (exists (length x); apply alltrue_eq, E).
    destruct Hx as (k & ->). rewrite repeat_length. apply ahLt_%(mid)s.
  - destruct (ttdecomp x) as [(k & r & ->) | (k & ->)].
    2:{ rewrite alltrue_repeat in E. discriminate. }
    rewrite binc_int. apply ahLc_%(mid)s.
Qed.

%(hidef)s
Lemma aHstep_%(mid)s : forall s, aI_%(mid)s s -> Reach1 tm (aC_%(mid)s s) (aC_%(mid)s (aF_%(mid)s s)).
Proof.
  intros [[x z] p] [Hz Hp]. unfold aF_%(mid)s.
  apply (reach10 tm _ (aD_%(mid)s x (fst (rinc_%(mid)s z p)) (snd (rinc_%(mid)s z p)))).
  - apply ahR_%(mid)s, Hp.
  - apply reach1_0, ahL_%(mid)s.
Qed.

(** *** Where each instruction fires *)
%(afr)s
Lemma afL_%(mid)s : forall t,
  (forall k r z p, Fires tm (aD_%(mid)s (repeat true k ++ false :: r) z p) t) ->
  (forall k z p, Fires tm (aD_%(mid)s (repeat true k) z p) t) ->
  forall s, aI_%(mid)s s -> Fires tm (aC_%(mid)s s) t.
Proof.
  intros t Hc Ht [[x z] p] [Hz Hp].
  apply (fire_back tm _ (aD_%(mid)s x (fst (rinc_%(mid)s z p)) (snd (rinc_%(mid)s z p)))).
  { apply reach1_0, ahR_%(mid)s, Hp. }
  destruct (ttdecomp x) as [(k & r & ->) | (k & ->)]; [apply Hc | apply Ht].
Qed.

%(afrest)s
Lemma aHfire_%(mid)s : forall t, ~ In t pins_%(mid)s -> forall s, aI_%(mid)s s ->
  exists n, Fires tm (aC_%(mid)s (fiter _ aF_%(mid)s n s)) t.
Proof.
  intros t Hnp st Hs.
  destruct t as [q h]; destruct q, h; try (exfalso; apply Hnp; simpl; tauto).
%(firecases)s
Qed.
"""

PH = dict(
    aTdef="""Definition aT_%(mid)s (p : nat) : list Sym := match p with 0 => %(T0)s | _ => %(T1)s end.
""",
    rincdef="""Definition rinc_%(mid)s (z : list bool) (p : nat) : list bool * nat :=
  if alltrue z then
    match p with 0 => (repeat false (length z), 1) | _ => (repeat false (S (length z)), 0) end
  else (binc z, p).
""",
    rtop="""Lemma ahRt0_%(mid)s : forall x j,
  Reach1 tm (aC_%(mid)s (x, repeat true j, 0)) (aD_%(mid)s x (repeat false j) 1).
Proof.
  intros x j. unfold aC_%(mid)s, aD_%(mid)s, aT_%(mid)s. rewrite bcells_rep_true, bcells_rep_false.
  pose proof (%(rt0)s j (bcells %(ZL)s %(OL)s x) []) as H. rewrite ?app_nil_r in H. exact H.
Qed.

Lemma ahRt1_%(mid)s : forall x j,
  Reach1 tm (aC_%(mid)s (x, repeat true j, 1)) (aD_%(mid)s x (repeat false (S j)) 0).
Proof.
  intros x j. unfold aC_%(mid)s, aD_%(mid)s, aT_%(mid)s. rewrite bcells_rep_true, bcells_rep_false.
  rewrite rep_S_r, <- app_assoc.
  pose proof (%(rt1)s j (bcells %(ZL)s %(OL)s x) []) as H. rewrite ?app_nil_r in H. exact H.
Qed.

Lemma ahR_%(mid)s : forall x z p, p <= 1 ->
  Reach1 tm (aC_%(mid)s (x, z, p)) (aD_%(mid)s x (fst (rinc_%(mid)s z p)) (snd (rinc_%(mid)s z p))).
Proof.
  intros x z p Hp. unfold rinc_%(mid)s.
  destruct (alltrue z) eqn:E.
  - assert (Hz : exists j, z = repeat true j) by (exists (length z); apply alltrue_eq, E).
    destruct Hz as (j & ->). rewrite repeat_length.
    destruct p as [|[|p]]; [apply ahRt0_%(mid)s | apply ahRt1_%(mid)s | lia].
  - destruct (ttdecomp z) as [(j & s & ->) | (j & ->)].
    2:{ rewrite alltrue_repeat in E. discriminate. }
    cbn [fst snd]. rewrite binc_int. apply ahRc_%(mid)s.
Qed.
""",
    hidef="""Lemma aHI_%(mid)s : forall s, aI_%(mid)s s -> aI_%(mid)s (aF_%(mid)s s).
Proof.
  intros [[x z] p] [Hz Hp]. unfold aF_%(mid)s, aI_%(mid)s, rinc_%(mid)s.
  destruct (alltrue z) eqn:E.
  - destruct p as [|[|p]]; cbn [fst snd]; rewrite ?repeat_length; split; try lia.
  - cbn [fst snd]. destruct (binc_val z E) as [_ H2]. rewrite H2. split; assumption.
Qed.
""",
    afr="""Lemma afR_%(mid)s : forall t,
  (forall x j s p, Fires tm (aC_%(mid)s (x, repeat true j ++ false :: s, p)) t) ->
  (forall x j, Fires tm (aC_%(mid)s (x, repeat true j, 0)) t) ->
  (forall x j, Fires tm (aC_%(mid)s (x, repeat true j, 1)) t) ->
  forall s, aI_%(mid)s s -> Fires tm (aC_%(mid)s s) t.
Proof.
  intros t Hc H0 H1 [[x z] p] [Hz Hp].
  destruct (ttdecomp z) as [(j & s & ->) | (j & ->)]; [apply Hc|].
  destruct p as [|[|p]]; [apply H0 | apply H1 | lia].
Qed.
""",
    afrest="""(** fired by the right half unless the right counter tops in phase 1: then
    by the next round's *)
Lemma afR1_%(mid)s : forall t,
  (forall x j s p, Fires tm (aC_%(mid)s (x, repeat true j ++ false :: s, p)) t) ->
  (forall x j, Fires tm (aC_%(mid)s (x, repeat true j, 0)) t) ->
  forall s, aI_%(mid)s s -> exists n, Fires tm (aC_%(mid)s (fiter _ aF_%(mid)s n s)) t.
Proof.
  intros t Hc H0 [[x z] p] [Hz Hp].
  destruct (ttdecomp z) as [(j & s & ->) | (j & ->)]; [exists 0; apply Hc|].
  destruct p as [|[|p]]; [exists 0; apply H0 | | lia].
  exists 1. cbn [fiter]. unfold aF_%(mid)s, rinc_%(mid)s. rewrite alltrue_repeat. cbn [fst snd].
  rewrite repeat_length. exact (Hc _ 0 (repeat false j) 0).
Qed.

(** fired by the right half when the right counter ends in a 1; one ending
    in 0 does after one round *)
Lemma afH_%(mid)s : forall t,
  (forall x j s p, Fires tm (aC_%(mid)s (x, repeat true (S j) ++ false :: s, p)) t) ->
  (forall x j, Fires tm (aC_%(mid)s (x, repeat true (S j), 0)) t) ->
  (forall x j, Fires tm (aC_%(mid)s (x, repeat true (S j), 1)) t) ->
  forall s, aI_%(mid)s s -> exists n, Fires tm (aC_%(mid)s (fiter _ aF_%(mid)s n s)) t.
Proof.
  intros t Hc H0 H1 [[x z] p] [Hz Hp].
  assert (Hone : forall x z p, p <= 1 -> hd false z = true -> Fires tm (aC_%(mid)s (x, z, p)) t).
  { intros x' z' p' Hp' Hh.
    destruct (ttdecomp z') as [(j & s & ->) | (j & ->)].
    - destruct j as [|j]; [discriminate | apply Hc].
    - destruct j as [|j]; [discriminate|].
      destruct p' as [|[|p']]; [apply H0 | apply H1 | lia]. }
  destruct z as [|[|] s]; [cbn in Hz; lia | exists 0; apply Hone; [exact Hp | reflexivity] |].
  exists 1. cbn [fiter]. unfold aF_%(mid)s, rinc_%(mid)s. cbn [alltrue forallb andb].
  cbn [fst snd binc]. apply Hone; [exact Hp | reflexivity].
Qed.
""")

# the right counter's top WIDENS it (one phase, no right end)
WD = dict(
    aTdef="""Definition aT_%(mid)s (p : nat) : list Sym := [].
""",
    rincdef="""Definition rinc_%(mid)s (z : list bool) (p : nat) : list bool * nat :=
  if alltrue z then (repeat false (length z) ++ [true], p) else (binc z, p).
""",
    rtop="""Lemma ahRt_%(mid)s : forall x j p,
  Reach1 tm (aC_%(mid)s (x, repeat true j, p)) (aD_%(mid)s x (repeat false j ++ [true]) p).
Proof.
  intros x j p. unfold aC_%(mid)s, aD_%(mid)s, aT_%(mid)s. rewrite bcells_rep_true, bcells_ff.
  change (bcells %(ZR)s %(OR)s [true]) with (%(OR)s ++ []).
  pose proof (%(rt)s j (bcells %(ZL)s %(OL)s x) []) as H. rewrite ?app_nil_r in H. rewrite ?app_nil_r. exact H.
Qed.

Lemma ahR_%(mid)s : forall x z p, p <= 1 ->
  Reach1 tm (aC_%(mid)s (x, z, p)) (aD_%(mid)s x (fst (rinc_%(mid)s z p)) (snd (rinc_%(mid)s z p))).
Proof.
  intros x z p Hp. unfold rinc_%(mid)s.
  destruct (alltrue z) eqn:E.
  - assert (Hz : exists j, z = repeat true j) by (exists (length z); apply alltrue_eq, E).
    destruct Hz as (j & ->). rewrite repeat_length. apply ahRt_%(mid)s.
  - destruct (ttdecomp z) as [(j & s & ->) | (j & ->)].
    2:{ rewrite alltrue_repeat in E. discriminate. }
    cbn [fst snd]. rewrite binc_int. apply ahRc_%(mid)s.
Qed.
""",
    hidef="""Lemma aHI_%(mid)s : forall s, aI_%(mid)s s -> aI_%(mid)s (aF_%(mid)s s).
Proof.
  intros [[x z] p] [Hz Hp]. unfold aF_%(mid)s, aI_%(mid)s, rinc_%(mid)s.
  destruct (alltrue z) eqn:E.
  - cbn [fst snd]. rewrite app_length, repeat_length. cbn. split; lia.
  - cbn [fst snd]. destruct (binc_val z E) as [_ H2]. rewrite H2. split; assumption.
Qed.
""",
    afr="""Lemma afR_%(mid)s : forall t,
  (forall x j s p, Fires tm (aC_%(mid)s (x, repeat true j ++ false :: s, p)) t) ->
  (forall x j p, Fires tm (aC_%(mid)s (x, repeat true j, p)) t) ->
  forall s, aI_%(mid)s s -> Fires tm (aC_%(mid)s s) t.
Proof.
  intros t Hc Ht [[x z] p] [Hz Hp].
  destruct (ttdecomp z) as [(j & s & ->) | (j & ->)]; [apply Hc | apply Ht].
Qed.
""",
    afrest="""(** fired by the right half when the right counter ends in a 1; one ending
    in 0 does after one round *)
Lemma afH_%(mid)s : forall t,
  (forall x j s p, Fires tm (aC_%(mid)s (x, repeat true (S j) ++ false :: s, p)) t) ->
  (forall x j p, Fires tm (aC_%(mid)s (x, repeat true (S j), p)) t) ->
  forall s, aI_%(mid)s s -> exists n, Fires tm (aC_%(mid)s (fiter _ aF_%(mid)s n s)) t.
Proof.
  intros t Hc Ht [[x z] p] [Hz Hp].
  assert (Hone : forall x z p, hd false z = true -> Fires tm (aC_%(mid)s (x, z, p)) t).
  { intros x' z' p' Hh.
    destruct (ttdecomp z') as [(j & s & ->) | (j & ->)].
    - destruct j as [|j]; [discriminate | apply Hc].
    - destruct j as [|j]; [discriminate | apply Ht]. }
  destruct z as [|[|] s]; [cbn in Hz; lia | exists 0; apply Hone; reflexivity |].
  exists 1. cbn [fiter]. unfold aF_%(mid)s, rinc_%(mid)s. cbn [alltrue forallb andb].
  cbn [fst snd binc]. apply Hone; reflexivity.
Qed.
""")

FIRE_RTW = """      intros x j p. unfold aC_%(mid)s, aT_%(mid)s. rewrite bcells_rep_true.
      pose proof (%(f)s j (bcells %(ZL)s %(OL)s x) []) as H. rewrite ?app_nil_r in H. rewrite ?app_nil_r. exact H."""


FIRE_L = """  - exists 0. apply afL_%(mid)s; [| |exact Hs].
    + intros k r z p. unfold aD_%(mid)s. rewrite bcells_tt.
      change (bcells %(ZL)s %(OL)s (false :: r)) with (%(ZL)s ++ bcells %(ZL)s %(OL)s r).
      rewrite <- ?app_assoc. exact (%(flc)s k (bcells %(ZL)s %(OL)s r) (bcells %(ZR)s %(OR)s z ++ aT_%(mid)s p)).
    + intros k z p. unfold aD_%(mid)s. rewrite bcells_rep_true.
      pose proof (%(flt)s k [] (bcells %(ZR)s %(OR)s z ++ aT_%(mid)s p)) as H.
      unfold aT_%(mid)s in *. rewrite ?app_nil_r in H. rewrite ?app_nil_r. exact H."""

FIRE_RC = """      intros x j s p. unfold aC_%(mid)s. rewrite bcells_tt.
      change (bcells %(ZR)s %(OR)s (false :: s)) with (%(ZR)s ++ bcells %(ZR)s %(OR)s s).
      rewrite <- ?app_assoc. exact (%(frc)s j (bcells %(ZL)s %(OL)s x) (bcells %(ZR)s %(OR)s s ++ aT_%(mid)s p))."""
FIRE_RT = """      intros x j. unfold aC_%(mid)s, aT_%(mid)s. rewrite bcells_rep_true.
      pose proof (%(f)s j (bcells %(ZL)s %(OL)s x) []) as H. rewrite ?app_nil_r in H. exact H."""

FIRE_R = """  - exists 0. apply afR_%(mid)s; [| | |exact Hs].
    +""" + FIRE_RC[5:] + """
    +""" + FIRE_RT[5:].replace('%(f)s', '%(frt0)s') + """
    +""" + FIRE_RT[5:].replace('%(f)s', '%(frt1)s')

FIRE_R1 = """  - apply afR1_%(mid)s; [| |exact Hs].
    +""" + FIRE_RC[5:] + """
    +""" + FIRE_RT[5:].replace('%(f)s', '%(frt0)s')

FIRE_H = """  - apply afH_%(mid)s; [| | |exact Hs].
    +""" + FIRE_RC[5:] + """
    +""" + FIRE_RT[5:].replace('%(f)s', '%(frt01)s') + """
    +""" + FIRE_RT[5:].replace('%(f)s', '%(frt11)s')


FIRE_RW = """  - exists 0. apply afR_%(mid)s; [| |exact Hs].
    +""" + FIRE_RC[5:] + """
    +""" + FIRE_RTW[5:].replace('%(f)s', '%(frt)s')

FIRE_HW = """  - apply afH_%(mid)s; [| |exact Hs].
    +""" + FIRE_RC[5:] + """
    +""" + FIRE_RTW[5:].replace('%(f)s', '%(frt1)s')


def emit_closure_ab(cert, tab, mid):
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
    sy = lambda w: syms(w)  # noqa: E731
    P = dict(mid=mid, qB=ST[r['qB']], hB=SYM[r['hB']], qD=ST[r['qD']], hD=SYM[r['hD']],
             ZL=sy(r['ZL']), OL=sy(r['OL']), ZR=sy(r['ZR']), OR=sy(r['OR']),
             T0=sy(r['T0']), T1=sy(r['T1']), **names)
    cases = []
    for w in g.want:
        inn = lambda *ks: all(w in fires[k] for k in ks)  # noqa: E731
        f = lambda k: fires[k][w]  # noqa: E731
        if inn('lc', 'lt'):
            cases.append(FIRE_L % dict(P, flc=f('lc'), flt=f('lt')))
        elif r.get('rwiden') and inn('rc', 'rt'):
            cases.append(FIRE_RW % dict(P, frc=f('rc'), frt=f('rt')))
        elif r.get('rwiden') and inn('rc1', 'rt1'):
            cases.append(FIRE_HW % dict(P, frc=f('rc1'), frt1=f('rt1')))
        elif r.get('rwiden'):
            return E.CLOSURE_NONE % NoClosure('no fire strategy for %s' % 'ABCD'[w[0]] + str(w[1])), None
        elif inn('rc', 'rt0', 'rt1'):
            cases.append(FIRE_R % dict(P, frc=f('rc'), frt0=f('rt0'), frt1=f('rt1')))
        elif inn('rc', 'rt0'):
            cases.append(FIRE_R1 % dict(P, frc=f('rc'), frt0=f('rt0')))
        elif inn('rc1', 'rt01', 'rt11'):
            cases.append(FIRE_H % dict(P, frc=f('rc1'), frt01=f('rt01'), frt11=f('rt11')))
        else:
            return E.CLOSURE_NONE % NoClosure('no fire strategy for %s' % 'ABCD'[w[0]] + str(w[1])), None
    V = WD if r.get('rwiden') else PH
    body = COQ % dict(P, firecases='\n'.join(cases), **{k: v % P for k, v in V.items()})
    t0, x0, z0, p0 = cert['boot']
    bl = lambda v: '[' + ';'.join('true' if b else 'false' for b in v) + ']'  # noqa: E731
    body += """
Lemma aboot_%(mid)s :
  stepn tm %(t0)d InitES = Some (lift (aC_%(mid)s (%(x0)s, %(z0)s, %(p0)d))).
Proof.
  assert (H : match csteps tm %(t0)d c0 with
              | Some c => ceqb c (aC_%(mid)s (%(x0)s, %(z0)s, %(p0)d))
              | None => false end = true) by (vm_compute; reflexivity).
  destruct (csteps tm %(t0)d c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** The machine-level theorem, at the INSTRUCTION level, through
    [AbsStepTr.absstep_neverqhtr]. *)
Theorem nqhtr_%(mid)s : NeverQuasiHaltsTr tm_%(mid)s.
Proof.
  exact (absstep_neverqhtr tm_%(mid)s pins_%(mid)s _ aC_%(mid)s aF_%(mid)s aI_%(mid)s
           aHI_%(mid)s aHstep_%(mid)s aHfire_%(mid)s (%(x0)s, %(z0)s, %(p0)d)
           ltac:(cbn; split; lia) %(t0)d aboot_%(mid)s).
Qed.
""" % dict(mid=mid, t0=t0, x0=bl(x0), z0=bl(z0), p0=p0)
    head = """
(** ** The closure: two counters at a pivot, stepped in turn ([AbsStepTr], [TwoSideArmTr]) *)
From BBB4.Checkers Require Import LadderNest LadderCheckNestTr.
From BBB4.Counters Require Import NestCountTr PhBinCountTr TwoSideArmTr AbsStepTr.

"""
    return head + inner_coq(mid, g.inner) + ''.join(g.out) + body, dict(nest=True)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('spec')
    ap.add_argument('-o', '--out', required=True)
    a = ap.parse_args()
    spec = a.spec
    r = ROWS[spec]
    E.TR_PINS = E.unfired(spec, 10 ** 6)
    t0, x0, z0, p0 = boot(spec, r)
    cert = dict(spec=spec, closed=True, ladder=[], arms=[], row=r, boot=(t0, x0, z0, p0),
                family=dict(state='ABCD'[r['qB']], head=r['hB'], side='R', other_side_cells=[],
                            digits=[list(r['ZL']), list(r['OL'])], near_head_prefix=[], terminator=[],
                            terminators_by_phase=[[]], n_phases=1, base=2, digit_len=2,
                            code='binary', value_step_per_anchor_visit=1),
                fill=dict(widens_by=1, target_prefix=[], target_fill_digit=0, target_suffix=[],
                          lands_in_phase=0))
    E.emit_closure = emit_closure_ab
    good, bad, cd = E.emit(cert, a.out)
    print('%s: closure %s' % (a.out, 'BUILT' if cd else 'not built'))
    return 0 if cd else 1


if __name__ == '__main__':
    sys.exit(main())
