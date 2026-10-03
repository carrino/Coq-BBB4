#!/usr/bin/env python3
"""UNTRUSTED emitter (SCOPING_INSTR 7.4.LE9): LE7's zig-zag MIRRORS, a binary
counter held on both sides of the head and carried copy by copy -> a Coq
board closed by [TopMapGTr].

At the anchor the tape is [cells x | h | 0 cells x] (both copies LSB at the
head, digit words Z / O read outward), plain binary increment (the overflow
is the carry over the blank end).  A carry over k ones is a fixed sequence
of PASSES, each crossing one copy's block while the other copy is an opaque
tail ([TwoSideArmTr], arms from le9/gen2.py): the row's `chain` lists them,
each with the form it starts and ends at.  The row's `fire` arm fires every
instruction; its prefix of the chain is a [Reach0] from the carry's start.

    python3 emit_zz.py SPEC -o OUT.v
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

ZZ1_BOARD = r"""
(** *** The board: one phase, the top is the carry over the blank end *)
Definition zG_%(mid)s (p k m : nat) : list bool * nat * nat := (repeat false k ++ [true], m, p).
Definition zInv_%(mid)s (k m p : nat) : Prop := 1 <= k.

Lemma zcarryI_%(mid)s : forall k r m p, zInv_%(mid)s (k + S (length r)) m p ->
  Reach1 tm (zC_%(mid)s (repeat true k ++ false :: r) m p) (zC_%(mid)s (repeat false k ++ true :: r) m p).
Proof. intros k r m p _. apply zcarryC_%(mid)s. Qed.

Lemma ztopI_%(mid)s : forall p k m, zInv_%(mid)s k m p ->
  Reach1 tm (zC_%(mid)s (repeat true k) m p) (gcfg zC_%(mid)s (zG_%(mid)s p k m)).
Proof. intros p k m _. exact (ztop_%(mid)s k m p). Qed.

Lemma zGinv_%(mid)s : forall p k m, zInv_%(mid)s k m p -> GInv zInv_%(mid)s (zG_%(mid)s p k m).
Proof. intros p k m _. unfold GInv, zG_%(mid)s, zInv_%(mid)s. rewrite app_length, repeat_length. cbn. lia. Qed.

Lemma zfire_%(mid)s : forall t, ~ In t pins_%(mid)s -> exists Q : nat -> nat -> nat -> Prop,
  (forall k m p, Q k m p -> zInv_%(mid)s k m p -> Fires tm (zC_%(mid)s (repeat true k) m p) t) /\
  (forall k m p, zInv_%(mid)s k m p -> exists n,
     let '(k', m', p') := gmiter zG_%(mid)s (k, m, p) n in Q k' m' p').
Proof.
  intros t Hnp. exists (fun _ _ _ => True). split.
  - intros k m p _ Hk. destruct k as [|n]; [unfold zInv_%(mid)s in Hk; lia|].
    apply zfireC_%(mid)s, Hnp.
  - intros k m p _. exists 0. exact I.
Qed.
"""

# 1RB0LA_0RC1RB_0LD0RB_1LD0LA at A0: Z = 00, O = 01.  The carry over 1 + n
# ones (then a 0 digit, then the next digit's first cell 0):
#   a0  flat, C1;  a1  right pass over the right copy (01 -> 11);
#   a2  left pass over the left copy (01 -> 00);  a3 flat;
#   a4  right pass back (11 -> 00);  a5 flat.   k0: the carry over no ones.
ZZ1 = dict(
    q=A, Z=(0, 0), O=(0, 1),
    arms=[
        ('a0', (A, 0, [('c', (0, 1)), ('X',)], [('c', (0, 0, 1)), ('X',)]),
               (C, 1, [('c', (0, 1, 1)), ('X',)], [('c', (0, 1)), ('X',)])),
        ('a1', (C, 1, [('X',)], [('r', (0, 1), 0), ('c', (0, 0, 0)), ('X',)]),
               (D, 0, [('X',)], [('r', (1, 1), 0), ('c', (1, 0, 0)), ('X',)])),
        ('a2', (D, 0, [('c', (0, 1, 1)), ('r', (0, 1), 0), ('c', (0, 0, 0)), ('X',)], [('X',)]),
               (B, 0, [('c', (0, 0)), ('r', (0, 0), 0), ('c', (1, 0)), ('X',)], [('c', (1, 1)), ('X',)])),
        ('a3', (B, 0, [('X',)], [('c', (1, 1)), ('X',)]),
               (B, 1, [('c', (0, 0)), ('X',)], [('X',)])),
        ('a4', (B, 1, [('X',)], [('r', (1, 1), 0), ('c', (1, 0, 0)), ('X',)]),
               (A, 1, [('X',)], [('r', (0, 0), 0), ('c', (0, 1, 0)), ('X',)])),
        ('a5', (A, 1, [('c', (0,)), ('X',)], [('X',)]),
               (A, 0, [('X',)], [('c', (0,)), ('X',)])),
        ('k0', (A, 0, [('c', (0, 0, 0)), ('X',)], [('c', (0, 0, 0, 0)), ('X',)]),
               (A, 0, [('c', (0, 1, 0)), ('X',)], [('c', (0, 0, 1, 0)), ('X',)])),
    ],
    fire=[('a2', 'zm2_%(mid)s n [] []', 'zpre2_%(mid)s n [] []',
           'n [] (rep [S1;S1] (S n) ++ [S1;S0;S0] ++ [])')],
    coq=r"""
(** *** The carry over [1 + n] ones, pass by pass *)
Definition zst_%(mid)s (n : nat) (XL XR : list Sym) : cconf :=
  (StA, (rep [S0;S1] (S n) ++ [S0;S0;S0] ++ XL, S0, [S0] ++ rep [S0;S1] (S n) ++ [S0;S0;S0] ++ XR)).
Definition zm1_%(mid)s (n : nat) (XL XR : list Sym) : cconf :=
  (StC, ([S0;S1;S1] ++ rep [S0;S1] n ++ [S0;S0;S0] ++ XL, S1, [S0;S1] ++ rep [S0;S1] n ++ [S0;S0;S0] ++ XR)).
Definition zm2_%(mid)s (n : nat) (XL XR : list Sym) : cconf :=
  (StD, ([S0;S1;S1] ++ rep [S0;S1] n ++ [S0;S0;S0] ++ XL, S0, rep [S1;S1] (S n) ++ [S1;S0;S0] ++ XR)).
Definition zm3_%(mid)s (n : nat) (XL XR : list Sym) : cconf :=
  (StB, ([S0;S0] ++ rep [S0;S0] n ++ [S1;S0] ++ XL, S0, [S1;S1] ++ rep [S1;S1] (S n) ++ [S1;S0;S0] ++ XR)).
Definition zm4_%(mid)s (n : nat) (XL XR : list Sym) : cconf :=
  (StB, ([S0;S0] ++ [S0;S0] ++ rep [S0;S0] n ++ [S1;S0] ++ XL, S1, rep [S1;S1] (S n) ++ [S1;S0;S0] ++ XR)).
Definition zm5_%(mid)s (n : nat) (XL XR : list Sym) : cconf :=
  (StA, ([S0;S0;S0;S0] ++ rep [S0;S0] n ++ [S1;S0] ++ XL, S1, rep [S0;S0] (S n) ++ [S0;S1;S0] ++ XR)).
Definition zen_%(mid)s (n : nat) (XL XR : list Sym) : cconf :=
  (StA, ([S0;S0;S0] ++ rep [S0;S0] n ++ [S1;S0] ++ XL, S0, [S0] ++ rep [S0;S0] (S n) ++ [S0;S1;S0] ++ XR)).

Lemma zpre2_%(mid)s : forall n XL XR, Reach0 tm (zst_%(mid)s n XL XR) (zm2_%(mid)s n XL XR).
Proof.
  intros n XL XR.
  apply (reach0_trans tm _ (zm1_%(mid)s n XL XR)).
  { apply reach1_0. exact (%(a0)s 0 (rep [S0;S1] n ++ [S0;S0;S0] ++ XL) (rep [S0;S1] n ++ [S0;S0;S0] ++ XR)). }
  apply reach1_0. exact (%(a1)s (S n) ([S0;S1;S1] ++ rep [S0;S1] n ++ [S0;S0;S0] ++ XL) XR).
Qed.

Lemma zcarry_%(mid)s : forall n XL XR, Reach1 tm (zst_%(mid)s n XL XR) (zen_%(mid)s n XL XR).
Proof.
  intros n XL XR.
  apply (reach01 tm _ (zm2_%(mid)s n XL XR)); [apply zpre2_%(mid)s|].
  apply (reach10 tm _ (zm3_%(mid)s n XL XR)).
  { exact (%(a2)s n XL (rep [S1;S1] (S n) ++ [S1;S0;S0] ++ XR)). }
  apply (reach0_trans tm _ (zm4_%(mid)s n XL XR)).
  { apply reach1_0. exact (%(a3)s 0 ([S0;S0] ++ rep [S0;S0] n ++ [S1;S0] ++ XL) (rep [S1;S1] (S n) ++ [S1;S0;S0] ++ XR)). }
  apply (reach0_trans tm _ (zm5_%(mid)s n XL XR)).
  { apply reach1_0. exact (%(a4)s (S n) ([S0;S0;S0;S0] ++ rep [S0;S0] n ++ [S1;S0] ++ XL) XR). }
  apply reach1_0. exact (%(a5)s 0 ([S0;S0;S0] ++ rep [S0;S0] n ++ [S1;S0] ++ XL) (rep [S0;S0] (S n) ++ [S0;S1;S0] ++ XR)).
Qed.

Lemma zfix_%(mid)s : forall n (Y : list Sym),
  [S0;S0;S0] ++ rep [S0;S0] n ++ [S1;S0] ++ Y = rep [S0;S0] (S n) ++ [S0;S1;S0] ++ Y.
Proof.
  induction n as [|n IH]; intros Y; [reflexivity|].
  change (rep [S0;S0] (S (S n))) with ([S0;S0] ++ rep [S0;S0] (S n)).
  rewrite <- app_assoc, <- IH. reflexivity.
Qed.

(** *** The counter, both copies, padded with a blank each side *)
Definition zC_%(mid)s (x : list bool) (m p : nat) : cconf :=
  (StA, (bcells [S0;S0] [S0;S1] x ++ [S0], S0, S0 :: bcells [S0;S0] [S0;S1] x ++ [S0])).

Lemma zpad_%(mid)s : forall r, exists Y, bcells [S0;S0] [S0;S1] r ++ [S0] = S0 :: Y.
Proof. intros [|[|] r]; [exists [] | eexists | eexists]; reflexivity. Qed.

Lemma zcarryC_%(mid)s : forall k r m p,
  Reach1 tm (zC_%(mid)s (repeat true k ++ false :: r) m p) (zC_%(mid)s (repeat false k ++ true :: r) m p).
Proof.
  intros k r m p. unfold zC_%(mid)s.
  rewrite !bcells_tt, !bcells_ff.
  change (bcells [S0;S0] [S0;S1] (false :: r)) with ([S0;S0] ++ bcells [S0;S0] [S0;S1] r).
  change (bcells [S0;S0] [S0;S1] (true :: r)) with ([S0;S1] ++ bcells [S0;S0] [S0;S1] r).
  destruct (zpad_%(mid)s r) as (Y & HY).
  rewrite <- !app_assoc, !HY.
  destruct k as [|n].
  - exact (%(k0)s 0 Y Y).
  - pose proof (zcarry_%(mid)s n Y Y) as H. unfold zst_%(mid)s, zen_%(mid)s in H.
    rewrite zfix_%(mid)s in H. exact H.
Qed.

Lemma ztop_%(mid)s : forall k m p,
  Reach1 tm (zC_%(mid)s (repeat true k) m p) (zC_%(mid)s (repeat false k ++ [true]) m p).
Proof.
  intros k m p.
  apply (reach1_lift_l tm _ (zC_%(mid)s (repeat true k ++ [false]) m p)).
  { unfold zC_%(mid)s. rewrite bcells_app. cbn [bcells flat_map].
    rewrite <- !app_assoc. cbn [app].
    rewrite <- (lift_fixL_padn 2 StA (bcells [S0;S0] [S0;S1] (repeat true k) ++ [S0])).
    rewrite <- (lift_fixR_padn 2 StA _ S0 (S0 :: bcells [S0;S0] [S0;S1] (repeat true k) ++ [S0])).
    cbn [repeat app]. rewrite <- ?app_assoc. cbn [app]. reflexivity. }
  exact (zcarryC_%(mid)s k [] m p).
Qed.

Lemma zfireC_%(mid)s : forall t, ~ In t pins_%(mid)s -> forall n m p,
  Fires tm (zC_%(mid)s (repeat true (S n)) m p) t.
Proof.
  intros t Hnp n m p.
  apply (fire_lift tm _ (zst_%(mid)s n [] [])).
  { unfold zC_%(mid)s, zst_%(mid)s. rewrite bcells_rep_true. cbn [app].
    rewrite <- (lift_fixL_padn 2 StA (rep [S0;S1] (S n) ++ [S0])).
    rewrite <- (lift_fixR_padn 2 StA _ S0 (S0 :: rep [S0;S1] (S n) ++ [S0])).
    cbn [repeat app]. rewrite <- ?app_assoc. cbn [app]. reflexivity. }
  destruct t as [q s]; destruct q, s; try (exfalso; apply Hnp; simpl; tauto).
%(firecases)s
Qed.

""" + ZZ1_BOARD,
)


# 1RB0LA_1LC0RB_1RD1LA_1LA1RC at A0: the copies use different words, the
# left (outward) Z = 00, O = 10 and terminator 1, the right 00 ++ cells x ++ 01
# with O = 01.  The carry over n ones (then a 0 digit) is four passes, each
# carrying its block across the head: p1 left over the left copy (10 -> 11
# on the right), p2 back right (11 -> 00 on the left), p3 right over the
# right copy (01 -> 11 on the left), p4 back left (11 -> 00 on the right).
# The top (x all ones) is the same carry with n = k + 1 over the blank ends.
ZZ2 = dict(
    q=A,
    dec=lambda L, R: zz2_dec(L, R),
    arms=[
        ('p1', (A, 0, [('r', (1, 0), 0), ('c', (0,)), ('X',)], [('c', (0, 0)), ('X',)]),
               (A, 0, [('X',)], [('r', (1, 1), 0), ('c', (1, 1, 0)), ('X',)])),
        ('p2', (A, 0, [('X',)], [('r', (1, 1), 0), ('c', (1, 1, 0)), ('X',)]),
               (B, 0, [('c', (0, 0)), ('r', (0, 0), 0), ('c', (1,)), ('X',)], [('X',)])),
        ('p3', (B, 0, [('c', (0, 0)), ('X',)], [('r', (0, 1), 0), ('c', (0, 0)), ('X',)]),
               (D, 0, [('r', (1, 1), 0), ('c', (1, 1, 1, 0)), ('X',)], [('X',)])),
        ('p4', (D, 0, [('r', (1, 1), 0), ('c', (1, 1, 1, 0)), ('X',)], [('X',)]),
               (A, 0, [('X',)], [('c', (0, 0)), ('r', (0, 0), 0), ('c', (0, 1)), ('X',)])),
    ],
    fire=[('p1', 'zst_%(mid)s (S k) [] []', 'reach0_refl tm _',
           '(S k) ([S0] ++ []) (rep [S0;S1] (S k) ++ [S0;S0] ++ [])'),
          ('p2', 'zm1_%(mid)s (S k) [] []', 'zpre1_%(mid)s (S k) [] []',
           '(S k) ([S0] ++ []) (rep [S0;S1] (S k) ++ [S0;S0] ++ [])'),
          ('p3', 'zm2_%(mid)s (S k) [] []', 'zpre2_%(mid)s (S k) [] []',
           '(S k) (rep [S0;S0] (S k) ++ [S1] ++ [S0] ++ []) []'),
          ('p4', 'zm3_%(mid)s (S k) [] []', 'zpre3_%(mid)s (S k) [] []',
           '(S k) (rep [S0;S0] (S k) ++ [S1] ++ [S0] ++ []) []')],
    coq=r"""
(** *** The carry over [n] ones, pass by pass *)
Definition zst_%(mid)s (n : nat) (XL XR : list Sym) : cconf :=
  (StA, (rep [S1;S0] n ++ [S0;S0] ++ XL, S0, [S0;S0] ++ rep [S0;S1] n ++ [S0;S0] ++ XR)).
Definition zm1_%(mid)s (n : nat) (XL XR : list Sym) : cconf :=
  (StA, ([S0] ++ XL, S0, rep [S1;S1] n ++ [S1;S1;S0] ++ rep [S0;S1] n ++ [S0;S0] ++ XR)).
Definition zm2_%(mid)s (n : nat) (XL XR : list Sym) : cconf :=
  (StB, ([S0;S0] ++ rep [S0;S0] n ++ [S1] ++ [S0] ++ XL, S0, rep [S0;S1] n ++ [S0;S0] ++ XR)).
Definition zm3_%(mid)s (n : nat) (XL XR : list Sym) : cconf :=
  (StD, (rep [S1;S1] n ++ [S1;S1;S1;S0] ++ rep [S0;S0] n ++ [S1] ++ [S0] ++ XL, S0, XR)).
Definition zen_%(mid)s (n : nat) (XL XR : list Sym) : cconf :=
  (StA, (rep [S0;S0] n ++ [S1] ++ [S0] ++ XL, S0, [S0;S0] ++ rep [S0;S0] n ++ [S0;S1] ++ XR)).

Lemma zst1_%(mid)s : forall n XL XR, Reach1 tm (zst_%(mid)s n XL XR) (zm1_%(mid)s n XL XR).
Proof. intros n XL XR. exact (%(p1)s n ([S0] ++ XL) (rep [S0;S1] n ++ [S0;S0] ++ XR)). Qed.
Lemma z12_%(mid)s : forall n XL XR, Reach1 tm (zm1_%(mid)s n XL XR) (zm2_%(mid)s n XL XR).
Proof. intros n XL XR. exact (%(p2)s n ([S0] ++ XL) (rep [S0;S1] n ++ [S0;S0] ++ XR)). Qed.
Lemma z23_%(mid)s : forall n XL XR, Reach1 tm (zm2_%(mid)s n XL XR) (zm3_%(mid)s n XL XR).
Proof. intros n XL XR. exact (%(p3)s n (rep [S0;S0] n ++ [S1] ++ [S0] ++ XL) XR). Qed.
Lemma z3e_%(mid)s : forall n XL XR, Reach1 tm (zm3_%(mid)s n XL XR) (zen_%(mid)s n XL XR).
Proof. intros n XL XR. exact (%(p4)s n (rep [S0;S0] n ++ [S1] ++ [S0] ++ XL) XR). Qed.

Lemma zpre1_%(mid)s : forall n XL XR, Reach0 tm (zst_%(mid)s n XL XR) (zm1_%(mid)s n XL XR).
Proof. intros n XL XR. apply reach1_0, zst1_%(mid)s. Qed.
Lemma zpre2_%(mid)s : forall n XL XR, Reach0 tm (zst_%(mid)s n XL XR) (zm2_%(mid)s n XL XR).
Proof. intros n XL XR. apply (reach0_trans tm _ _ _ (zpre1_%(mid)s n XL XR)), reach1_0, z12_%(mid)s. Qed.
Lemma zpre3_%(mid)s : forall n XL XR, Reach0 tm (zst_%(mid)s n XL XR) (zm3_%(mid)s n XL XR).
Proof. intros n XL XR. apply (reach0_trans tm _ _ _ (zpre2_%(mid)s n XL XR)), reach1_0, z23_%(mid)s. Qed.

Lemma zcarry_%(mid)s : forall n XL XR, Reach1 tm (zst_%(mid)s n XL XR) (zen_%(mid)s n XL XR).
Proof.
  intros n XL XR.
  apply (reach01 tm _ (zm3_%(mid)s n XL XR)); [apply zpre3_%(mid)s|].
  apply z3e_%(mid)s.
Qed.

(** *** The counter, both copies *)
Definition zC_%(mid)s (x : list bool) (m p : nat) : cconf :=
  (StA, (bcells [S0;S0] [S1;S0] x ++ [S1], S0, [S0;S0] ++ bcells [S0;S0] [S0;S1] x ++ [S0;S1])).

Lemma zcarryC_%(mid)s : forall k r m p,
  Reach1 tm (zC_%(mid)s (repeat true k ++ false :: r) m p) (zC_%(mid)s (repeat false k ++ true :: r) m p).
Proof.
  intros k r m p. unfold zC_%(mid)s.
  rewrite !bcells_tt, !bcells_ff.
  change (bcells [S0;S0] [S1;S0] (false :: r)) with ([S0;S0] ++ bcells [S0;S0] [S1;S0] r).
  change (bcells [S0;S0] [S1;S0] (true :: r)) with ([S1;S0] ++ bcells [S0;S0] [S1;S0] r).
  change (bcells [S0;S0] [S0;S1] (false :: r)) with ([S0;S0] ++ bcells [S0;S0] [S0;S1] r).
  change (bcells [S0;S0] [S0;S1] (true :: r)) with ([S0;S1] ++ bcells [S0;S0] [S0;S1] r).
  rewrite <- !app_assoc.
  exact (zcarry_%(mid)s k (bcells [S0;S0] [S1;S0] r ++ [S1]) (bcells [S0;S0] [S0;S1] r ++ [S0;S1])).
Qed.

(** the top: the carry over [k + 1] ones, the last of them the blank ends *)
Lemma ztoplift_%(mid)s : forall k m p,
  lift (zC_%(mid)s (repeat true k) m p) = lift (zst_%(mid)s (S k) [] []).
Proof.
  intros k m p. unfold zC_%(mid)s, zst_%(mid)s. rewrite !bcells_rep_true, !rep_S_r.
  rewrite <- (lift_fixL_padn 3 StA (rep [S1;S0] k ++ [S1]) S0 ([S0;S0] ++ rep [S0;S1] k ++ [S0;S1])).
  rewrite <- (lift_fixR_padn 2 StA ((rep [S1;S0] k ++ [S1]) ++ repeat S0 3) S0
                ([S0;S0] ++ rep [S0;S1] k ++ [S0;S1])).
  cbn [repeat]. rewrite <- !app_assoc. reflexivity.
Qed.

Lemma ztop_%(mid)s : forall k m p,
  Reach1 tm (zC_%(mid)s (repeat true k) m p) (zC_%(mid)s (repeat false (S k)) m p).
Proof.
  intros k m p.
  apply (reach1_lift_l tm _ (zst_%(mid)s (S k) [] [])); [apply ztoplift_%(mid)s|].
  apply (reach1_lift_r tm _ _ (zen_%(mid)s (S k) [] [])).
  { unfold zC_%(mid)s, zen_%(mid)s. rewrite !bcells_rep_false.
    rewrite <- (lift_fixL_padn 1 StA (rep [S0;S0] (S k) ++ [S1])).
    cbn [repeat]. rewrite <- !app_assoc. reflexivity. }
  apply zcarry_%(mid)s.
Qed.

Lemma zfireC_%(mid)s : forall t, ~ In t pins_%(mid)s -> forall k m p,
  Fires tm (zC_%(mid)s (repeat true k) m p) t.
Proof.
  intros t Hnp k m p.
  apply (fire_lift tm _ (zst_%(mid)s (S k) [] [])); [apply ztoplift_%(mid)s|].
  destruct t as [q s]; destruct q, s; try (exfalso; apply Hnp; simpl; tauto).
%(firecases)s
Qed.

(** *** The board: one phase, the top widens the counter by a digit *)
Definition zG_%(mid)s (p k m : nat) : list bool * nat * nat := (repeat false (S k), m, p).
Definition zInv_%(mid)s (k m p : nat) : Prop := True.

Lemma zcarryI_%(mid)s : forall k r m p, zInv_%(mid)s (k + S (length r)) m p ->
  Reach1 tm (zC_%(mid)s (repeat true k ++ false :: r) m p) (zC_%(mid)s (repeat false k ++ true :: r) m p).
Proof. intros k r m p _. apply zcarryC_%(mid)s. Qed.

Lemma ztopI_%(mid)s : forall p k m, zInv_%(mid)s k m p ->
  Reach1 tm (zC_%(mid)s (repeat true k) m p) (gcfg zC_%(mid)s (zG_%(mid)s p k m)).
Proof. intros p k m _. exact (ztop_%(mid)s k m p). Qed.

Lemma zGinv_%(mid)s : forall p k m, zInv_%(mid)s k m p -> GInv zInv_%(mid)s (zG_%(mid)s p k m).
Proof. intros p k m _. exact I. Qed.

Lemma zfire_%(mid)s : forall t, ~ In t pins_%(mid)s -> exists Q : nat -> nat -> nat -> Prop,
  (forall k m p, Q k m p -> zInv_%(mid)s k m p -> Fires tm (zC_%(mid)s (repeat true k) m p) t) /\
  (forall k m p, zInv_%(mid)s k m p -> exists n,
     let '(k', m', p') := gmiter zG_%(mid)s (k, m, p) n in Q k' m' p').
Proof.
  intros t Hnp. exists (fun _ _ _ => True). split.
  - intros k m p _ _. apply zfireC_%(mid)s, Hnp.
  - intros k m p _. exists 0. exact I.
Qed.
""",
)


def zz2_dec(L, R):
    """x when L = cells x ++ 1 (Z 00, O 10) and R = 00 ++ cells x ++ 01 (O 01)"""
    def rd(st, Z, O):
        x = []
        while len(st) >= 2 and st[:2] in (Z, O):
            x.append(st[:2] == O)
            st = st[2:]
        return x, st
    L = L.rstrip('0')
    R = R.rstrip('0')
    if not R.startswith('00'):
        return None
    xl, tl = rd(L, '00', '10')
    xr, tr = rd(R[2:], '00', '01')
    # the right terminator 01 reads as a last digit O
    if tl != '1' or tr or not xr or not xr[-1]:
        return None
    return xl if xl == xr[:-1] else None


def zz1_dec(L, R):
    def rd(st):
        x = []
        while st[:2] in ('00', '01') and len(st) >= 2:
            x.append(st[:2] == '01')
            st = st[2:]
        return x, st
    xl, tl = rd(L)
    if R.startswith('0'):
        xr, tr = rd(R[1:])
        if xl == xr and xl and not tl.strip('0') and not tr.strip('0'):
            return xl
    return None


ZZ1['dec'] = zz1_dec

# 1RB1RC_0RC1RB_0LD0RB_1LD0LA at A0: the counter of ZZ1 (both copies Z = 00,
# O = 01), carried differently.  Over 1 + n ones: q1 flat; q2 a bounce over
# the right copy (01 -> 11); q3a a bounce over the left copy (01 -> 00, the
# 0 digit -> 01); q3b right across the right copy's ones, carrying them to
# the left; q4 back left, carrying them to the right as 00 (the 0 digit -> 01).
ZZ3 = dict(
    q=A,
    dec=lambda L, R: zz1_dec(L, R),
    arms=[
        ('q1', (A, 0, [('c', (0,)), ('X',)], [('c', (0, 0)), ('X',)]),
               (A, 0, [('X',)], [('c', (0, 1, 0)), ('X',)])),
        ('q2', (A, 0, [('X',)], [('c', (0, 1, 0, 1)), ('r', (0, 1), 0), ('c', (0, 0)), ('X',)]),
               (D, 1, [('X',)], [('c', (1, 1, 1, 1)), ('r', (1, 1), 0), ('c', (1, 0)), ('X',)])),
        ('q3a', (D, 1, [('c', (1,)), ('r', (0, 1), 0), ('c', (0, 0)), ('X',)], [('X',)]),
                (B, 0, [('c', (0,)), ('r', (0, 0), 0), ('c', (0, 1)), ('X',)], [('X',)])),
        ('q3b', (B, 0, [('X',)], [('c', (1, 1, 1, 1)), ('r', (1, 1), 0), ('c', (1, 0)), ('X',)]),
                (B, 0, [('r', (1, 1), 0), ('c', (1, 1, 1, 1, 0, 0)), ('X',)], [('X',)])),
        ('q4', (B, 0, [('r', (1, 1), 0), ('c', (1, 1, 1, 1, 0, 0)), ('X',)], [('c', (0,)), ('X',)]),
               (A, 0, [('c', (0,)), ('X',)], [('c', (0, 0, 0)), ('r', (0, 0), 0), ('c', (0, 1, 0)), ('X',)])),
        ('k0', (A, 0, [('c', (0, 0, 0)), ('X',)], [('c', (0, 0, 0, 0)), ('X',)]),
               (A, 0, [('c', (0, 1, 0)), ('X',)], [('c', (0, 0, 1, 0)), ('X',)])),
    ],
    fire=[('q1', 'zst_%(mid)s n [] []', 'reach0_refl tm _',
           '0 ([S1] ++ rep [S0;S1] n ++ [S0;S0] ++ []) ([S1] ++ rep [S0;S1] n ++ [S0;S0;S0] ++ [])'),
          ('q2', 'zm1_%(mid)s n [] []', 'zpre1_%(mid)s n [] []',
           'n ([S1] ++ rep [S0;S1] n ++ [S0;S0] ++ []) ([S0] ++ [])'),
          ('q3a', 'zm2_%(mid)s n [] []', 'zpre2_%(mid)s n [] []',
           'n [] ([S1;S1;S1;S1] ++ rep [S1;S1] n ++ [S1;S0] ++ [S0] ++ [])'),
          ('q3b', 'zm3_%(mid)s n [] []', 'zpre3_%(mid)s n [] []',
           'n ([S0] ++ rep [S0;S0] n ++ [S0;S1] ++ []) ([S0] ++ [])'),
          ('q4', 'zm4_%(mid)s n [] []', 'zpre4_%(mid)s n [] []',
           'n ([S0] ++ rep [S0;S0] n ++ [S0;S1] ++ []) []')],
    coq=r"""
(** *** The carry over [1 + n] ones, pass by pass *)
Definition zst_%(mid)s (n : nat) (XL XR : list Sym) : cconf :=
  (StA, (rep [S0;S1] (S n) ++ [S0;S0] ++ XL, S0, [S0] ++ rep [S0;S1] (S n) ++ [S0;S0;S0] ++ XR)).
Definition zm1_%(mid)s (n : nat) (XL XR : list Sym) : cconf :=
  (StA, ([S1] ++ rep [S0;S1] n ++ [S0;S0] ++ XL, S0, [S0;S1;S0] ++ [S1] ++ rep [S0;S1] n ++ [S0;S0;S0] ++ XR)).
Definition zm2_%(mid)s (n : nat) (XL XR : list Sym) : cconf :=
  (StD, ([S1] ++ rep [S0;S1] n ++ [S0;S0] ++ XL, S1, [S1;S1;S1;S1] ++ rep [S1;S1] n ++ [S1;S0] ++ [S0] ++ XR)).
Definition zm3_%(mid)s (n : nat) (XL XR : list Sym) : cconf :=
  (StB, ([S0] ++ rep [S0;S0] n ++ [S0;S1] ++ XL, S0, [S1;S1;S1;S1] ++ rep [S1;S1] n ++ [S1;S0] ++ [S0] ++ XR)).
Definition zm4_%(mid)s (n : nat) (XL XR : list Sym) : cconf :=
  (StB, (rep [S1;S1] n ++ [S1;S1;S1;S1;S0;S0] ++ [S0] ++ rep [S0;S0] n ++ [S0;S1] ++ XL, S0, [S0] ++ XR)).
Definition zen_%(mid)s (n : nat) (XL XR : list Sym) : cconf :=
  (StA, ([S0] ++ [S0] ++ rep [S0;S0] n ++ [S0;S1] ++ XL, S0, [S0;S0;S0] ++ rep [S0;S0] n ++ [S0;S1;S0] ++ XR)).

Lemma zs1_%(mid)s : forall n XL XR, Reach1 tm (zst_%(mid)s n XL XR) (zm1_%(mid)s n XL XR).
Proof. intros n XL XR. exact (%(q1)s 0 ([S1] ++ rep [S0;S1] n ++ [S0;S0] ++ XL) ([S1] ++ rep [S0;S1] n ++ [S0;S0;S0] ++ XR)). Qed.
Lemma z12_%(mid)s : forall n XL XR, Reach1 tm (zm1_%(mid)s n XL XR) (zm2_%(mid)s n XL XR).
Proof. intros n XL XR. exact (%(q2)s n ([S1] ++ rep [S0;S1] n ++ [S0;S0] ++ XL) ([S0] ++ XR)). Qed.
Lemma z23_%(mid)s : forall n XL XR, Reach1 tm (zm2_%(mid)s n XL XR) (zm3_%(mid)s n XL XR).
Proof. intros n XL XR. exact (%(q3a)s n XL ([S1;S1;S1;S1] ++ rep [S1;S1] n ++ [S1;S0] ++ [S0] ++ XR)). Qed.
Lemma z34_%(mid)s : forall n XL XR, Reach1 tm (zm3_%(mid)s n XL XR) (zm4_%(mid)s n XL XR).
Proof. intros n XL XR. exact (%(q3b)s n ([S0] ++ rep [S0;S0] n ++ [S0;S1] ++ XL) ([S0] ++ XR)). Qed.
Lemma z4e_%(mid)s : forall n XL XR, Reach1 tm (zm4_%(mid)s n XL XR) (zen_%(mid)s n XL XR).
Proof. intros n XL XR. exact (%(q4)s n ([S0] ++ rep [S0;S0] n ++ [S0;S1] ++ XL) XR). Qed.

Lemma zpre1_%(mid)s : forall n XL XR, Reach0 tm (zst_%(mid)s n XL XR) (zm1_%(mid)s n XL XR).
Proof. intros n XL XR. apply reach1_0, zs1_%(mid)s. Qed.
Lemma zpre2_%(mid)s : forall n XL XR, Reach0 tm (zst_%(mid)s n XL XR) (zm2_%(mid)s n XL XR).
Proof. intros n XL XR. apply (reach0_trans tm _ _ _ (zpre1_%(mid)s n XL XR)), reach1_0, z12_%(mid)s. Qed.
Lemma zpre3_%(mid)s : forall n XL XR, Reach0 tm (zst_%(mid)s n XL XR) (zm3_%(mid)s n XL XR).
Proof. intros n XL XR. apply (reach0_trans tm _ _ _ (zpre2_%(mid)s n XL XR)), reach1_0, z23_%(mid)s. Qed.
Lemma zpre4_%(mid)s : forall n XL XR, Reach0 tm (zst_%(mid)s n XL XR) (zm4_%(mid)s n XL XR).
Proof. intros n XL XR. apply (reach0_trans tm _ _ _ (zpre3_%(mid)s n XL XR)), reach1_0, z34_%(mid)s. Qed.

Lemma zcarry_%(mid)s : forall n XL XR, Reach1 tm (zst_%(mid)s n XL XR) (zen_%(mid)s n XL XR).
Proof.
  intros n XL XR.
  apply (reach01 tm _ (zm4_%(mid)s n XL XR)); [apply zpre4_%(mid)s|].
  apply z4e_%(mid)s.
Qed.

(** *** The counter, both copies, padded with a blank each side *)
Definition zC_%(mid)s (x : list bool) (m p : nat) : cconf :=
  (StA, (bcells [S0;S0] [S0;S1] x ++ [S0], S0, S0 :: bcells [S0;S0] [S0;S1] x ++ [S0])).

Lemma zpad_%(mid)s : forall r, exists Y, bcells [S0;S0] [S0;S1] r ++ [S0] = S0 :: Y.
Proof. intros [|[|] r]; [exists [] | eexists | eexists]; reflexivity. Qed.

Lemma zcarryC_%(mid)s : forall k r m p,
  Reach1 tm (zC_%(mid)s (repeat true k ++ false :: r) m p) (zC_%(mid)s (repeat false k ++ true :: r) m p).
Proof.
  intros k r m p. unfold zC_%(mid)s.
  rewrite !bcells_tt, !bcells_ff.
  change (bcells [S0;S0] [S0;S1] (false :: r)) with ([S0;S0] ++ bcells [S0;S0] [S0;S1] r).
  change (bcells [S0;S0] [S0;S1] (true :: r)) with ([S0;S1] ++ bcells [S0;S0] [S0;S1] r).
  destruct (zpad_%(mid)s r) as (Y & HY).
  rewrite <- !app_assoc, !HY.
  destruct k as [|n].
  - exact (%(k0)s 0 Y Y).
  - exact (zcarry_%(mid)s n (S0 :: Y) Y).
Qed.

Lemma ztop_%(mid)s : forall k m p,
  Reach1 tm (zC_%(mid)s (repeat true k) m p) (zC_%(mid)s (repeat false k ++ [true]) m p).
Proof.
  intros k m p.
  apply (reach1_lift_l tm _ (zC_%(mid)s (repeat true k ++ [false]) m p)).
  { unfold zC_%(mid)s. rewrite bcells_app. cbn [bcells flat_map].
    rewrite <- !app_assoc. cbn [app].
    rewrite <- (lift_fixL_padn 2 StA (bcells [S0;S0] [S0;S1] (repeat true k) ++ [S0])).
    rewrite <- (lift_fixR_padn 2 StA _ S0 (S0 :: bcells [S0;S0] [S0;S1] (repeat true k) ++ [S0])).
    cbn [repeat app]. rewrite <- ?app_assoc. cbn [app]. reflexivity. }
  exact (zcarryC_%(mid)s k [] m p).
Qed.

Lemma zfireC_%(mid)s : forall t, ~ In t pins_%(mid)s -> forall n m p,
  Fires tm (zC_%(mid)s (repeat true (S n)) m p) t.
Proof.
  intros t Hnp n m p.
  apply (fire_lift tm _ (zst_%(mid)s n [] [])).
  { unfold zC_%(mid)s, zst_%(mid)s. rewrite !bcells_rep_true. cbn [app].
    rewrite <- (lift_fixL_padn 1 StA (rep [S0;S1] (S n) ++ [S0]) S0 (S0 :: rep [S0;S1] (S n) ++ [S0])).
    rewrite <- (lift_fixR_padn 2 StA ((rep [S0;S1] (S n) ++ [S0]) ++ repeat S0 1) S0
                  (S0 :: rep [S0;S1] (S n) ++ [S0])).
    cbn [repeat app]. rewrite <- ?app_assoc. cbn [app]. reflexivity. }
  destruct t as [q s]; destruct q, s; try (exfalso; apply Hnp; simpl; tauto).
%(firecases)s
Qed.
""" + ZZ1_BOARD,
)

ROWS = {'1RB0LA_0RC1RB_0LD0RB_1LD0LA': ZZ1,
        '1RB0LA_1LC0RB_1RD1LA_1LA1RC': ZZ2,
        '1RB1RC_0RC1RB_0LD0RB_1LD0LA': ZZ3}


def boot(spec, r, steps=200000):
    """(t, x): the first anchor visit past 2000 steps whose tape the row's
    decoder reads as the counter [x]"""
    tab = E.parse_tm(spec)
    tape, h, q = {}, 0, 0
    for t in range(steps):
        s = tape.get(h, 0)
        if q == r['q'] and s == 0 and t > 2000:
            cs = sorted(i for i, v in tape.items() if v)
            L = ''.join(str(tape.get(i, 0)) for i in range(h - 1, cs[0] - 1, -1))
            R = ''.join(str(tape.get(i, 0)) for i in range(h + 1, cs[-1] + 1))
            x = r['dec'](L, R)
            if x:
                return t, x
        w, d, nq = tab[(q, s)]
        tape[h] = w
        h += d
        q = nq
    raise NoClosure('no boot')


def emit_closure_zz(cert, tab, mid):
    r = cert['row']
    ctab = {k: (None if k in E.TR_PINS else v) for k, v in csim_parse(cert['spec']).items()}
    g = G2.Gen2(tab, mid, E.TR_PINS, ctab)
    names = {}
    try:
        for key, a, b in r['arms']:
            names[key] = g.arm(a, b, key)
    except NoClosure as e:
        return E.CLOSURE_NONE % e, None
    fires = {}
    for key, pre, reach, args in r['fire']:
        got = g.fires(names[key], mine=[w for w in g.want if w not in fires])
        for w, nm in got.items():
            fires[w] = (nm, pre, reach, args)
    miss = [w for w in g.want if w not in fires]
    if miss:
        return E.CLOSURE_NONE % NoClosure('fire arms miss %s' % miss), None
    firecases = '\n'.join(('  - apply (fire_back tm _ (%s)); [apply (%s)|].\n'
                           '    exact (%s %s).') % (pre, reach, nm, args)
                          for nm, pre, reach, args in (fires[w] for w in g.want))
    firecases = firecases % dict(mid=mid)
    body = r['coq'] % dict(mid=mid, firecases=firecases, **names)
    t0, x0 = cert['boot']
    xs = '[' + ';'.join('true' if v else 'false' for v in x0) + ']'
    body += """
Lemma zboot_%(mid)s :
  stepn tm %(t0)d InitES = Some (lift (gcfg zC_%(mid)s (%(x0)s, 0, 0))).
Proof.
  assert (H : match csteps tm %(t0)d c0 with
              | Some c => ceqb c (gcfg zC_%(mid)s (%(x0)s, 0, 0))
              | None => false end = true) by (vm_compute; reflexivity).
  destruct (csteps tm %(t0)d c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** The machine-level theorem, at the INSTRUCTION level, through
    [TopMapGTr.topmapg_neverqhtr]. *)
Theorem nqhtr_%(mid)s : NeverQuasiHaltsTr tm_%(mid)s.
Proof.
  exact (topmapg_neverqhtr tm_%(mid)s pins_%(mid)s zC_%(mid)s zG_%(mid)s zInv_%(mid)s
           zcarryI_%(mid)s ztopI_%(mid)s zGinv_%(mid)s zfire_%(mid)s %(x0)s 0 0
           ltac:(unfold GInv, zInv_%(mid)s; cbn; lia) %(t0)d zboot_%(mid)s).
Qed.
""" % dict(mid=mid, t0=t0, x0=xs)
    head = """
(** ** The closure: a zig-zag mirrored counter ([TopMapGTr], [TwoSideArmTr]) *)
From BBB4.Checkers Require Import LadderNest LadderCheckNestTr.
From BBB4.Counters Require Import NestCountTr PhBinCountTr TwoSideArmTr TopMapGTr.

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
    t0, x0 = boot(spec, r)
    cert = dict(spec=spec, closed=True, ladder=[], arms=[], row=r, boot=(t0, x0),
                family=dict(state='ABCD'[r['q']], head=0, side='R', other_side_cells=[],
                            digits=[list(r.get('Z', (0, 0))), list(r.get('O', (0, 1)))], near_head_prefix=[], terminator=[],
                            terminators_by_phase=[[]], n_phases=1, base=2, digit_len=2,
                            code='binary', value_step_per_anchor_visit=1),
                fill=dict(widens_by=1, target_prefix=[], target_fill_digit=0, target_suffix=[],
                          lands_in_phase=0))
    E.emit_closure = emit_closure_zz
    good, bad, cd = E.emit(cert, a.out)
    print('%s: closure %s' % (a.out, 'BUILT' if cd else 'not built'))
    return 0 if cd else 1


if __name__ == '__main__':
    sys.exit(main())
