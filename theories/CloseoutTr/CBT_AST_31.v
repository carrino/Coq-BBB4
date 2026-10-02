(** Transition-level closeout batch AST_31: a moving frontier counter.
    Its non-firing carries decrease a lexicographic count of ones and
    adjacent pairs of ones.  Collected by gen_closeout_tr.py. *)
From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Census Require Import Deferred_Defs.
From BBB4.CloseoutTr Require Import CloseoutKitTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
From BBB4.Counters Require Import ValueLapTr MovingTokenTr FrontierTokenTr.
Import ListNotations.

(* spec 0RB0RA_1RC1RA_0LD1LC_1RA1LB *)
Definition r_AST_31_0000 : list (option Trans) :=
  [t0RB;t0RA;t1RC;t1RA;t0LD;t1LC;t1RA;t1LB].
Local Definition tm := row_to_tm r_AST_31_0000.

Local Lemma lap : forall w,
  csteps tm (fr_gcost w+8) (fr_anchor w) = Some (fr_anchor (mv_g w)).
Proof. apply fr_lap; reflexivity. Qed.

Local Lemma hits : forall w q s, fr_hits tm q s (fr_anchor w).
Proof. apply fr_all_hits; reflexivity. Qed.

Lemma cv_AST_31_0000 : coversTr (row_to_tm r_AST_31_0000).
Proof.
  apply coversTr_nqh.
  apply (value_lap_neverqhtr tm (list Sym) mv_g
    (fun _ w => fr_anchor w) [S1;S0;S1]).
  - exists 17. rewrite <- lift_c0. apply csteps_lift. reflexivity.
  - intros n w. exists (fr_gcost w+8), (fr_anchor (mv_g w)).
    split; [apply lap|]. split; [reflexivity|lia].
  - intros n w [q s]. destruct (hits w q s) as (j & L & R & H).
    exists j, (q,(L,s,R)). split; [exact H|reflexivity].
Qed.

Definition cbtrows_AST_31 : list (list (option Trans)) := [r_AST_31_0000].

Lemma cbt_AST_31_covers : Forall coversTr (map row_to_tm cbtrows_AST_31).
Proof. exact (Forall_cons _ cv_AST_31_0000 (Forall_nil _)). Qed.
