(** Transition-level closeout batch AST_30: two implementations of the
    same moving binary-word transducer beside a periodic bouncer.
    Collected by tools/closeouttr/gen_closeout_tr.py. *)
From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Census Require Import Deferred_Defs.
From BBB4.CloseoutTr Require Import CloseoutKitTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
From BBB4.Counters Require Import WTape ValueLapTr MovingTokenTr TokenSweepTr MovingSweepTr.
Import ListNotations.

Section MovingPair.
Variable tm : TM.
Variable kc : nat.
Hypothesis HA0 : tm StA S0 = Some (mkTrans S0 DR StB).
Hypothesis HA1 : tm StA S1 = Some (mkTrans S0 DR StA).
Hypothesis HB0 : tm StB S0 = Some (mkTrans S1 DL StC).
Hypothesis HB1 : tm StB S1 = Some (mkTrans S1 DR StA).
Hypothesis HC0 : tm StC S0 = Some (mkTrans S0 DL StD).
Hypothesis HD0 : tm StD S0 = Some (mkTrans S1 DR StA).
Hypothesis HD1 : tm StD S1 = Some (mkTrans S1 DL StB).
Hypothesis HC1 : forall L R,
  csteps tm kc (StC,(L,S1,S1::R)) =
  Some (StC,(ctl L,chd L,S1::S1::R)).

Local Definition anchor (n : nat) (w : list Sym) : cconf :=
  (StC,(w,S1,rep [S1;S1;S0] (S n) ++ [S1])).
Local Definition middle (n : nat) (w : list Sym) : cconf :=
  (StA,(mv_f w,S1,rep [S1;S0;S1] (S n))).
Hypothesis Hboot : csteps tm 11 c0 = Some (anchor 0 []).

Local Lemma first_phase : forall n w,
  csteps tm (mv_fcost kc w) (anchor n w) = Some (middle n w).
Proof.
  intros n w. unfold anchor, middle. rewrite token_sweep_rotation.
  apply mv_f_run; assumption.
Qed.

Local Lemma lap : forall n w,
  csteps tm (mv_fcost kc w + (12*S n+12)) (anchor n w) =
  Some (anchor (S n) (mv_f w)).
Proof.
  intros n w. rewrite csteps_add, first_phase. unfold middle, anchor.
  apply moving_sweep; assumption.
Qed.

Local Lemma fire : forall n w t,
  exists k c, csteps tm k (anchor n w) = Some c /\ cinstr c = t.
Proof.
  intros n w t. destruct (instr_eqb t (StC,S1)) eqn:E.
  - apply instr_eqb_spec in E. subst t.
    exists 0, (anchor n w). split; reflexivity.
  - assert (Hne : t <> (StC,S1)).
    { intro H; subst t. discriminate E. }
    assert (Hfire : forall k L t, t <> (StC,S1) ->
      exists j c, csteps tm j (StA,(L,S1,rep [S1;S0;S1] k)) =
      Some c /\ cinstr c = t).
    { apply moving_sweep_fire; assumption. }
    destruct (Hfire (S n) (mv_f w) t Hne) as (j & c & Hj & Ht).
    exists (mv_fcost kc w+j), c. split; [|exact Ht].
    rewrite csteps_add, first_phase. exact Hj.
Qed.

Local Lemma moving_pair_covers : coversTr tm.
Proof.
  apply coversTr_nqh.
  apply (value_lap_neverqhtr tm (list Sym) mv_f anchor []).
  - exists 11. rewrite <- lift_c0. exact (csteps_lift _ _ _ _ Hboot).
  - intros n w. exists (mv_fcost kc w+(12*S n+12)), (anchor (S n) (mv_f w)).
    split; [apply lap|]. split; [reflexivity|lia].
  - exact fire.
Qed.
End MovingPair.

(* spec 0RB0RA_1LC1RA_0LD1LC_1RA1LB *)
Definition r_AST_30_0000 : list (option Trans) :=
  [t0RB;t0RA;t1LC;t1RA;t0LD;t1LC;t1RA;t1LB].

Lemma cv_AST_30_0000 : coversTr (row_to_tm r_AST_30_0000).
Proof.
  apply (moving_pair_covers (row_to_tm r_AST_30_0000) 1); try reflexivity.
Qed.

(* spec 0RB0RA_1LC1RA_0LD0RD_1RA1LB *)
Definition r_AST_30_0001 : list (option Trans) :=
  [t0RB;t0RA;t1LC;t1RA;t0LD;t0RD;t1RA;t1LB].

Lemma cv_AST_30_0001 : coversTr (row_to_tm r_AST_30_0001).
Proof.
  apply (moving_pair_covers (row_to_tm r_AST_30_0001) 3); try reflexivity.
Qed.

Definition cbtrows_AST_30 : list (list (option Trans)) :=
  [r_AST_30_0000;r_AST_30_0001].

Lemma cbt_AST_30_covers : Forall coversTr (map row_to_tm cbtrows_AST_30).
Proof.
  exact (Forall_cons _ cv_AST_30_0000
    (Forall_cons _ cv_AST_30_0001 (Forall_nil _))).
Qed.
