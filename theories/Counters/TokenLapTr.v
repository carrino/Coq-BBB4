(** * Complete token laps at arbitrary bouncer lengths.

    The original blank-start example has an odd block count.  These
    lemmas also admit an even block count and arbitrary counter words,
    so the same proof applies after a different initial-state boot. *)
From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
From BBB4.Counters Require Import WTape MutualTokenTr TokenSweepTr MovingTokenTr MovingSweepTr.
Import ListNotations.

Definition tkl_anchor (k : nat) (w : list mt_digit) : cconf :=
  (StC,(mt_encode w,S1,rep [S1;S1;S0] k ++ [S1])).
Definition mvl_anchor (k : nat) (w : list Sym) : cconf :=
  (StC,(w,S1,rep [S1;S1;S0] k ++ [S1])).

Section TokenLap.
Variable tm : TM.
Hypothesis HA0 : tm StA S0 = Some (mkTrans S0 DR StB).
Hypothesis HA1 : tm StA S1 = Some (mkTrans S0 DR StA).
Hypothesis HB0 : tm StB S0 = Some (mkTrans S1 DL StC).
Hypothesis HB1 : tm StB S1 = Some (mkTrans S1 DR StA).
Hypothesis HC0 : tm StC S0 = Some (mkTrans S0 DL StD).
Hypothesis HC1 : tm StC S1 = Some (mkTrans S0 DL StC).
Hypothesis HD0 : tm StD S0 = Some (mkTrans S1 DL StA).
Hypothesis HD1 : tm StD S1 = Some (mkTrans S1 DL StB).

Lemma token_finish_any : forall k X,
  csteps tm (6*k+6) (StB,(X,S1,rep [S1;S1;S0] k ++ [S1])) =
  Some (StA,(X,S1,rep [S1;S0;S1] (S k))).
Proof.
  intros k X. rewrite token_sweep_rotation.
  replace (6*k+6) with (1+(6*k+5)) by lia. rewrite csteps_add.
  assert (E : csteps tm 1 (StB,(X,S1,S1::rep [S1;S0;S1] k)) =
    Some (StA,(S1::X,S1,rep [S1;S0;S1] k))).
  { cbn [csteps cstep]. rewrite HB1. reflexivity. }
  rewrite E. apply token_sweep_first; assumption.
Qed.

Lemma token_first_any : forall k w,
  csteps tm (6*k+18+6*mt_depth w) (tkl_anchor k w) =
  Some (StA,(mt_encode (mt_succ w),S1,rep [S1;S0;S1] (S k))).
Proof.
  intros k w. unfold tkl_anchor.
  replace (6*k+18+6*mt_depth w) with ((12+6*mt_depth w)+(6*k+6)) by lia.
  rewrite csteps_add.
  rewrite (mt_token_phase tm StA StB StC StD HA0 HA1 HB0 HB1 HC0 HC1 HD0 HD1).
  apply token_finish_any.
Qed.

Lemma token_lap : forall k w,
  csteps tm (18*k+44+6*mt_depth w) (tkl_anchor k w) =
  Some (tkl_anchor (k+2) (mt_succ w)).
Proof.
  intros k w.
  replace (18*k+44+6*mt_depth w) with
    ((6*k+18+6*mt_depth w)+((6*S k+5)+(6*S k+9))) by lia.
  rewrite csteps_add, token_first_any, csteps_add.
  destruct (mt_succ_head w) as (Y & HY). rewrite HY.
  assert (Hfirst := token_sweep_first tm HA0 HA1 HB0 HB1 HC0 HD0 HD1 (S k) (S0::Y)).
  rewrite Hfirst. cbn [chd ctl].
  assert (Hsecond := token_sweep_second tm HA0 HA1 HB0 HB1 HC0 HD1 (S k) Y).
  rewrite Hsecond. unfold tkl_anchor. rewrite HY.
  replace (k+2) with (S (S k)) by lia. reflexivity.
Qed.

Lemma token_lap_fire : forall k w t,
  exists j c, csteps tm j (tkl_anchor k w) = Some c /\ cinstr c = t.
Proof.
  intros k w t. destruct (instr_eqb t (StC,S1)) eqn:E.
  - apply instr_eqb_spec in E. subst t. exists 0, (tkl_anchor k w). split; reflexivity.
  - assert (Hne : t <> (StC,S1)) by (intro H; subst t; discriminate).
    destruct (token_sweep_fire tm HA0 HA1 HB0 HB1 HC0 HD1
      k (mt_encode (mt_succ w)) t Hne) as (j & c & H & Hi).
    exists ((6*k+18+6*mt_depth w)+j), c. split; [|exact Hi].
    rewrite csteps_add, token_first_any. exact H.
Qed.
End TokenLap.

Section MovingLap.
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
  csteps tm kc (StC,(L,S1,S1::R)) = Some (StC,(ctl L,chd L,S1::S1::R)).

Lemma moving_first_any : forall k w,
  csteps tm (mv_fcost kc w) (mvl_anchor k w) =
  Some (StA,(mv_f w,S1,rep [S1;S0;S1] k)).
Proof.
  intros k w. unfold mvl_anchor. rewrite token_sweep_rotation.
  apply mv_f_run; assumption.
Qed.

Lemma moving_lap : forall k w,
  csteps tm (mv_fcost kc w+(12*k+12)) (mvl_anchor k w) =
  Some (mvl_anchor (S k) (mv_f w)).
Proof.
  intros k w. rewrite csteps_add, moving_first_any. unfold mvl_anchor.
  apply moving_sweep; assumption.
Qed.

Lemma moving_lap_fire : forall k w t,
  exists j c, csteps tm j (mvl_anchor k w) = Some c /\ cinstr c = t.
Proof.
  intros k w t. destruct (instr_eqb t (StC,S1)) eqn:E.
  - apply instr_eqb_spec in E. subst t. exists 0, (mvl_anchor k w). split; reflexivity.
  - assert (Hne : t <> (StC,S1)) by (intro H; subst t; discriminate).
    destruct (moving_sweep_fire tm HA0 HA1 HB0 HB1 HC0 HD0 HD1
      k (mv_f w) t Hne) as (j & c & H & Hi).
    exists (mv_fcost kc w+j), c. split; [|exact Hi].
    rewrite csteps_add, moving_first_any. exact H.
Qed.
End MovingLap.
