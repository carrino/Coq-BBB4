(** Exact token sweeps for the common B0-avoiding period-three core.
    No hypothesis is made about B0. *)
From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement CTape.
Import ListNotations.

Definition p3_raw (d:bool) : list Sym :=
 if d then [S1;S1;S0] else [S1;S0].
Definition p3_written (d:bool) : list Sym :=
 if d then [S1;S0;S1] else [S1;S1].
Definition p3_shifted (d:bool) : list Sym :=
 if d then [S0;S1;S1] else [S1;S1].
Fixpoint p3_code (f:bool->list Sym) (ds:list bool) : list Sym :=
 match ds with []=>[] | d::rest=>f d ++ p3_code f rest end.
Definition p3_R q L R : cconf := (q,(L,chd R,ctl R)).
Definition p3_L q L R : cconf := (q,(ctl L,chd L,R)).
Lemma p3_code_app : forall f a b,
 p3_code f (a++b) = p3_code f a ++ p3_code f b.
Proof. intros f a; induction a; intros b; cbn; [reflexivity|].
 rewrite IHa, app_assoc. reflexivity. Qed.
Lemma p3_code_length : forall ds,
 length(p3_code p3_written ds)=length(p3_code p3_raw ds).
Proof. induction ds as [|d ds IH]; cbn; [reflexivity|].
 destruct d; cbn; rewrite IH; reflexivity. Qed.
Lemma p3_code_length_rev : forall f ds,
 length(p3_code f (rev ds))=length(p3_code f ds).
Proof. intros f ds; induction ds as [|d ds IH]; cbn; [reflexivity|].
 rewrite p3_code_app, !app_length; cbn; rewrite IH, app_length; cbn; lia. Qed.
Lemma p3_shift_code : forall ds,
 S1 :: p3_code p3_shifted ds = p3_code p3_written ds ++ [S1].
Proof. induction ds as [|d ds IH]; cbn; [reflexivity|].
 destruct d; cbn in *; rewrite IH; reflexivity. Qed.

Section Core.
Variable tm:TM.
Hypotheses
 (HA0:tm StA S0=Some(mkTrans S1 DR StB))
 (HA1:tm StA S1=Some(mkTrans S0 DL StC))
 (HB1:tm StB S1=Some(mkTrans S1 DR StD))
 (HC0:tm StC S0=Some(mkTrans S1 DL StA))
 (HC1:tm StC S1=Some(mkTrans S1 DL StC))
 (HD0:tm StD S0=Some(mkTrans S1 DR StB))
 (HD1:tm StD S1=Some(mkTrans S0 DR StA)).
Local Ltac steps := progress (cbn [p3_R p3_L p3_raw p3_written p3_shifted
 csteps cstep ctape_move t_dir t_write t_next chd ctl length app]; rewrite ?HA0,?HA1,?HB1,?HC0,?HC1,?HD0,?HD1;
 cbn [csteps cstep ctape_move t_dir t_write t_next chd ctl length app]).

Lemma p3_right_token : forall d L R,
 csteps tm (length(p3_raw d)) (p3_R StB L (p3_raw d++R)) =
 Some(p3_R StB (p3_written d++L) R).
Proof. intros d L R; destruct d; repeat steps; reflexivity. Qed.
Lemma p3_left_token : forall d L R,
 csteps tm (length(p3_written d)) (p3_L StC (p3_written d++L) R) =
 Some(p3_L StC L (p3_shifted d++R)).
Proof. intros d L R; destruct d; repeat steps; reflexivity. Qed.

Lemma p3_right_tokens : forall ds L R,
 csteps tm (length(p3_code p3_raw ds)) (p3_R StB L (p3_code p3_raw ds++R)) =
 Some(p3_R StB (p3_code p3_written (rev ds)++L) R).
Proof.
 induction ds as [|d ds IH]; intros L R; [reflexivity|].
 cbn [p3_code rev]. rewrite app_length, <-app_assoc, csteps_add, p3_right_token.
 rewrite IH, p3_code_app. cbn [p3_code]. rewrite app_nil_r, app_assoc. reflexivity.
Qed.
Lemma p3_left_tokens : forall ds L R,
 csteps tm (length(p3_code p3_written ds)) (p3_L StC (p3_code p3_written ds++L) R) =
 Some(p3_L StC L (p3_code p3_shifted (rev ds)++R)).
Proof.
 induction ds as [|d ds IH]; intros L R; [reflexivity|].
 cbn [p3_code rev]. rewrite app_length, <-app_assoc, csteps_add, p3_left_token.
 rewrite IH, p3_code_app. cbn [p3_code]. rewrite app_nil_r, app_assoc. reflexivity.
Qed.
Lemma p3_turn : forall L R,
 csteps tm 5 (p3_R StB L (S1::S1::S1::R)) =
 Some(p3_L StC L (S0::S1::S0::R)).
Proof. intros L R; repeat steps; reflexivity. Qed.
Lemma p3_finish : forall R,
 csteps tm 2 (p3_L StC [S1] R) = Some(StA,([],S0,S1::S1::R)).
Proof. intro R; repeat steps; reflexivity. Qed.

Theorem p3_round : forall ds R,
 csteps tm (2*length(p3_code p3_raw ds)+8)
 (StA,([],S0,p3_code p3_raw ds++S1::S1::S1::R)) =
 Some(StA,([],S0,S1::p3_code p3_written ds++S1::S0::S1::S0::R)).
Proof.
 intros ds R.
 replace (2*length(p3_code p3_raw ds)+8) with
 (1+(length(p3_code p3_raw ds)+(5+(length(p3_code p3_written(rev ds))+2))))
 by (rewrite p3_code_length_rev,p3_code_length; lia).
 rewrite csteps_add. steps.
 change (csteps tm (length(p3_code p3_raw ds)+(5+(length(p3_code p3_written(rev ds))+2)))
   (p3_R StB [S1] (p3_code p3_raw ds++S1::S1::S1::R)) =
   Some(StA,([],S0,S1::p3_code p3_written ds++S1::S0::S1::S0::R))).
 rewrite csteps_add, p3_right_tokens, csteps_add, p3_turn,
 csteps_add, p3_left_tokens, rev_involutive, p3_finish.
 f_equal. f_equal. f_equal.
 f_equal.
 change ((S1::p3_code p3_shifted ds)++(S0::S1::S0::R) =
 p3_code p3_written ds++S1::S0::S1::S0::R).
 rewrite p3_shift_code, <-app_assoc. reflexivity.
Qed.
End Core.
