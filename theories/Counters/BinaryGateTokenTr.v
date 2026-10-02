(** * A binary carry split across three periodic sweeps.

    Digits 00 and 01 have a fixed 010 terminator.  The first carry pass
    produces a run of ones; the second rewrites it to the successor word.
    Both passes are structural inductions over an arbitrary digit word. *)
From Coq Require Import Arith Lia List PArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Checkers Require Import LapDecider.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
From BBB4.Counters Require Import WTape LapGlueTr ValueLapTr.
Import ListNotations.

Fixpoint bg_word (w : list Sym) : list Sym :=
 match w with []=>[S0;S1;S0] | d::w=>S0::d::bg_word w end.
Fixpoint bg_next (w : list Sym) : list Sym :=
 match w with []=>[S0] | S0::w=>S1::w | S1::w=>S0::bg_next w end.
Fixpoint bg_mid (w : list Sym) : list Sym :=
 match w with []=>[S1;S1;S1;S0] | S0::w=>S1::S0::bg_word w
 | S1::w=>S1::S1::bg_mid w end.
Fixpoint bg_c1 (w : list Sym) : nat :=
 match w with []=>8 | S0::_=>4 | S1::w=>4+bg_c1 w end.
Fixpoint bg_c2 (w : list Sym) : nat :=
 match w with []=>10 | S0::_=>6 | S1::w=>4+bg_c2 w end.
Definition bg_anchor n w : cconf :=
 (StD,(S0::S1::bg_word w,S1,rep [S1;S0;S1] n)).
Definition bg_cost n w := 18*n+26+bg_c1 w+bg_c2 w.

Definition bg_s1 := mkC StD (sflat [S0;S1]) S1 (mkS [] [S1;S0;S1] 1 0 []).
Definition bg_e1 := mkC StA (sflat []) S1 (mkS [] [S1;S0;S1] 1 1 []).
Definition bg_ch1 := [(SCycR 3); (SWinR 2); (SCycL 3 0); (SWin 2); (SRotR 1); (SFoldR 1)].
Definition bg_s2 := mkC StD (sflat []) S1 (mkS [] [S1;S0;S1] 1 0 []).
Definition bg_e2 := mkC StC (sflat []) S1 (mkS [S1] [S1;S0;S1] 1 0 []).
Definition bg_ch2 := [(SCycR 3); (SWinR 2); (SCycL 3 0); (SRotR 1)].
Definition bg_s3 := mkC StD (sflat [S0]) S0 (mkS [S1] [S1;S0;S1] 1 0 []).
Definition bg_e3 := mkC StD (sflat [S0;S1;S0]) S1 (mkS [] [S1;S0;S1] 1 0 []).
Definition bg_ch3 := [(SWin 1); (SCycR 3); (SWinR 2); (SCycL 3 0); (SWin 4); (SRotR 1); (SWin 1)].
Definition bg_f3 := mkC StD (sflat [S0]) S0 (mkS [S1] [S1;S0;S1] 1 1 []).

Section BinaryGate.
Variable tm : TM.
Hypothesis HA0 : tm StA S0 = Some (mkTrans S0 DR StB).
Hypothesis HA1 : tm StA S1 = Some (mkTrans S1 DL StC).
Hypothesis HB0 : tm StB S0 = Some (mkTrans S1 DL StC).
Hypothesis HB1 : tm StB S1 = Some (mkTrans S1 DR StD).
Hypothesis HC0 : tm StC S0 = Some (mkTrans S1 DL StA).
Hypothesis HC1 : tm StC S1 = Some (mkTrans S0 DL StC).
Hypothesis HD0 : tm StD S0 = Some (mkTrans S0 DR StD).
Hypothesis HD1 : tm StD S1 = Some (mkTrans S1 DR StB).
Local Ltac bg_compute :=
 cbn [Nat.add csteps cstep ctape_move chd ctl t_next t_dir t_write];
 repeat (first [rewrite HA0|rewrite HA1|rewrite HB0|rewrite HB1|
                rewrite HC0|rewrite HC1|rewrite HD0|rewrite HD1];
         cbn [Nat.add csteps cstep ctape_move chd ctl t_next t_dir t_write]);
 reflexivity.

Lemma bg_carry1 : forall w R,
 csteps tm (bg_c1 w) (StA,(bg_word w,S1,R)) =
 Some (StD,(bg_mid w,S1,R)).
Proof.
 induction w as [|d w IH];intro R;[cbn [bg_c1 bg_word bg_mid];bg_compute|].
 destruct d;cbn [bg_c1 bg_word bg_mid];[bg_compute|].
 replace (4+bg_c1 w) with (2+(bg_c1 w+2)) by lia.
 rewrite csteps_add.
 assert (H : csteps tm 2 (StA,(S0::S1::bg_word w,S1,R)) =
   Some (StA,(bg_word w,S1,S1::S1::R))) by bg_compute.
 rewrite H,csteps_add,IH. bg_compute.
Qed.

Lemma bg_carry2 : forall w R,
 csteps tm (bg_c2 w) (StC,(bg_mid w,S1,R)) =
 Some (StD,(bg_word (bg_next w),S0,R)).
Proof.
 induction w as [|d w IH];intro R;[cbn [bg_c2 bg_word bg_mid bg_next];bg_compute|].
 destruct d;cbn [bg_c2 bg_word bg_mid bg_next].
 - destruct w;cbn [bg_word];bg_compute.
 -
 replace (4+bg_c2 w) with (2+(bg_c2 w+2)) by lia.
 rewrite csteps_add.
 assert (H : csteps tm 2 (StC,(S1::S1::bg_mid w,S1,R)) =
   Some (StC,(bg_mid w,S1,S0::S0::R))) by bg_compute.
 rewrite H,csteps_add,IH. bg_compute.
Qed.

Hypothesis Hs1 : srun tm false true bg_ch1 bg_s1 = Some (bg_e1,6,4).
Hypothesis Hs2 : srun tm false true bg_ch2 bg_s2 = Some (bg_e2,6,2).
Hypothesis Hs3 : srun tm false true bg_ch3 bg_s3 = Some (bg_e3,6,8).

Local Ltac bg_den n H :=
 unfold cden,sden,sflat,bg_s1,bg_e1,bg_s2,bg_e2,bg_s3,bg_e3,bg_f3 in H;
 cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post] in H;
 rewrite rep_nil in H;cbn [app] in H;
 repeat rewrite app_nil_r in H;
 replace (1*n+0) with n in H by lia;
 try replace (1*n+1) with (S n) in H by lia.

Lemma bg_sweep1 : forall n w,
 csteps tm (6*n+4) (StD,(S0::S1::w,S1,rep [S1;S0;S1] n)) =
 Some (StA,(w,S1,rep [S1;S0;S1] (S n))).
Proof.
 intros n w. pose proof (srun_sound tm false true bg_ch1 bg_s1 bg_e1 6 4 Hs1
   w [] n ltac:(discriminate) ltac:(reflexivity)) as H.
 bg_den n H. exact H.
Qed.
Lemma bg_sweep2 : forall n w,
 csteps tm (6*n+2) (StD,(w,S1,rep [S1;S0;S1] n)) =
 Some (StC,(w,S1,S1::rep [S1;S0;S1] n)).
Proof.
 intros n w. pose proof (srun_sound tm false true bg_ch2 bg_s2 bg_e2 6 2 Hs2
   w [] n ltac:(discriminate) ltac:(reflexivity)) as H.
 bg_den n H. exact H.
Qed.
Lemma bg_sweep3 : forall n w,
 csteps tm (6*n+8) (StD,(S0::w,S0,S1::rep [S1;S0;S1] n)) =
 Some (StD,(S0::S1::S0::w,S1,rep [S1;S0;S1] n)).
Proof.
 intros n w. pose proof (srun_sound tm false true bg_ch3 bg_s3 bg_e3 6 8 Hs3
   w [] n ltac:(discriminate) ltac:(reflexivity)) as H.
 bg_den n H. exact H.
Qed.

Lemma bg_word_zero : forall w, exists v, bg_word w = S0::v.
Proof. intros [|d w];eexists;reflexivity. Qed.

Lemma bg_lap : forall n w,
 csteps tm (bg_cost n w) (bg_anchor n w) = Some (bg_anchor (S n) (bg_next w)).
Proof.
 intros n w. unfold bg_cost,bg_anchor.
 replace (18*n+26+bg_c1 w+bg_c2 w) with
   ((6*n+4)+(bg_c1 w+((6*S n+2)+(bg_c2 w+(6*S n+8))))) by lia.
 rewrite csteps_add,bg_sweep1,csteps_add,bg_carry1,csteps_add,bg_sweep2,
   csteps_add,bg_carry2.
 destruct (bg_word_zero (bg_next w)) as [v Hv]. rewrite Hv. apply bg_sweep3.
Qed.

Hypothesis Hfires : forall t, t<>(StA,S1) -> exists ch,
 srun_instr tm false true ch bg_f3 = Some t.

Lemma bg_fire : forall n w t, exists j c,
 csteps tm j (bg_anchor n w) = Some c /\ cinstr c = t.
Proof.
 intros n w [q s]. destruct (instr_eqb (q,s) (StA,S1)) eqn:E.
 - apply instr_eqb_spec in E. rewrite E.
   exists (6*n+4),(StA,(bg_word w,S1,rep [S1;S0;S1] (S n))).
   split;[apply bg_sweep1|reflexivity].
 - assert (Et : (q,s)<>(StA,S1)) by (intro H;rewrite H in E;discriminate).
   destruct (Hfires (q,s) Et) as [ch Hch].
   destruct (bg_word_zero (bg_next w)) as [v Hv].
   assert (Hden : forall x, cden v [] x bg_f3 =
     (StD,(S0::v,S0,S1::rep [S1;S0;S1] (S x)))).
   { intro x. unfold cden,sden,sflat,bg_f3.
     cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
     rewrite rep_nil. cbn [app]. rewrite app_nil_r.
     replace (1*x+1) with (S x) by lia. reflexivity. }
   destruct (fire_of_run_instr tm (fun _ => (StD,(S0::v,S0,S1::rep [S1;S0;S1] (S n))))
     false true ch bg_f3 xH n v [] (q,s) Hch ltac:(discriminate) ltac:(reflexivity)
     (eq_sym (Hden n))) as (j&c&Hj&Hi).
   exists ((6*n+4)+(bg_c1 w+((6*S n+2)+(bg_c2 w+j)))),c. split;[|exact Hi].
   unfold bg_anchor.
   rewrite csteps_add,bg_sweep1,csteps_add,bg_carry1,csteps_add,bg_sweep2,
     csteps_add,bg_carry2,Hv. exact Hj.
Qed.
End BinaryGate.
