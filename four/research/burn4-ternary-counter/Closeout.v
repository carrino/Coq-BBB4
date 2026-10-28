From Coq Require Import Arith Lia List NArith.
From BBB24 Require Import Statement StatementTr Spec CTape Bounds Census Bootstrap Closeout CertifiedBoard.
From BBB24Burn4Ternary Require Import Counter Tail FiveTargets.
Import ListNotations.
Lemma recurrent_except_B0_B3:forall tg,tg<>(StB,S0)->tg<>(StB,S3)->
 forall N,exists k,N<=k /\ FiresAt family tg k.
Proof.
 intros[q h] H0 H3 N;destruct q,h;
 try(exfalso;apply H0;reflexivity);try(exfalso;apply H3;reflexivity).
 all:try exact(tc_A0_recurrent N).
 all:apply(proj2 five_sound);unfold targets;simpl;tauto.
Qed.
Theorem exact_bounds:NonHalt family /\ Bounds 0%N 4%N family.
Proof.
 split;[exact(proj1 five_sound)|]. unfold Bounds;cbn;split.
 - intros q s[Hv Hquiet].
   destruct(recurrent_except_B0_B3(q,S1)ltac:(discriminate)ltac:(discriminate)(S s))as(k&Hk&Hfire).
   exfalso;apply(Hquiet k);[lia|eapply fires_visits;exact Hfire].
 - intros tg s[Hfire Hquiet].
   destruct(lt_dec s 4);[lia|].
   assert(Hcases:tg=(StB,S0) \/ tg=(StB,S3) \/ (tg<>(StB,S0) /\ tg<>(StB,S3))).
   {destruct tg as[q h];destruct q,h;intuition congruence. }
   destruct Hcases as[->|[->|[H0 H3]]].
   + exfalso;apply(tc_bad_quiet S0 ltac:(auto) s);[lia|exact Hfire].
   + exfalso;apply(tc_bad_quiet S3 ltac:(auto) s);[lia|exact Hfire].
   + destruct(recurrent_except_B0_B3 tg H0 H3(S s))as(k&Hk&Hfire').
     exfalso;apply(Hquiet k);[lia|exact Hfire'].
Qed.
Theorem exact_instruction_score:QuietAfterTr family(StB,S3)3.
Proof. exact tc_B3_exact_last. Qed.
Theorem instruction_bound_is_tight:~QHBoundTr 3 family.
Proof. intro H;specialize(H(StB,S3)3 exact_instruction_score);lia. Qed.
Definition board:list TM:=[family].
Lemma small_sound:BoardSound 0%N 4%N board.
Proof.
 intros f[<-|Hfalse]tm Hle;[|contradiction].
 destruct exact_bounds as[Hnh Hb];eapply extend_bounds;eauto.
Qed.
Lemma sound:BoardSound scoreN scoreN board.
Proof.
 intros f Hin tm Hle;eapply(bounds_weaken 0%N 4%N scoreN scoreN tm).
 - vm_compute;discriminate.
 - vm_compute;discriminate.
 - exact(small_sound f Hin tm Hle).
Qed.
Lemma pending_checked:forallb(pending_check 9 empty bootstrap)board=true.
Proof. vm_compute;reflexivity. Qed.
Lemma was_pending:forall f,In f board->bootstrap_pending f.
Proof.
 intros f Hin;apply pending_check_sound.
 pose proof pending_checked as H;apply forallb_forall with(x:=f)in H;assumption.
Qed.
Print Assumptions exact_bounds.
