From Coq Require Import Arith Lia List NArith.
From BBB24 Require Import Statement StatementTr Spec CTape Bounds Census Bootstrap Closeout CertifiedBoard.
From BBB24Burn3Tail Require Import TailInvariant SevenTargets.
Import ListNotations.
Lemma recurrent_except_B1:forall tg,tg<>(StB,S1) -> forall N,exists k,N<=k /\ FiresAt family tg k.
Proof.
 intros [q h] H N;apply(proj2 seven_sound (q,h));unfold targets;destruct q,h;simpl in *;intuition congruence.
Qed.
Theorem exact_bounds:NonHalt family /\ Bounds 0%N 10%N family.
Proof.
 split;[exact(proj1 seven_sound)|]. unfold Bounds;cbn;split.
 - intros q s[Hv Hquiet].
   destruct(recurrent_except_B1(q,S0)ltac:(discriminate)(S s))as(k&Hk&Hfire).
   exfalso;apply(Hquiet k);[lia|eapply fires_visits;exact Hfire].
 - intros tg s[Hfire Hquiet].
   destruct(instr_eqb tg(StB,S1))eqn:Etg.
   + apply instr_eqb_spec in Etg;subst tg.
     destruct(lt_dec s 10);[lia|].
     exfalso;apply(ti_B1_quiet s);[lia|exact Hfire].
   + assert(Hneq:tg<>(StB,S1)).
     {intro E;subst tg;discriminate. }
     destruct(recurrent_except_B1 tg Hneq(S s))as(k&Hk&Hfire').
     exfalso;apply(Hquiet k);[lia|exact Hfire'].
Qed.
Theorem exact_instruction_score:QuietAfterTr family(StB,S1)9.
Proof. exact ti_B1_exact_last. Qed.
Theorem instruction_bound_is_tight : ~ QHBoundTr 9 family.
Proof.
 intro H;specialize(H (StB,S1) 9 exact_instruction_score);lia.
Qed.
Definition board:list TM:=[family].
Lemma small_sound:BoardSound 0%N 10%N board.
Proof.
 intros f[<-|Hfalse]tm Hle;[|contradiction].
 destruct exact_bounds as[Hnh Hb];eapply extend_bounds;eauto.
Qed.
Lemma sound:BoardSound scoreN scoreN board.
Proof.
 intros f Hin tm Hle;eapply(bounds_weaken 0%N 10%N scoreN scoreN tm).
 - vm_compute;discriminate.
 - vm_compute;discriminate.
 - exact(small_sound f Hin tm Hle).
Qed.
Lemma pending_checked:forallb(pending_check 9 empty bootstrap)board=true.
Proof. vm_compute;reflexivity. Qed.
Lemma was_pending:forall f,In f board -> bootstrap_pending f.
Proof.
 intros f Hin;apply pending_check_sound.
 pose proof pending_checked as H;apply forallb_forall with(x:=f)in H;assumption.
Qed.
Print Assumptions exact_bounds.
