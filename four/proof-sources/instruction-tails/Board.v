(** Four new instruction families; the common bound is only for the ledger. *)
From Coq Require Import List Arith Lia NArith.
From BBB24 Require Import Statement StatementTr Spec Bounds Census Bootstrap Closeout
 CertifiedBoard Pipeline CensusUnion.
From BBB24InstructionTails Require Import FiniteTails.
Import ListNotations.

Lemma s57_count_nat : forall n,D.sd_count n=N.to_nat n.
Proof. intros;unfold D.sd_count;reflexivity. Qed.
Lemma s77_count_nat : forall n,E.s77_count n=N.to_nat n.
Proof. intros;unfold E.s77_count;reflexivity. Qed.
Lemma counter_count_nat : forall n,C.fc_count n=N.to_nat n.
Proof. intros;unfold C.fc_count;reflexivity. Qed.
Lemma former_count_nat : forall n,B.sf_count n=N.to_nat n.
Proof. intros;unfold B.sf_count;reflexivity. Qed.

Lemma state_weaken_nat : forall tm a b,
 QHBound a tm -> a<=b -> QHBound b tm.
Proof. intros tm a b H Hab q s Hq;eapply Nat.le_trans;[exact(H q s Hq)|exact Hab]. Qed.
Lemma instruction_weaken_nat : forall tm a b,
 QHBoundTr a tm -> a<=b -> QHBoundTr b tm.
Proof. intros tm a b H Hab tg s Hq;eapply Nat.le_trans;[exact(H tg s Hq)|exact Hab]. Qed.

Definition boundN:N:=72057594037927936%N.
Definition board:list TM:=[D.sd_tm;E.s77_tm;C.fc_tm;M.sc_tm].

Lemma s57_run : NonHalt D.sd_tm /\ Bounds boundN boundN D.sd_tm.
Proof.
 split;[exact D.sd_nonhalt|split].
 - eapply state_weaken_nat;[exact D.sd_prefix_bound|].
   rewrite <-(s57_count_nat boundN);apply D.sd_count_le;unfold D.sd_stepsN,boundN;vm_compute;discriminate.
 - eapply instruction_weaken_nat;[exact s57_instruction_bound|].
   rewrite <-(s57_count_nat boundN);apply D.sd_count_le;unfold D.sd_stepsN,boundN;vm_compute;discriminate.
Qed.
Lemma s77_run : NonHalt E.s77_tm /\ Bounds boundN boundN E.s77_tm.
Proof.
 split;[exact E.s77_nonhalt|split].
 - eapply state_weaken_nat;[exact P.s77_exact_bound|].
   rewrite <-(s77_count_nat boundN);apply E.s77_count_le;unfold boundN;vm_compute;discriminate.
 - eapply instruction_weaken_nat;[exact s77_instruction_bound|].
   rewrite <-(s77_count_nat boundN);apply E.s77_count_le;unfold boundN;vm_compute;discriminate.
Qed.
Lemma finite_counter_run : NonHalt C.fc_tm /\ Bounds boundN boundN C.fc_tm.
Proof.
 split;[exact(proj1 T.fc_sound)|split].
 - eapply state_weaken_nat;[exact(proj2 T.fc_sound)|].
   rewrite <-(counter_count_nat boundN);apply C.fc_count_le;unfold T.fc_boundN,boundN;vm_compute;discriminate.
 - eapply instruction_weaken_nat;[exact finite_counter_instruction_bound|].
   rewrite <-(counter_count_nat boundN);apply C.fc_count_le;unfold boundN;vm_compute;discriminate.
Qed.
Lemma former_champion_run : NonHalt M.sc_tm /\ Bounds boundN boundN M.sc_tm.
Proof.
 split;[exact B.sf_nonhalt|split].
 - eapply state_weaken_nat;[exact F.sf_exact_bound|].
   rewrite <-(former_count_nat boundN);apply B.sf_count_le;unfold boundN;vm_compute;discriminate.
 - eapply instruction_weaken_nat;[exact former_champion_instruction_bound|].
   rewrite <-(former_count_nat boundN);apply B.sf_count_le;unfold boundN;vm_compute;discriminate.
Qed.

Lemma runs : forall family,In family board -> NonHalt family /\ Bounds boundN boundN family.
Proof.
 intros family[<-|[<-|[<-|[<-|Hbad]]]].
 - exact s57_run.
 - exact s77_run.
 - exact finite_counter_run.
 - exact former_champion_run.
 - contradiction.
Qed.
Lemma small_sound : BoardSound boundN boundN board.
Proof.
 intros family Hin tm Hle;destruct(runs family Hin)as[Hnh Hb].
 eapply extend_bounds;eauto.
Qed.
Lemma sound : BoardSound scoreN scoreN board.
Proof.
 intros family Hin tm Hle;eapply(bounds_weaken boundN boundN scoreN scoreN).
 - unfold boundN,scoreN;vm_compute;discriminate.
 - unfold boundN,scoreN;vm_compute;discriminate.
 - exact(small_sound family Hin tm Hle).
Qed.
Lemma nonhalt : forall family,In family board -> NonHalt family.
Proof. intros family Hin;exact(proj1(runs family Hin)). Qed.
Lemma pending_checked : forallb(pending_check 9 empty bootstrap)board=true.
Proof. vm_compute;reflexivity. Qed.
Lemma was_pending : forall family,In family board -> bootstrap_pending family.
Proof.
 intros family Hin;apply pending_check_sound.
 pose proof pending_checked as H;apply forallb_forall with(x:=family)in H;assumption.
Qed.
Print Assumptions sound.
