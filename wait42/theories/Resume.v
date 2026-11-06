(** Resume a checked frontier using additional quantitative leaf certificates.
    Every rejected or unknown node remains an explicit completion obligation. *)
From Coq Require Import Arith Bool List NArith.
From BBB4 Require Import BBB4_Statement BBB4_Spec.
From BBB4.Census Require Import TNF_QH.
From BBBWait42 Require Import Spec Census Run Batch.
Import ListNotations.

Definition waiting_checker_sound (B w : nat) (f : TM -> bool) :=
 forall tm, f tm = true -> NonHalt tm /\ WindowBound tm B w.

Definition residual_nodes (f : TM -> bool) (nodes : list TNF_Node) :=
 filter (fun x => negb (f (node_tm x))) nodes.

Lemma residual_nodes_spec : forall f nodes x,
 In x (residual_nodes f nodes) <-> In x nodes /\ f (node_tm x) = false.
Proof.
 intros f nodes x; unfold residual_nodes; rewrite filter_In.
 rewrite Bool.negb_true_iff; reflexivity.
Qed.

Theorem resume_nodes_sound : forall B w D f nodes,
 waiting_checker_sound B w f ->
 (forall x, In x (residual_nodes f nodes) -> Census.NodeDecided B w D (node_tm x)) ->
 forall x, In x nodes -> Census.NodeDecided B w D (node_tm x).
Proof.
 intros B w D f nodes Hsound Hres x Hin.
 destruct (f (node_tm x)) eqn:Hcheck.
 - destruct (Hsound _ Hcheck) as [HN HW].
   apply Census.node_decided_leaf; assumption.
 - apply Hres; apply residual_nodes_spec; auto.
Qed.

(** Independent finite checkers may be combined without weakening the contract. *)
Lemma waiting_checker_or_sound : forall B w f g,
 waiting_checker_sound B w f -> waiting_checker_sound B w g ->
 waiting_checker_sound B w (fun tm => f tm || g tm).
Proof.
 intros B w f g Hf Hg tm H; apply orb_true_iff in H as [H|H]; auto.
Qed.

Definition pilot_residual_nodes n f :=
 residual_nodes f (fst (pilot_walk n) ++ snd (pilot_walk n)).

Theorem pilot_resume_wait_bound : forall w n f,
 pilot_width <= w -> waiting_checker_sound champion_score w f ->
 (forall x, In x (pilot_residual_nodes n f) ->
   Census.NodeDecided champion_score w [] (node_tm x)) ->
 WaitBound champion_score w.
Proof.
 intros w n f Hw Hsound Hres.
 apply (pilot_front_wait_bound_at_width w Hw n).
 eapply resume_nodes_sound; [exact Hsound|exact Hres].
Qed.

(** Certificate discovery and lookup are untrusted. A lookup miss keeps the
    node; a hit is removed only after the complete binary checker accepts. *)
Definition periodic_lookup_check (B w : N)
 (choose : TM -> option periodic_certificate) (tm : TM) : bool :=
 match choose tm with
 | Some c => periodic_entry_check B w (tm,c)
 | None => false
 end.

Theorem periodic_lookup_check_sound : forall B w choose,
 waiting_checker_sound (N.to_nat B) (N.to_nat w) (periodic_lookup_check B w choose).
Proof.
 intros B w choose tm H; unfold periodic_lookup_check in H.
 destruct (choose tm) as [c|]; [|discriminate].
 destruct (periodic_entry_sound B w tm c H) as [HN [HW _]]; auto.
Qed.

Corollary periodic_lookup_check_sound_at : forall B w choose Bnat wnat,
 N.to_nat B = Bnat -> N.to_nat w = wnat ->
 waiting_checker_sound Bnat wnat (periodic_lookup_check B w choose).
Proof. intros B w choose Bnat wnat <- <-; apply periodic_lookup_check_sound. Qed.

Corollary pilot_resume_periodic : forall w n choose,
 pilot_width <= w ->
 (forall x, In x (pilot_residual_nodes n
   (periodic_lookup_check 32779478%N (N.of_nat w) choose)) ->
   Census.NodeDecided champion_score w [] (node_tm x)) ->
 WaitBound champion_score w.
Proof.
 intros w n choose Hw Hres.
 eapply pilot_resume_wait_bound; [exact Hw| |exact Hres].
 apply periodic_lookup_check_sound_at; [reflexivity|apply Nat2N.id].
Qed.

Module ResumeRegression.
Definition accepted_tm : TM := fun _ _ => Some (mkTrans S0 DR StA).
Definition unknown_tm : TM := fun _ _ => None.
Definition accepted_node := mkNode accepted_tm None.
Definition unknown_node := mkNode unknown_tm (Some StB).
Definition choose (tm : TM) : option periodic_certificate :=
 match tm StA S0 with
 | Some _ => Some {| pc_anchor := 0%N; pc_period := 1;
                    pc_width := 0; pc_left := false |}
 | None => None
 end.
Definition check := periodic_lookup_check 0%N 0%N choose.

Example accepted_passes : check accepted_tm = true.
Proof. vm_compute; reflexivity. Qed.
Example unknown_stays : check unknown_tm = false.
Proof. vm_compute; reflexivity. Qed.
Example one_explicit_residual :
 residual_nodes check [accepted_node; unknown_node] = [unknown_node].
Proof. vm_compute; reflexivity. Qed.
Example no_unknown_lost : In unknown_node (residual_nodes check [accepted_node; unknown_node]).
Proof. rewrite one_explicit_residual; left; reflexivity. Qed.
Example regression_resume : forall D,
 Census.NodeDecided 0 0 D unknown_tm ->
 forall x, In x [accepted_node;unknown_node] -> Census.NodeDecided 0 0 D (node_tm x).
Proof.
 intros D Hunknown; eapply (resume_nodes_sound 0 0 D check [accepted_node;unknown_node]).
 - exact (periodic_lookup_check_sound 0%N 0%N choose).
 - rewrite one_explicit_residual; intros x [<-|[]]; exact Hunknown.
Qed.
End ResumeRegression.

Print Assumptions resume_nodes_sound.
Print Assumptions pilot_resume_wait_bound.
Print Assumptions pilot_resume_periodic.
