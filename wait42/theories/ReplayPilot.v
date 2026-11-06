(** A bounded quantitative replay of the existing ten-round pilot frontier.
    Search failure preserves a node verbatim as a completion obligation. *)
From Coq Require Import Arith Lia Bool List.
From BBB4 Require Import BBB4_Statement BBB4_Spec.
From BBB4.Census Require Import TNF_QH.
From BBBWait42 Require Import Spec Census Run Pilot Resume Ranked RankedCompletion RepeatedWord.
Import ListNotations.
Local Opaque champion_score.

Definition replay_pilot_checker tm :=
 if repwl_ranked_search tm 3 2 64 0 1024 4096 then true else
 if repwl_ranked_search tm 3 2 64 32 1024 4096 then true else
 ngram_ranked_search tm 4 64 256 34 4096.

Lemma replay_pilot_anchor_bound : 64 <= champion_score.
Proof.
 eapply Nat.le_trans; [|exact pilot_halt_gas_le_cutoff].
 unfold pilot_halt_gas; lia.
Qed.

Local Opaque repwl_ranked_search ngram_ranked_search.
Theorem replay_pilot_checker_sound :
 waiting_checker_sound champion_score 4096 replay_pilot_checker.
Proof.
 intros tm H; unfold replay_pilot_checker in H.
 destruct (repwl_ranked_search tm 3 2 64 0 1024 4096) eqn:H0.
 - split.
   + exact (repwl_ranked_search_nonhalt tm 3 2 64 0 1024 4096 H0).
   + exact (repwl_ranked_search_sound tm 3 2 64 0 1024 4096 champion_score
       (Nat.le_0_l _) H0).
 - destruct (repwl_ranked_search tm 3 2 64 32 1024 4096) eqn:H32.
   + split.
     * exact (repwl_ranked_search_nonhalt tm 3 2 64 32 1024 4096 H32).
     * apply (repwl_ranked_search_sound tm 3 2 64 32 1024 4096 champion_score); [|exact H32].
       eapply Nat.le_trans; [|exact replay_pilot_anchor_bound]; lia.
   + split.
     * exact (ngram_ranked_search_nonhalt tm 4 64 256 34 4096 H).
     * exact (ngram_ranked_search_sound tm 4 64 256 34 4096 champion_score
         replay_pilot_anchor_bound H).
Qed.

Local Transparent repwl_ranked_search ngram_ranked_search.
Definition replay_pilot_residual := pilot_residual_nodes 10 replay_pilot_checker.

(** The front consists of pending subtree roots; the back consists of nodes
    already tagged unknown by the original pilot. Neither list enumerates only
    fully specified machines. Keep this distinction in the computed counts. *)
Definition replay_pilot_residual_parts :=
 let q := checked_pilot_frontier in
 (residual_nodes replay_pilot_checker (fst q),
  residual_nodes replay_pilot_checker (snd q)).

Theorem replay_pilot_initial_count :
 length (fst checked_pilot_frontier ++ snd checked_pilot_frontier) = 391.
Proof.
 rewrite app_length.
 exact (f_equal (fun p : nat * nat => fst p + snd p) checked_pilot_sizes).
Qed.

(** Native evaluation proposes the equality; the saved proof and all its
    dependencies are recursively kernel checked by coqchk. *)
Theorem replay_pilot_residual_sizes :
 (length (fst replay_pilot_residual_parts), length (snd replay_pilot_residual_parts)) = (21,29).
Proof. native_compute; reflexivity. Qed.

Local Opaque repwl_ranked_search ngram_ranked_search replay_pilot_checker pilot_walk.

Theorem replay_pilot_residual_count : length replay_pilot_residual = 50.
Proof.
 unfold replay_pilot_residual, pilot_residual_nodes, residual_nodes.
 rewrite filter_app, app_length.
 exact (f_equal (fun p : nat * nat => fst p + snd p) replay_pilot_residual_sizes).
Qed.

Theorem replay_pilot_removed_count :
 length (fst checked_pilot_frontier ++ snd checked_pilot_frontier) -
 length replay_pilot_residual = 341.
Proof. rewrite replay_pilot_initial_count, replay_pilot_residual_count; reflexivity. Qed.

Theorem replay_pilot_still_unfinished : replay_pilot_residual <> [].
Proof.
 intro H; pose proof replay_pilot_residual_count as HC; rewrite H in HC; discriminate.
Qed.

Theorem replay_pilot_residual_spec : forall x,
 In x replay_pilot_residual <->
 In x (fst checked_pilot_frontier ++ snd checked_pilot_frontier) /\
 replay_pilot_checker (node_tm x) = false.
Proof. intro x; apply residual_nodes_spec. Qed.

Theorem replay_pilot_conditional_coverage :
 (forall x, In x replay_pilot_residual ->
   Census.NodeDecided champion_score 4096 [] (node_tm x)) ->
 WaitBound champion_score 4096.
Proof.
 intro Hres; apply (pilot_resume_wait_bound 4096 10 replay_pilot_checker).
 - apply Nat.le_refl.
 - exact replay_pilot_checker_sound.
 - exact Hres.
Qed.

Print Assumptions replay_pilot_checker_sound.
Print Assumptions replay_pilot_residual_sizes.
Print Assumptions replay_pilot_conditional_coverage.
