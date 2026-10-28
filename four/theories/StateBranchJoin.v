(** A finite lookup board may discharge every defined child of a reached
    partial family. The halting child is checked separately. *)
From Coq Require Import Arith Bool List Lia NArith.
From BBB24 Require Import Statement Spec CTape Census Bootstrap Closeout
  BranchCloseout StateOnlyCloseout StateBranchCloseout.
Import ListNotations.

Lemma state_board_N_weaken : forall b b' board,
  (b <= b')%N -> StateBoardSound (N.to_nat b) board ->
  StateBoardSound (N.to_nat b') board.
Proof.
  intros b b' board Hle H family Hin tm Htm q n Hq.
  pose proof (H family Hin tm Htm q n Hq) as Hb.
  assert (Hnat : N.to_nat b <= N.to_nat b').
  { apply Nat.compare_le_iff. rewrite <- N2Nat.inj_compare. exact Hle. }
  exact (Nat.le_trans _ _ _ Hb Hnat).
Qed.
Lemma state_board_check_completion : forall B board family,
  StateBoardSound B board -> board_check board family = true ->
  forall complete, TM_le family complete -> QHBound B complete.
Proof.
  intros B board family Hsound H complete Hle.
  apply existsb_exists in H as (source & Hin & Hsource).
  apply table_leb_spec in Hsource. apply (Hsound source Hin complete).
  eapply branch_tm_le_trans; eauto.
Qed.
Definition state_branch_lookup_check (B : N) board family anchor :=
  (N.of_nat anchor <? B)%N &&
  match csteps family anchor c0 with
  | None => false
  | Some (q,(_,a,_)) =>
      match family q a with
      | Some _ => false
      | None => forallb (board_check board) (branch_children family q a)
      end
  end.
Theorem state_branch_lookup_check_sound : forall B board family anchor,
  StateBoardSound (N.to_nat B) board ->
  state_branch_lookup_check B board family anchor = true ->
  forall complete, TM_le family complete -> QHBound (N.to_nat B) complete.
Proof.
  intros B board family anchor Hsound H.
  unfold state_branch_lookup_check in H. apply andb_prop in H as [Hn H].
  apply N.ltb_lt in Hn.
  destruct (csteps family anchor c0) as [[q [[l a] r]]|] eqn:Erun; [|discriminate].
  destruct (family q a) as [tr|] eqn:Efamily; [discriminate|].
  assert (Hnat : anchor < N.to_nat B).
  { rewrite <- (Nat2N.id anchor). apply Nat.compare_lt_iff.
    rewrite <- N2Nat.inj_compare. exact Hn. }
  eapply (state_branch_children_sound (N.to_nat B)); [exact Hnat|exact Erun|exact Efamily|].
  intros child Hin complete Hle.
  apply forallb_forall with (x:=child) in H; [|exact Hin].
  exact (state_board_check_completion _ _ _ Hsound H complete Hle).
Qed.
Example state_lookup_missing_child_rejected :
  state_branch_lookup_check 1 (tl (branch_children empty StA S0)) empty 0 = false.
Proof. vm_compute; reflexivity. Qed.
Example state_lookup_halting_choice_needs_budget :
  state_branch_lookup_check 0 (branch_children empty StA S0) empty 0 = false.
Proof. reflexivity. Qed.
Example state_lookup_all_children_covered :
  state_branch_lookup_check 1 (branch_children empty StA S0) empty 0 = true.
Proof. vm_compute; reflexivity. Qed.
Print Assumptions state_branch_lookup_check_sound.
