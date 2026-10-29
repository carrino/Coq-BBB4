(** State-only closure of a reached undefined transition. All sixteen defined
    choices and the separate halting choice are retained. No instruction bound
    or nonhalting claim is made for the partial root family. *)
From Coq Require Import Arith Lia Bool List NArith.
From BBB24 Require Import Statement Spec CTape Census Closeout BranchCloseout
  StateOnlyCloseout OneStateReach Pipeline.
Import ListNotations.

Theorem state_branch_children_sound : forall B family anchor q l a r,
  anchor < B -> csteps family anchor c0 = Some (q,(l,a,r)) ->
  family q a = None -> StateBoardSound B (branch_children family q a) ->
  forall complete, TM_le family complete -> QHBound B complete.
Proof.
  intros B family anchor q l a r Hn Hrun Hnone Hchildren complete Hle.
  destruct (complete q a) as [tr|] eqn:Ecomplete.
  - destruct (codes_complete tr) as (v & Hv & Ev).
    assert (Hin : In (update family q a (nat_trans v)) (branch_children family q a)).
    { unfold branch_children. apply in_map_iff. exists v; auto. }
    apply (Hchildren _ Hin complete). eapply update_le; eauto. now rewrite Ev.
  - assert (Hr : stepn complete anchor InitES = Some (lift (q,(l,a,r)))).
    { eapply extend_steps; [exact Hle|]. rewrite <- lift_c0.
      apply csteps_lift; exact Hrun. }
    assert (Hhalt : stepn complete (S anchor) InitES = None).
    { replace (S anchor) with (anchor+1) by lia. rewrite stepn_add, Hr.
      cbn [stepn step lift lift_tape fst snd t_head]. now rewrite Ecomplete. }
    pose proof (halt_bounds (N.of_nat B) (N.of_nat B) complete (S anchor)
      ltac:(lia) ltac:(lia) Hhalt) as [Hs _].
    now rewrite Nat2N.id in Hs.
Qed.

Definition state_ore_branch_check B family anchor :=
  (anchor <? B) &&
  match csteps family anchor c0 with
  | None => false
  | Some (q,(_,a,_)) =>
      match family q a with
      | Some _ => false
      | None => forallb ore_auto_state (branch_children family q a)
      end
  end.
Theorem state_ore_branch_check_sound : forall B family anchor,
  state_ore_branch_check B family anchor = true ->
  forall complete, TM_le family complete -> QHBound B complete.
Proof.
  intros B family anchor H.
  unfold state_ore_branch_check in H. apply andb_prop in H as [Hn H].
  apply Nat.ltb_lt in Hn.
  destruct (csteps family anchor c0) as [[q [[l a] r]]|] eqn:Erun; [|discriminate].
  destruct (family q a) as [tr|] eqn:Efamily; [discriminate|].
  eapply state_branch_children_sound; [exact Hn|exact Erun|exact Efamily|].
  apply state_board_zero_weaken. intros child Hin complete Hle.
  apply forallb_forall with (x:=child) in H; [|exact Hin].
  destruct (ore_auto_state_sound child H) as [Hnh Hb].
  exact (state_bound_extend 0 child complete Hnh Hb Hle).
Qed.

Definition StateBranchRows := list (list nat * nat).
Definition state_branch_batch_check B (rows : StateBranchRows) :=
  forallb (fun row => state_ore_branch_check B (machine_of_codes (fst row)) (snd row)) rows.
Definition state_branch_board (rows : StateBranchRows) :=
  map (fun row => machine_of_codes (fst row)) rows.
Theorem state_branch_board_sound : forall B rows,
  state_branch_batch_check B rows = true -> StateBoardSound B (state_branch_board rows).
Proof.
  intros B rows H family Hin complete Hle.
  apply in_map_iff in Hin as ([code anchor] & <- & Hin).
  apply forallb_forall with (x:=(code,anchor)) in H; [|exact Hin].
  exact (state_ore_branch_check_sound B _ _ H complete Hle).
Qed.

Example state_branch_halting_choice_requires_budget :
  state_ore_branch_check 0 empty 0 = false.
Proof. reflexivity. Qed.
Example state_branch_missing_children_rejected :
  state_ore_branch_check 1 empty 0 = false.
Proof. vm_compute; reflexivity. Qed.
Print Assumptions state_branch_children_sound.
Print Assumptions state_ore_branch_check_sound.
