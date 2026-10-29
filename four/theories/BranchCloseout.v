(** Join an explored partial family using any already proved child board.
    The undefined (halting) choice is separate from the sixteen defined
    transitions and is bounded by the verified first-undefined prefix. *)
From Coq Require Import Arith Lia Bool List NArith.
From BBB24 Require Import Statement Spec CTape Bounds Census Closeout.
Import ListNotations.

Definition branch_children (family : TM) q a :=
  map (fun v => update family q a (nat_trans v)) (seq 0 16).
Definition branch_link_check bs bi (board : list TM) (family : TM) anchor :=
  (N.of_nat anchor <? N.min bs bi)%N &&
  match csteps family anchor c0 with
  | None => false
  | Some (q,(_,a,_)) =>
    match family q a with
    | Some _ => false
    | None => forallb (board_check board) (branch_children family q a)
    end
  end.

Lemma branch_tm_le_trans : forall a b c, TM_le a b -> TM_le b c -> TM_le a c.
Proof.
  intros a b c Hab Hbc q s. destruct (Hab q s) as [E|E]; [left; exact E|].
  destruct (Hbc q s) as [F|F]; [left|right]; congruence.
Qed.
Lemma board_check_completion : forall bs bi board family,
  BoardSound bs bi board -> board_check board family = true ->
  forall complete, TM_le family complete -> Bounds bs bi complete.
Proof.
  intros bs bi board family Hsound H complete Hle.
  apply existsb_exists in H as [source [Hin Hsource]].
  apply table_leb_spec in Hsource. apply (Hsound source Hin complete).
  eapply branch_tm_le_trans; eauto.
Qed.

Theorem branch_link_check_sound : forall bs bi board family anchor,
  BoardSound bs bi board -> branch_link_check bs bi board family anchor = true ->
  forall complete, TM_le family complete -> Bounds bs bi complete.
Proof.
  intros bs bi board family anchor Hsound H complete Hle.
  unfold branch_link_check in H. apply andb_prop in H as [Hn H].
  apply N.ltb_lt in Hn.
  destruct (csteps family anchor c0) as [[q [[l a] r]]|] eqn:Erun; [|discriminate].
  destruct (family q a) as [tr|] eqn:Efamily; [discriminate|].
  destruct (complete q a) as [tr|] eqn:Ecomplete.
  - destruct (codes_complete tr) as [v [Hv Ev]].
    assert (Hin : In (update family q a (nat_trans v)) (branch_children family q a)).
    { unfold branch_children. apply in_map_iff. exists v; auto. }
    apply forallb_forall with (x:=update family q a (nat_trans v)) in H; [|exact Hin].
    eapply board_check_completion; [exact Hsound|exact H|].
    eapply update_le; [exact Hle|exact Efamily|]. now rewrite Ev.
  - apply (halt_bounds bs bi complete (S anchor)).
    + pose proof (N.le_min_l bs bi); lia.
    + pose proof (N.le_min_r bs bi); lia.
    + assert (Hr : stepn complete anchor InitES = Some (lift (q,(l,a,r)))).
      { eapply extend_steps; [exact Hle|]. rewrite <- lift_c0.
        apply csteps_lift; exact Erun. }
      replace (S anchor) with (anchor+1) by lia. rewrite stepn_add, Hr.
      cbn [stepn step lift lift_tape fst snd t_head]. now rewrite Ecomplete.
Qed.

Example missing_defined_child_rejected :
  branch_link_check 2 2 (tl (branch_children empty StA S0)) empty 0 = false.
Proof. vm_compute; reflexivity. Qed.
Example halting_choice_needs_budget :
  branch_link_check 0 0 (branch_children empty StA S0) empty 0 = false.
Proof. vm_compute; reflexivity. Qed.
Example all_defined_children_covered :
  branch_link_check 1 1 (branch_children empty StA S0) empty 0 = true.
Proof. vm_compute; reflexivity. Qed.

Print Assumptions branch_link_check_sound.
