(** State-only branch joining with a mixture of existing one-state reachability
    checks and cycle/census certificates for exceptional defined children. *)
From Coq Require Import Arith Lia Bool List NArith.
From BBB24 Require Import Statement Spec CTape Census Closeout BranchCloseout
  StateOnlyCloseout OneStateReach Pipeline CycleBatch StateBranchCloseout.
Import ListNotations.

Definition state_branch_child_check B child cert :=
  ore_auto_state child || closed_census_check (N.of_nat B) (N.of_nat B) 9 child cert.
Lemma state_branch_child_check_sound : forall B child cert,
  state_branch_child_check B child cert = true ->
  forall complete, TM_le child complete -> QHBound B complete.
Proof.
  intros B child cert H complete Hle. apply orb_true_iff in H as [H|H].
  - destruct (ore_auto_state_sound child H) as [Hnh Hb].
    pose proof (state_bound_extend 0 child complete Hnh Hb Hle) as Hs.
    intros q n Hq. specialize (Hs q n Hq). lia.
  - destruct (closed_census_check_sound _ _ _ _ _ H complete Hle) as [Hs _].
    now rewrite Nat2N.id in Hs.
Qed.
Definition state_branch_child_cert v certs :=
  match find (fun row : nat*Cert => Nat.eqb (fst row) v) certs with
  | Some (_, cert) => cert | None => Deferred
  end.
Definition state_mixed_branch_check B family anchor certs :=
  (anchor <? B) &&
  match csteps family anchor c0 with
  | None => false
  | Some (q,(_,a,_)) =>
      match family q a with
      | Some _ => false
      | None => forallb (fun v => state_branch_child_check B
          (update family q a (nat_trans v)) (state_branch_child_cert v certs)) (seq 0 16)
      end
  end.
Theorem state_mixed_branch_check_sound : forall B family anchor certs,
  state_mixed_branch_check B family anchor certs = true ->
  forall complete, TM_le family complete -> QHBound B complete.
Proof.
  intros B family anchor certs H.
  unfold state_mixed_branch_check in H. apply andb_prop in H as [Hn H].
  apply Nat.ltb_lt in Hn.
  destruct (csteps family anchor c0) as [[q [[l a] r]]|] eqn:Erun; [|discriminate].
  destruct (family q a) as [tr|] eqn:Efamily; [discriminate|].
  eapply state_branch_children_sound; [exact Hn|exact Erun|exact Efamily|].
  intros child Hin complete Hle. apply in_map_iff in Hin as (v & <- & Hin).
  apply forallb_forall with (x:=v) in H; [|exact Hin].
  exact (state_branch_child_check_sound B _ _ H complete Hle).
Qed.
Definition StateMixedBranchRows := list (list nat * nat * list (nat*Cert)).
Definition state_mixed_branch_batch_check B (rows : StateMixedBranchRows) :=
  forallb (fun row => let '(code,anchor,certs) := row in
    state_mixed_branch_check B (machine_of_codes code) anchor certs) rows.
Definition state_mixed_branch_board (rows : StateMixedBranchRows) :=
  map (fun row => let '(code,_,_) := row in machine_of_codes code) rows.
Theorem state_mixed_branch_board_sound : forall B rows,
  state_mixed_branch_batch_check B rows = true ->
  StateBoardSound B (state_mixed_branch_board rows).
Proof.
  intros B rows H family Hin complete Hle.
  apply in_map_iff in Hin as ([[code anchor] certs] & <- & Hin).
  apply forallb_forall with (x:=(code,anchor,certs)) in H; [|exact Hin].
  exact (state_mixed_branch_check_sound B _ _ _ H complete Hle).
Qed.

Example mixed_branch_missing_exception_rejected :
  state_mixed_branch_check 8192 (machine_of_codes [5;10;4;6;14;16;9;2]) 375 [] = false.
Proof. vm_compute; reflexivity. Qed.
Print Assumptions state_mixed_branch_check_sound.
