(** Reusable, compact evidence for a late first undefined instruction.
    The projection hides the large concrete tape, while retaining a checked
    successful prefix and the exact undefined state/symbol pair. *)
From Coq Require Import Arith Bool List Lia NArith.
From BBB24 Require Import Statement Spec CTape Census StateBranchJoin.

Definition reached_undefined_cell family anchor :=
  match csteps family anchor c0 with
  | None => None
  | Some (q,(_,a,_)) =>
      match family q a with Some _ => None | None => Some (q,a) end
  end.
Lemma reached_undefined_witness : forall family anchor q a,
  reached_undefined_cell family anchor = Some (q,a) ->
  exists l r, csteps family anchor c0 = Some (q,(l,a,r)) /\ family q a = None.
Proof.
  intros family anchor q a H. unfold reached_undefined_cell in H.
  destruct (csteps family anchor c0) as [[p [[l s] r]]|] eqn:E; [|discriminate].
  destruct (family p s) eqn:F; [discriminate|]. injection H as <- <-. eauto.
Qed.
Lemma reached_undefined_survives : forall family anchor q a,
  reached_undefined_cell family anchor = Some (q,a) ->
  exists cc, stepn family anchor InitES = Some cc.
Proof.
  intros family anchor q a H.
  destruct (reached_undefined_witness _ _ _ _ H) as (l & r & E & _).
  exists (lift(q,(l,a,r))). rewrite <- lift_c0. apply csteps_lift; exact E.
Qed.
Lemma reached_undefined_halts : forall family anchor q a,
  reached_undefined_cell family anchor = Some (q,a) ->
  stepn family (S anchor) InitES = None.
Proof.
  intros family anchor q a H.
  destruct (reached_undefined_witness _ _ _ _ H) as (l & r & E & F).
  assert (Hr : stepn family anchor InitES = Some(lift(q,(l,a,r)))).
  { rewrite <- lift_c0. apply csteps_lift; exact E. }
  replace (S anchor) with (anchor+1) by lia. rewrite stepn_add,Hr.
  cbn [stepn step lift lift_tape fst snd t_head]. now rewrite F.
Qed.
Lemma state_lookup_reached : forall B board family anchor,
  state_branch_lookup_check B board family anchor =
  ((N.of_nat anchor <? B)%N &&
   match reached_undefined_cell family anchor with
   | None => false
   | Some (q,a) => forallb (Closeout.board_check board) (BranchCloseout.branch_children family q a)
   end).
Proof.
  intros. unfold state_branch_lookup_check,reached_undefined_cell.
  destruct (csteps family anchor c0) as [[q [[l a] r]]|]; [destruct(family q a)|]; reflexivity.
Qed.
Print Assumptions reached_undefined_halts.
