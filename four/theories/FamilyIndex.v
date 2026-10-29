(** Positive-key lookup in a proved partial-family board.  A lookup key is an
    untrusted search witness: even a collision selects only another proved
    family, whose table relation to the target must still pass its checker. *)
From Coq Require Import List NArith Bool FSets.FMapPositive.
From BBB24 Require Import Statement StatementTr Bounds Census Closeout FamilyTransport.
Import ListNotations.

Definition family_cell_code (tm : TM) (tg : Instr) :=
  match tm (fst tg) (snd tg) with Some tr => trans_code tr | None => 16 end.
Definition family_key tm :=
  match fold_left (fun acc tg => (17*acc+N.of_nat (family_cell_code tm tg))%N) all_Instr 1%N with
  | N0 => xH | Npos key => key end.
Fixpoint family_index (board : list TM) : PositiveMap.t TM :=
  match board with
  | [] => PositiveMap.empty TM
  | tm::tail => PositiveMap.add (family_key tm) tm (family_index tail)
  end.
Lemma family_index_member : forall board key tm,
  PositiveMap.find key (family_index board)=Some tm -> In tm board.
Proof.
  induction board as [|head tail IH]; intros key tm H; cbn [family_index] in H.
  - rewrite PositiveMap.gempty in H. discriminate.
  - rewrite PositiveMapAdditionalFacts.gsspec in H.
    destruct (PositiveMap.E.eq_dec key (family_key head)).
    + injection H as <-. now left.
    + right. eapply IH; exact H.
Qed.
Theorem family_index_strong : forall bs bi board key tm,
  StrongBoard bs bi board -> PositiveMap.find key (family_index board)=Some tm ->
  NonHalt tm /\ Bounds bs bi tm.
Proof. intros bs bi board key tm Hboard H; apply Hboard; eapply family_index_member; exact H. Qed.

Definition indexed_completion_check index key target :=
  match PositiveMap.find key index with
  | Some source => table_leb source target
  | None => false
  end.
Theorem indexed_completion_sound : forall bs bi board key target,
  StrongBoard bs bi board -> indexed_completion_check (family_index board) key target=true ->
  NonHalt target /\ Bounds bs bi target.
Proof.
  intros bs bi board key target Hboard H. unfold indexed_completion_check in H.
  destruct (PositiveMap.find key (family_index board)) as [source|] eqn:E; [|discriminate].
  apply table_leb_spec in H. eapply completion_strong; [|exact H].
  eapply family_index_strong; eauto.
Qed.

Print Assumptions family_index_strong.
Print Assumptions indexed_completion_sound.
