(** Constant-size positive keys select already proved source families.  Every
    selected transition table and pair of finite boots is still checked. *)
From Coq Require Import List Bool NArith FSets.FMapPositive.
From BBB24 Require Import Statement Bounds Census Closeout Pipeline FamilyTransport
  Symmetry ConjugateTransport FamilyIndex.
Import ListNotations.

Record IndexedConjugateRow := indexed_conjugate_row {
  indexed_codes : list nat;
  indexed_source_key : positive;
  indexed_permutation : SymPerm;
  indexed_mirrored : bool;
  indexed_destination_boot : nat;
  indexed_source_boot : nat
}.
Definition indexed_conjugate_tm row := machine_of_codes (indexed_codes row).
Definition indexed_conjugate_check bs bi out_bs out_bi index row :=
  ((bs+N.of_nat (indexed_destination_boot row) <=? out_bs)%N) &&
  ((bi+N.of_nat (indexed_destination_boot row) <=? out_bi)%N) &&
  match PositiveMap.find (indexed_source_key row) index with
  | Some source => conjugate_check (indexed_conjugate_tm row) source
      (indexed_permutation row) (indexed_mirrored row)
      (indexed_destination_boot row) (indexed_source_boot row)
  | None => false
  end.
Theorem indexed_conjugate_sound : forall bs bi out_bs out_bi board row,
  StrongBoard bs bi board ->
  indexed_conjugate_check bs bi out_bs out_bi (family_index board) row=true ->
  NonHalt (indexed_conjugate_tm row) /\ Bounds out_bs out_bi (indexed_conjugate_tm row).
Proof.
  intros bs bi out_bs out_bi board row Hboard H.
  apply andb_prop in H as [Hbud Hcheck]. apply andb_prop in Hbud as [Hbs Hbi].
  apply N.leb_le in Hbs,Hbi.
  destruct (PositiveMap.find (indexed_source_key row) (family_index board)) as [source|] eqn:E;
    [|discriminate].
  destruct (family_index_strong bs bi board _ _ Hboard E) as [Hnh Hb].
  destruct (conjugate_check_sound _ _ _ _ _ _ _ _ Hcheck Hnh Hb) as [Hnh' Hb'].
  split; [exact Hnh'|]. eapply bounds_weaken; eauto.
Qed.
Theorem indexed_conjugate_batch_sound : forall bs bi out_bs out_bi board rows,
  StrongBoard bs bi board ->
  forallb (indexed_conjugate_check bs bi out_bs out_bi (family_index board)) rows=true ->
  StrongBoard out_bs out_bi (map indexed_conjugate_tm rows).
Proof.
  intros bs bi out_bs out_bi board rows Hboard H tm Hin.
  apply in_map_iff in Hin as (row & <- & Hin).
  apply forallb_forall with (x:=row) in H; [|exact Hin].
  eapply indexed_conjugate_sound; eauto.
Qed.

Print Assumptions indexed_conjugate_batch_sound.
