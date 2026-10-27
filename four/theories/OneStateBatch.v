(** Packed total-table inputs for state-only reachability replay. *)
From Coq Require Import List NArith.
From BBB24 Require Import Statement Spec Census Pipeline OneStateReach StateOnlyCloseout.
Import ListNotations.

Fixpoint ore_unpack fuel (packed : N) : list nat :=
  match fuel with
  | 0 => []
  | S f => N.to_nat (packed mod 16)%N :: ore_unpack f (packed / 16)%N
  end.
Definition ore_machine packed := machine_of_codes (ore_unpack 8 packed).
Definition ore_batch_check (rows : list N) :=
  forallb (fun packed => ore_auto_state (ore_machine packed)) rows.
Definition ore_board rows := map ore_machine rows.
Theorem ore_batch_nonhalt : forall rows,
  ore_batch_check rows=true -> forall family, In family (ore_board rows) -> NonHalt family.
Proof.
  intros rows H family Hin. apply in_map_iff in Hin as (packed&<-&Hin).
  apply forallb_forall with (x:=packed) in H; [|exact Hin].
  exact (proj1 (ore_auto_state_sound _ H)).
Qed.
Theorem ore_batch_state_sound : forall rows,
  ore_batch_check rows=true -> StateBoardSound 0 (ore_board rows).
Proof.
  intros rows H family Hin tm Hle. apply in_map_iff in Hin as (packed&<-&Hin).
  apply forallb_forall with (x:=packed) in H; [|exact Hin].
  destruct (ore_auto_state_sound _ H) as [Hnh Hb]. eapply state_bound_extend; eauto.
Qed.
Print Assumptions ore_batch_state_sound.
