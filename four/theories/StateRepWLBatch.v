(** Packed-table batches for state-only repeated-word closure. *)
From Coq Require Import List NArith.
From BBB24 Require Import Statement Spec Census StateOnlyCloseout StatePipeline StateRepWL.
Import ListNotations.
Record SRWStage := mkSRWStage { srw_L:nat; srw_T:nat; srw_t:nat; srw_fuel:nat }.
Definition srw_stage_check bound tm cert :=
  srw_check bound tm (srw_L cert) (srw_T cert) (srw_t cert) (srw_fuel cert).
Definition srw_batch_check bound cert (rows:list N) :=
  forallb (fun packed=>srw_stage_check bound (stp_machine packed) cert) rows.
Definition srw_board := stp_board.
Theorem srw_batch_state_sound : forall bound cert rows,
  srw_batch_check bound cert rows=true -> StateBoardSound (N.to_nat bound) (srw_board rows).
Proof.
  intros bound cert rows H family Hin tm Hle.
  apply in_map_iff in Hin as (packed&<-&Hin).
  apply forallb_forall with (x:=packed) in H; [|exact Hin].
  destruct (srw_check_sound _ _ _ _ _ _ H) as [Hnh Hb]. eapply state_bound_extend; eauto.
Qed.
Theorem srw_batch_nonhalt : forall bound cert rows,
  srw_batch_check bound cert rows=true -> forall family,
  In family (srw_board rows) -> NonHalt family.
Proof.
  intros bound cert rows H family Hin. apply in_map_iff in Hin as (packed&<-&Hin).
  apply forallb_forall with (x:=packed) in H; [|exact Hin].
  exact (proj1 (srw_check_sound _ _ _ _ _ _ H)).
Qed.
