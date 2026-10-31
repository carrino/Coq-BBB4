(** Reuse a supplied weighted closure and ranking after a separately checked
    boot. The table and boot may differ from the search source: every closure,
    prefix and liveness obligation is recomputed for the actual target. *)
From Coq Require Import List NArith.
From BBB24 Require Import Statement Bounds Census Mirror CycleCensus CTape Pipeline
  FamilyTransport WeightedCensus.
Import ListNotations.

Record WeightedReuseRow := weighted_reuse_row {
  reuse_codes : list nat;
  reuse_mirrored : bool;
  reuse_boot : nat
}.
Definition reuse_tm row := machine_of_codes (reuse_codes row).
Definition reuse_actual row :=
  if reuse_mirrored row then mirror_tm (reuse_tm row) else reuse_tm row.
Definition weighted_reuse_check bs bi n nodes cert row :=
  wc_graph_check bs bi (reuse_actual row) n (reuse_boot row) nodes cert.

Theorem weighted_reuse_sound : forall bs bi n nodes cert row,
  weighted_reuse_check bs bi n nodes cert row=true ->
  NonHalt (reuse_tm row) /\ Bounds bs bi (reuse_tm row).
Proof.
  intros bs bi n nodes cert row H.
  destruct (wc_graph_check_sound _ _ _ _ _ _ _ H) as [Hnh Hb].
  unfold reuse_actual in Hnh,Hb. destruct (reuse_mirrored row).
  - split; [apply mirror_nonhalt; exact Hnh|apply mirror_bounds; exact Hb].
  - split; assumption.
Qed.
Theorem weighted_reuse_batch_sound : forall bs bi n nodes cert rows,
  forallb (weighted_reuse_check bs bi n nodes cert) rows=true ->
  StrongBoard bs bi (map reuse_tm rows).
Proof.
  intros bs bi n nodes cert rows H tm Hin.
  apply in_map_iff in Hin as (row & <- & Hin).
  apply forallb_forall with (x:=row) in H; [|exact Hin].
  eapply weighted_reuse_sound; exact H.
Qed.

Print Assumptions weighted_reuse_batch_sound.
