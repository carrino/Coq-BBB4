(** Only root-cycle certificates imply that the original partial table is
    non-halting. Closed branching trees may include halting completions. *)
From Coq Require Import Bool List NArith.
From BBB24 Require Import Statement Bounds Census Closeout Pipeline CycleCensus CycleBatch.
Import ListNotations.

Definition is_root_cycle (row : list nat * Cert) :=
  match snd row with Cycle _ _ _ _ => true | _ => false end.
Definition cycle_only_board rows := cycle_board (filter is_root_cycle rows).

Lemma cycle_only_subset : forall rows family,
  In family (cycle_only_board rows) -> In family (cycle_board rows).
Proof.
  intros rows family Hin. apply in_map_iff in Hin as (row & <- & Hin).
  apply filter_In in Hin as [Hin _]. apply in_map_iff. exists row. split; [reflexivity|exact Hin].
Qed.
Theorem cycle_only_board_sound : forall bs bi rows,
  cycle_batch_check bs bi rows = true -> BoardSound bs bi (cycle_only_board rows).
Proof.
  intros bs bi rows H family Hin tm Hle.
  apply (cycle_board_sound bs bi rows H family); [apply cycle_only_subset; exact Hin|exact Hle].
Qed.
Theorem cycle_only_board_nonhalt : forall bs bi rows,
  cycle_batch_check bs bi rows = true -> forall family,
  In family (cycle_only_board rows) -> NonHalt family.
Proof.
  intros bs bi rows H family Hin.
  apply in_map_iff in Hin as ([codes cert] & <- & Hin).
  apply filter_In in Hin as [Hin Hkind].
  unfold cycle_batch_check in H.
  apply forallb_forall with (x:=(codes,cert)) in H; [|exact Hin].
  change (closed_census_check bs bi 9 (machine_of_codes codes) cert = true) in H.
  apply andb_prop in H as [Hv _].
  destruct cert as [| |n cs|mirror t p W]; cbn [is_root_cycle snd] in Hkind; try discriminate.
  change (CycleCensus.cycle_check bs bi (machine_of_codes codes) mirror t p W = true) in Hv.
  exact (proj1 (cycle_check_sound _ _ _ _ _ _ _ Hv)).
Qed.

Lemma concat_property : forall (P : TM -> Prop) boards,
  Forall (fun board => forall family, In family board -> P family) boards ->
  forall family, In family (concat boards) -> P family.
Proof.
  intros P boards H. induction H; intros family Hin; simpl in Hin.
  - contradiction.
  - apply in_app_iff in Hin as [Hin|Hin]; auto.
Qed.

Print Assumptions cycle_only_board_nonhalt.
