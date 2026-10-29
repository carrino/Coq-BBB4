(** Survivor-focused census certificates. A closed tree bounds every completion
    of its input family, including the halting choice at each reached undefined
    cell. Deferred children never count as a closed original family. *)
From Coq Require Import Arith Bool List NArith.
From BBB24 Require Import Statement Spec Bounds Census Bootstrap Closeout Pipeline.
Import ListNotations.

Definition closed_census_check bs bi depth tm cert :=
  verify bs bi depth tm cert && Nat.eqb (length (residue depth tm cert)) 0.

Theorem closed_census_check_sound : forall bs bi depth tm cert,
  closed_census_check bs bi depth tm cert = true ->
  forall complete, TM_le tm complete -> Bounds bs bi complete.
Proof.
  intros bs bi depth tm cert H complete Hle.
  apply andb_prop in H as [Hv Hr]. apply Nat.eqb_eq in Hr.
  apply length_zero_iff_nil in Hr.
  destruct (verify_cover bs bi depth tm cert Hv complete Hle) as [Hb|(leaf & Hin & _)];
    [exact Hb|]. rewrite Hr in Hin. contradiction.
Qed.

Definition CycleRows := list (list nat * Cert).
Definition cycle_batch_check bs bi (rows : CycleRows) :=
  forallb (fun row => closed_census_check bs bi 9 (machine_of_codes (fst row)) (snd row)) rows.
Definition cycle_board (rows : CycleRows) : list TM :=
  map (fun row => machine_of_codes (fst row)) rows.

Theorem cycle_board_sound : forall bs bi rows,
  cycle_batch_check bs bi rows = true -> BoardSound bs bi (cycle_board rows).
Proof.
  intros bs bi rows H family Hin tm Hle.
  apply in_map_iff in Hin as ([codes cert] & <- & Hin).
  unfold cycle_batch_check in H.
  apply forallb_forall with (x:=(codes,cert)) in H; [|exact Hin].
  eapply closed_census_check_sound; [exact H|exact Hle].
Qed.

Definition cycle_pending_check rows := forallb (pending_check 9 empty bootstrap) (cycle_board rows).
Theorem cycle_board_was_pending : forall rows,
  cycle_pending_check rows = true -> forall family,
  In family (cycle_board rows) -> bootstrap_pending family.
Proof.
  intros rows H family Hin. apply pending_check_sound.
  apply forallb_forall with (x:=family) in H; assumption.
Qed.

Example deferred_is_not_closed :
  closed_census_check 4097%N 4097%N 9 empty Deferred = false.
Proof. reflexivity. Qed.
Example missing_children_not_closed :
  closed_census_check 4097%N 4097%N 9 empty (Branch 0 []) = false.
Proof. vm_compute. reflexivity. Qed.
Example deferred_children_not_closed :
  closed_census_check 4097%N 4097%N 9 empty (Branch 0 (repeat Deferred 16)) = false.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions closed_census_check_sound.
