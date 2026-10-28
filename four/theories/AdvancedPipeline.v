(** Replay vocabulary for the next closure sweep. All modes here establish
    both state and instruction bounds; state-only search results are excluded. *)
From Coq Require Import List NArith.
From BBB24 Require Import Statement Bounds Census Closeout Pipeline FiniteCensus HistCensus.
Import ListNotations.

Inductive AdvancedCert :=
  | ExistingStage (cert : StageCert)
  | Finite (n t fuel rounds : nat)
  | History (k n t fuel rounds : nat).

Definition advanced_check (bs bi : N) (tm : TM) (cert : AdvancedCert) :=
  match cert with
  | ExistingStage c => stage_check bs bi tm c
  | Finite n t fuel rounds => fn_check_mode false bs bi tm n t fuel rounds
  | History k n t fuel rounds => hn_check_mode false bs bi tm k n t fuel rounds
  end.

Theorem advanced_check_sound : forall bs bi tm cert,
  advanced_check bs bi tm cert = true -> NonHalt tm /\ Bounds bs bi tm.
Proof.
  intros bs bi tm []; cbn [advanced_check].
  - apply stage_check_sound.
  - apply (fn_check_mode_sound false).
  - apply (hn_check_mode_sound false).
Qed.

Theorem advanced_completions : forall bs bi tm cert,
  advanced_check bs bi tm cert = true ->
  forall complete, TM_le tm complete -> Bounds bs bi complete.
Proof.
  intros bs bi tm cert H complete Hle.
  destruct (advanced_check_sound _ _ _ _ H) as [Hnh Hb].
  eapply extend_bounds; eauto.
Qed.

Definition AdvancedBatch := list (list nat * AdvancedCert).
Definition advanced_batch_check (bs bi : N) (batch : AdvancedBatch) :=
  forallb (fun row => advanced_check bs bi (machine_of_codes (fst row)) (snd row)) batch.

Theorem advanced_batch_completions : forall bs bi batch,
  advanced_batch_check bs bi batch = true -> forall codes cert,
  In (codes,cert) batch -> forall complete,
  TM_le (machine_of_codes codes) complete -> Bounds bs bi complete.
Proof.
  intros bs bi batch H codes cert Hin complete Hle.
  unfold advanced_batch_check in H.
  apply forallb_forall with (x:=(codes,cert)) in H; [|exact Hin].
  eapply advanced_completions; [exact H|exact Hle].
Qed.

Definition advanced_board (batch : AdvancedBatch) : list TM :=
  map (fun row => machine_of_codes (fst row)) batch.

Theorem advanced_board_sound : forall bs bi batch,
  advanced_batch_check bs bi batch = true -> BoardSound bs bi (advanced_board batch).
Proof.
  intros bs bi batch H family Hin tm Hle.
  apply in_map_iff in Hin as ([codes cert] & <- & Hin).
  eapply advanced_batch_completions; eauto.
Qed.

Theorem advanced_board_nonhalt : forall bs bi batch,
  advanced_batch_check bs bi batch = true -> forall family,
  In family (advanced_board batch) -> NonHalt family.
Proof.
  intros bs bi batch H family Hin.
  apply in_map_iff in Hin as ([codes cert] & <- & Hin).
  unfold advanced_batch_check in H.
  apply forallb_forall with (x:=(codes,cert)) in H; [|exact Hin].
  exact (proj1 (advanced_check_sound _ _ _ _ H)).
Qed.

Print Assumptions advanced_check_sound.
