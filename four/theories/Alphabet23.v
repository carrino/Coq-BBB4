(** Transfer the completed BBB(2,3) theorem to closed three-symbol families. *)
From Coq Require Import Arith Lia Bool List NArith.
From SmallBB Require Import Value23.
From BBB24 Require Import Statement StatementTr Spec Bounds Census Bootstrap
  Closeout CertifiedBoard AlphabetReduction Pipeline.
Import ListNotations.

Lemma small23_bounds : forall tm,
  SmallBB.Size.Admissible 2 3 tm -> SmallBB.Bounds.Bounds 59 67 tm.
Proof.
  intros tm Had.
  destruct SmallBB.Value23.BBB23_value as [[_ Hs] [_ Hi]]. split.
  - intros q n Hq. apply (Hs tm (S n) Had). exists q, n; auto.
  - intros tg n Hq. apply (Hi tm (S n) Had). exists tg, n; auto.
Qed.
Theorem alphabet23_bounds : forall b tm,
  ClosedAlphabet b tm -> Bounds 59 67 tm.
Proof.
  intros b tm H. change (Bounds (N.of_nat 59) (N.of_nat 67) tm).
  apply (reduced_bounds b tm 59 67 H), small23_bounds, reduced_admissible.
Qed.
Theorem alphabet23_checked : forall b tm,
  alphabet_check b tm = true -> NonHalt tm /\ Bounds 59 67 tm.
Proof.
  intros b tm H; apply alphabet_check_sound in H; split.
  - exact (closed_nonhalt b tm H).
  - exact (alphabet23_bounds b tm H).
Qed.

Definition AlphabetRows := list (list nat * bool).
Definition alphabet_batch_check (rows : AlphabetRows) :=
  forallb (fun row => alphabet_check (snd row) (machine_of_codes (fst row))) rows.
Definition alphabet_board (rows : AlphabetRows) :=
  map (fun row => machine_of_codes (fst row)) rows.
Lemma alphabet_board_small_sound : forall rows,
  alphabet_batch_check rows = true -> BoardSound 59 67 (alphabet_board rows).
Proof.
  intros rows H family Hin tm Hle. apply in_map_iff in Hin as [row [<- Hin]].
  unfold alphabet_batch_check in H. apply forallb_forall with (x:=row) in H; [|exact Hin].
  apply alphabet_check_sound in H. apply (alphabet23_bounds (snd row)).
  eapply closed_completion; eauto.
Qed.
Lemma alphabet_board_nonhalt : forall rows,
  alphabet_batch_check rows = true ->
  forall family, In family (alphabet_board rows) -> NonHalt family.
Proof.
  intros rows H family Hin. apply in_map_iff in Hin as [row [<- Hin]].
  unfold alphabet_batch_check in H. apply forallb_forall with (x:=row) in H; [|exact Hin].
  exact (proj1 (alphabet23_checked (snd row) (machine_of_codes (fst row)) H)).
Qed.
Lemma alphabet_board_sound : forall rows,
  alphabet_batch_check rows = true -> BoardSound scoreN scoreN (alphabet_board rows).
Proof.
  intros rows H family Hin tm Hle.
  apply (bounds_weaken 59 67 scoreN scoreN tm); try (vm_compute; discriminate).
  exact (alphabet_board_small_sound rows H family Hin tm Hle).
Qed.

Example unused_symbol_read_rejected :
  alphabet_check false (machine_of_codes [0;0;12;16;0;0;0;16]) = false.
Proof. vm_compute; reflexivity. Qed.
Example active_halt_rejected :
  alphabet_check false (machine_of_codes [0;0;16;16;0;0;0;16]) = false.
Proof. vm_compute; reflexivity. Qed.
Example different_omission_rejected :
  alphabet_check true (machine_of_codes [0;0;0;16;0;0;0;16]) = false.
Proof. vm_compute; reflexivity. Qed.

Print Assumptions alphabet23_bounds.
