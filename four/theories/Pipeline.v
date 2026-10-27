(** A small replay vocabulary for the exploratory closure sweep. Search and
    extracted execution are untrusted; accepting a certificate in Coq proves
    both bounds, including every completion of a partial table. *)
From Coq Require Import List NArith.
From BBB24 Require Import Statement Bounds Census NGramCensus RepWLCensus.
Import ListNotations.

Definition machine_of_codes (codes : list nat) : TM :=
  fun q s => nat_trans (nth (4 * st_index q + sym_index s) codes 16).

Inductive StageCert :=
  | NGram (n t fuel rounds : nat)
  | RepeatedWord (L T t fuel : nat).

Definition stage_check (bs bi : N) (tm : TM) (cert : StageCert) : bool :=
  match cert with
  | NGram n t fuel rounds => ng_check bs bi tm n t fuel rounds
  | RepeatedWord L T t fuel => rw_check bs bi tm L T t fuel
  end.

Theorem stage_check_sound : forall bs bi tm cert,
  stage_check bs bi tm cert = true -> NonHalt tm /\ Bounds bs bi tm.
Proof.
  intros bs bi tm []; cbn [stage_check];
    [apply ng_check_sound | apply rw_check_sound].
Qed.

Theorem stage_completions : forall bs bi tm cert,
  stage_check bs bi tm cert = true ->
  forall complete, TM_le tm complete -> Bounds bs bi complete.
Proof.
  intros bs bi tm cert H complete Hle.
  destruct (stage_check_sound _ _ _ _ H) as [Hnh Hb].
  eapply extend_bounds; eauto.
Qed.

Definition Batch := list (list nat * StageCert).
Definition batch_check (bs bi : N) (batch : Batch) :=
  forallb (fun row => stage_check bs bi (machine_of_codes (fst row)) (snd row)) batch.

Theorem batch_completions : forall bs bi batch,
  batch_check bs bi batch = true -> forall codes cert,
  In (codes,cert) batch -> forall complete,
  TM_le (machine_of_codes codes) complete -> Bounds bs bi complete.
Proof.
  intros bs bi batch H codes cert Hin complete Hle.
  unfold batch_check in H. apply forallb_forall with (x:=(codes,cert)) in H;
    [|exact Hin].
  eapply stage_completions; [exact H|exact Hle].
Qed.

Print Assumptions stage_completions.
