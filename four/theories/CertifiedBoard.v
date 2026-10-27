(** Assemble independently proved non-halting families without re-running their
    checkers. Each table is paired with its own proof, so a mistaken table/proof
    association is rejected by Coq's type checker. *)
From Coq Require Import List NArith.
From BBB24 Require Import Statement Bounds Census Closeout.
Import ListNotations.

Record CertifiedFamily (bs bi : N) := mkCertifiedFamily {
  certified_tm : TM;
  certified_run : NonHalt certified_tm /\ Bounds bs bi certified_tm
}.
Arguments certified_tm {bs bi} _.
Arguments certified_run {bs bi} _.

Definition certified_board bs bi (families : list (CertifiedFamily bs bi)) :=
  map (@certified_tm bs bi) families.

Theorem certified_board_nonhalt : forall bs bi families family,
  In family (certified_board bs bi families) -> NonHalt family.
Proof.
  intros bs bi families family H.
  apply in_map_iff in H as (entry & <- & _).
  exact (proj1 (certified_run entry)).
Qed.
Theorem certified_board_bounds : forall bs bi families family,
  In family (certified_board bs bi families) -> Bounds bs bi family.
Proof.
  intros bs bi families family H.
  apply in_map_iff in H as (entry & <- & _).
  exact (proj2 (certified_run entry)).
Qed.
Theorem certified_board_sound : forall bs bi families,
  BoardSound bs bi (certified_board bs bi families).
Proof.
  intros bs bi families family Hin tm Hle.
  eapply extend_bounds; [eapply certified_board_nonhalt | eapply certified_board_bounds |]; eauto.
Qed.

Lemma pending_completion : forall xs family tm,
  Pending xs family -> TM_le family tm -> Pending xs tm.
Proof.
  intros xs family tm (leaf & Hin & Hlf) Hft.
  exists leaf. split; [exact Hin|]. intros q s.
  destruct (Hlf q s) as [H|H]; [left; exact H|].
  destruct (Hft q s) as [H'|H']; [left|right]; congruence.
Qed.
Theorem board_families_discharged : forall bs bi xs pending board,
  (forall family, In family board -> Pending xs family) ->
  BoardSound bs bi board -> forall family,
  In family board -> forall tm, TM_le family tm ->
  Pending xs tm /\ Bounds bs bi tm /\ ~ remaining pending board tm.
Proof.
  intros bs bi xs pending board Hpending Hsound family Hin tm Hle.
  split; [eapply pending_completion; [apply Hpending; exact Hin|exact Hle]|].
  split; [exact (Hsound family Hin tm Hle)|].
  intros [_ Hremaining].
  assert (Hhit : board_check board tm = true).
  { apply existsb_exists. exists family. split; [exact Hin|].
    apply table_leb_spec. exact Hle. }
  congruence.
Qed.

Print Assumptions certified_board_nonhalt.
Print Assumptions certified_board_sound.
