(** Generic source candidate: actual table checks transfer a proved old board
    to arbitrary lightweight target data. No old provider is imported here. *)
From Coq Require Import List Bool NArith FSets.FMapPositive.
From BBB24 Require Import Statement Census StateOnlyCloseout FamilyIndex
  Closeout BranchCloseout FamilyTransport.
From BBB24GlobalLeaves Require Import GlobalLeaves.
From BBB24GlobalUnits Require Import Assembly.
Import ListNotations.

Lemma indexed_target_bound : forall B index target,
  IndexSound B index ->
  indexed_completion_check index (family_key target) target = true ->
  FamilyBound B target.
Proof.
  intros B index target HI HC complete Hle.
  unfold indexed_completion_check in HC.
  destruct (PositiveMap.find (family_key target) index) as [source|] eqn:E;
    [|discriminate].
  apply table_leb_spec in HC.
  apply (HI _ _ E complete).
  eapply branch_tm_le_trans; [exact HC|exact Hle].
Qed.

Definition transfer_check (index : PositiveMap.t TM) (targets : list TM) :=
  forallb (fun target => indexed_completion_check index (family_key target) target) targets.

Theorem transfer_state_sound : forall B old targets,
  StateBoardSound B old -> transfer_check (family_index old) targets = true ->
  StateBoardSound B targets.
Proof.
  intros B old targets HO HC target Hin.
  unfold transfer_check in HC.
  apply forallb_forall with (x := target) in HC; [|exact Hin].
  exact (indexed_target_bound B (family_index old) target
    (board_index_sound B old HO) HC).
Qed.

(** The final heavy proof file can use this theorem without evaluating an
    index. Its boards and index are the same lightweight data constants used
    in the independent certificate-checking processes. *)
Theorem aggregate_index_sound : forall B boards,
  Forall (StateBoardSound B) boards ->
  IndexSound B (family_index (concat boards)).
Proof.
  intros B boards HB. apply board_index_sound.
  apply state_boards_sound. exact HB.
Qed.

(** Small theorem TYPE: all large words live only inside an opaque proof.
    This existential is a proved certificate, not an assumed witness. *)
Definition CheckedCertificate (B : N) (index : PositiveMap.t TM)
    (family : TM) (parents : list TM) (root : positive) (depth : nat) : Prop :=
  exists words : list N,
    unit_check B index (unit_data family parents words root depth) = true.

Theorem existential_unit_sound : forall B index family parents root depth,
  IndexSound (N.to_nat B) index ->
  StateBoardSound (N.to_nat B) parents ->
  CheckedCertificate B index family parents root depth ->
  FamilyBound (N.to_nat B) family.
Proof.
  intros B index family parents root depth HI HP [words HC].
  exact (unit_sound B index (unit_data family parents words root depth) HI HP HC).
Qed.

Print Assumptions indexed_target_bound.
Print Assumptions transfer_state_sound.
Print Assumptions aggregate_index_sound.
Print Assumptions existential_unit_sound.
