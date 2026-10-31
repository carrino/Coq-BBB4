(** Small source boards for unconditional blank-frontier transports. *)
From Coq Require Import List Bool NArith.
From BBB24 Require Import Statement Spec Census Closeout StateOnlyCloseout
  StatePipeline StateBranchJoin OneStateReach FamilyIndex Symmetry BoardManifest.
From BBB24Burn10StateCensus Require Import StateCensus StateShadow.
Import ListNotations.

Definition projection_check original selected :=
  let index := family_index original in
  forallb (fun family => state_lookup_check index family
    (state_lookup (family_key family) P123 false)) selected.

Lemma projection_state_sound : forall B original selected,
  StateBoardSound B original -> projection_check original selected = true ->
  StateBoardSound B selected.
Proof.
  intros B original selected Hsound H family Hin complete Hle.
  unfold projection_check in H.
  apply forallb_forall with (x:=family) in H; [|exact Hin].
  exact (state_lookup_sound B original family _ Hsound H complete Hle).
Qed.

Lemma direct_reach_state_sound : forall board,
  forallb ore_auto_state board = true -> StateBoardSound 0 board.
Proof.
  intros board H family Hin complete Hle.
  apply forallb_forall with (x:=family) in H; [|exact Hin].
  destruct (ore_auto_state_sound family H) as [Hnh Hb].
  exact (state_bound_extend 0 family complete Hnh Hb Hle).
Qed.

Record BlankRow := blank_row {
  target_code : N;
  source_code : N;
  row_permutation : SymPerm;
  row_mirrored : bool
}.
Definition row_target row := stp_machine (target_code row).
Definition row_witness row := state_lookup (family_key (stp_machine (source_code row)))
  (row_permutation row) (row_mirrored row).
Definition blank_board rows := map row_target rows.
Definition blank_batch_check sources rows :=
  let index := family_index sources in
  forallb (fun row => state_shadow_check index (row_target row) (row_witness row)) rows.

Theorem blank_batch_state_sound : forall bound sources rows,
  StateBoardSound (N.to_nat bound) sources -> blank_batch_check sources rows = true ->
  StateBoardSound (N.to_nat (N.succ bound)) (blank_board rows).
Proof.
  intros bound sources rows Hsound H. rewrite N2Nat.inj_succ.
  intros family Hin complete Hle.
  apply in_map_iff in Hin as (row & <- & Hin).
  unfold blank_batch_check in H.
  apply forallb_forall with (x:=row) in H; [|exact Hin].
  exact (state_shadow_sound (N.to_nat bound) sources _ _ Hsound H complete Hle).
Qed.

Definition exact_members_check selected frontier :=
  forallb (fun target => existsb (table_same target) frontier) selected.
Lemma exact_members_sound : forall selected frontier,
  exact_members_check selected frontier = true ->
  forall family, In family selected -> In family frontier.
Proof.
  intros selected frontier H family Hin.
  apply forallb_forall with (x:=family) in H; [|exact Hin].
  apply existsb_exists in H as (member & Hmember & E).
  apply table_same_sound in E. now rewrite E.
Qed.

Print Assumptions blank_batch_state_sound.
