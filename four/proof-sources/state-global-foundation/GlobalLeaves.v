(** Reuse complete, proved source inventories without rebuilding a selected
    source board for each census unit. This module proves only generic
    conditional contracts, not any particular unit or global upper bound. *)
From Coq Require Import List Bool NArith Lia FSets.FMapPositive.
From BBB24 Require Import Statement Spec Census Closeout StateOnlyCloseout
  StatePipeline OneStateReach FamilyIndex Symmetry FamilyTransport OrbitCloseout
  BranchCloseout.
From BBB24Burn10StateCensus Require Import StateCensus.
Import ListNotations.

Definition IndexSound (B : nat) (index : PositiveMap.t TM) :=
  forall key source, PositiveMap.find key index = Some source ->
  forall complete, TM_le source complete -> QHBound B complete.

Lemma board_index_sound : forall B board,
  StateBoardSound B board -> IndexSound B (family_index board).
Proof.
  intros B board HB key source Hfind complete Hle.
  exact (HB source (family_index_member board key source Hfind) complete Hle).
Qed.

Lemma indexed_leaf_sound : forall B index target witness,
  IndexSound B index -> state_lookup_check index target witness = true ->
  forall complete, TM_le target complete -> QHBound B complete.
Proof.
  intros B index target witness HI Hcheck complete Hle.
  unfold state_lookup_check in Hcheck.
  destruct (PositiveMap.find (lookup_key witness) index) as [source|] eqn:E;
    [|discriminate].
  apply table_leb_spec in Hcheck.
  apply (image_state_bound_back B (lookup_permutation witness)
      (lookup_mirrored witness) complete).
  apply (HI _ _ E). eapply branch_tm_le_trans; [exact Hcheck|].
  apply image_extends; exact Hle.
Qed.

Inductive GlobalWitness :=
| Known (witness : StateLookup)
| Parent (witness : StateLookup)
| Reach (source_packed : N) (permutation : SymPerm) (mirrored : bool).

Definition reach_leaf_check target source_packed p mirrored :=
  let source := stp_machine source_packed in
  ore_auto_state source && table_leb source (image_tm p mirrored target).

Lemma reach_leaf_sound : forall B target source_packed p mirrored,
  reach_leaf_check target source_packed p mirrored = true ->
  forall complete, TM_le target complete -> QHBound B complete.
Proof.
  intros B target source_packed p mirrored H complete Hle.
  unfold reach_leaf_check in H. apply andb_prop in H as [Ha Htable].
  apply table_leb_spec in Htable.
  destruct (ore_auto_state_sound _ Ha) as [Hnh Hzero].
  assert (Hz : QHBound 0 (image_tm p mirrored complete)).
  { eapply state_bound_extend; [exact Hnh|exact Hzero|].
    eapply branch_tm_le_trans; [exact Htable|]. apply image_extends; exact Hle. }
  pose proof (image_state_bound_back 0 p mirrored complete Hz) as HT.
  intros q s Hquiet. specialize (HT q s Hquiet). lia.
Qed.

Definition global_leaf_check (global parents : PositiveMap.t TM)
    target witness :=
  match witness with
  | Known w => state_lookup_check global target w
  | Parent w => state_lookup_check parents target w
  | Reach n p mirrored => reach_leaf_check target n p mirrored
  end.

Theorem global_leaf_sound : forall B global parents,
  IndexSound B global -> IndexSound B parents ->
  forall target witness, global_leaf_check global parents target witness = true ->
  forall complete, TM_le target complete -> QHBound B complete.
Proof.
  intros B global parents HG HP target [w|w|n p mirrored] H.
  - exact (indexed_leaf_sound B global target w HG H).
  - exact (indexed_leaf_sound B parents target w HP H).
  - exact (reach_leaf_sound B target n p mirrored H).
Qed.

Corollary global_certificate_sound : forall B global parents depth family cert,
  IndexSound (N.to_nat B) global -> IndexSound (N.to_nat B) parents ->
  state_verify B GlobalWitness (global_leaf_check global parents)
    depth family cert = true ->
  forall complete, TM_le family complete -> QHBound (N.to_nat B) complete.
Proof.
  intros B global parents depth family cert HG HP HC.
  exact (state_verify_sound B GlobalWitness (global_leaf_check global parents)
    (global_leaf_sound (N.to_nat B) global parents HG HP)
    depth family cert HC).
Qed.

Print Assumptions board_index_sound.
Print Assumptions indexed_leaf_sound.
Print Assumptions reach_leaf_sound.
Print Assumptions global_certificate_sound.
