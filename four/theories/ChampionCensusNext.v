(** A separate exact census board for the reflected known champion.
    The historical small-bound campaign and its champion control are unchanged.
    All computations below inspect finite tables or the bounded census path;
    none evaluates [N.to_nat scoreN]. *)
From Coq Require Import List NArith.
From BBB24 Require Import Statement StatementTr Spec Champion Bounds Census
  Mirror CycleCensus Bootstrap Closeout BoardManifest.
Import ListNotations.

Local Opaque scoreN previousN.

Definition canonical_champion : TM := mirror_tm champion.

Theorem canonical_champion_nonhalting : NonHalt canonical_champion.
Proof.
  intros n H. unfold canonical_champion in H.
  rewrite mirror_stepn_init in H.
  pose proof (champion_nonhalting n) as Hnh.
  destruct (stepn champion n InitES); congruence.
Qed.

Theorem canonical_champion_bounds : Bounds scoreN scoreN canonical_champion.
Proof.
  split; intros q s [Hv Hquiet].
  - apply (champion_state_bound q s). split.
    + apply mirror_visits; exact Hv.
    + intros n Hn Hvisit. apply (Hquiet n Hn).
      apply mirror_visits; exact Hvisit.
  - apply (champion_instruction_bound q s). split.
    + apply mirror_fires; exact Hv.
    + intros n Hn Hfire. apply (Hquiet n Hn).
      apply mirror_fires; exact Hfire.
Qed.

Theorem canonical_champion_attains_state : AttainsSt canonical_champion score.
Proof.
  destruct champion_attains_state as (q & s & [Hv Hquiet] & Hscore).
  exists q, s. split; [split|exact Hscore].
  - apply mirror_visits; exact Hv.
  - intros n Hn Hvisit. apply (Hquiet n Hn).
    apply mirror_visits; exact Hvisit.
Qed.

Theorem canonical_champion_attains_instruction : AttainsTr canonical_champion score.
Proof.
  destruct champion_attains_instruction as (q & s & [Hv Hquiet] & Hscore).
  exists q, s. split; [split|exact Hscore].
  - apply mirror_fires; exact Hv.
  - intros n Hn Hfire. apply (Hquiet n Hn).
    apply mirror_fires; exact Hfire.
Qed.

Theorem canonical_champion_exact : NonHalt canonical_champion /\
  (QHBound score canonical_champion /\ AttainsSt canonical_champion score) /\
  (QHBoundTr score canonical_champion /\ AttainsTr canonical_champion score).
Proof.
  destruct canonical_champion_bounds as [Hs Hi].
  exact (conj canonical_champion_nonhalting
    (conj (conj Hs canonical_champion_attains_state)
      (conj Hi canonical_champion_attains_instruction))).
Qed.

(** Every cell is specified, so a completion agrees at every table cell. *)
Lemma canonical_champion_total : forall q s, canonical_champion q s <> None.
Proof. destruct q, s; discriminate. Qed.
Lemma canonical_champion_completion : forall complete,
  TM_le canonical_champion complete ->
  forall q s, complete q s = canonical_champion q s.
Proof.
  intros complete Hle q s.
  destruct (Hle q s) as [Hnone|Heq]; [|exact Heq].
  exfalso. exact (canonical_champion_total q s Hnone).
Qed.
Theorem canonical_champion_completion_exact : forall complete,
  TM_le canonical_champion complete -> NonHalt complete /\
  (QHBound score complete /\ AttainsSt complete score) /\
  (QHBoundTr score complete /\ AttainsTr complete score).
Proof.
  intros complete Hle.
  pose proof (extend_run canonical_champion complete
    canonical_champion_nonhalting Hle) as Hrun.
  unfold NonHalt, QHBound, QHBoundTr, AttainsSt, AttainsTr,
    QuietAfter, QuietAfterTr, VisitsAt, FiresAt.
  setoid_rewrite Hrun.
  exact canonical_champion_exact.
Qed.

Definition champion_census_board : list TM := [canonical_champion].
Theorem champion_census_board_sound :
  BoardSound scoreN scoreN champion_census_board.
Proof.
  intros family [<-|Hfalse] complete Hle; [|contradiction].
  exact (extend_bounds scoreN scoreN canonical_champion complete
    canonical_champion_nonhalting canonical_champion_bounds Hle).
Qed.

(** This path check proves membership in the formal frozen pending predicate,
    independently of membership in an external comparison cohort. *)
Lemma canonical_champion_pending_checked :
  pending_check 9 empty bootstrap canonical_champion = true.
Proof. vm_compute. reflexivity. Qed.
Theorem champion_census_board_pending : forall family,
  In family champion_census_board -> bootstrap_pending family.
Proof.
  intros family [<-|Hfalse]; [|contradiction].
  exact (pending_check_sound 9 empty bootstrap canonical_champion
    canonical_champion_pending_checked).
Qed.

(** Base-17 packing uses A0,A1,A2,A3,B0,B1,B2,B3 and the established
    trans_code convention. The exact external ID is
    1LB2RA1LA1RB_0RB2LB3LB1RA. *)
Definition champion_census_rows : list N := [2788885433%N].
Lemma champion_census_inventory_checked :
  manifest_check champion_census_rows champion_census_board = true.
Proof. vm_compute. reflexivity. Qed.
Theorem champion_census_inventory_exact :
  manifest_board champion_census_rows = champion_census_board.
Proof. apply manifest_check_sound. exact champion_census_inventory_checked. Qed.

Theorem champion_census_coverage : forall tm,
  Bounds scoreN scoreN tm \/ remaining bootstrap_pending champion_census_board tm.
Proof.
  apply closeout_coverage; [exact bootstrap_coverage|exact champion_census_board_sound].
Qed.
Theorem champion_census_discharged :
  ~ remaining bootstrap_pending champion_census_board canonical_champion.
Proof. intros [_ Hmiss]. discriminate Hmiss. Qed.

Print Assumptions canonical_champion_exact.
Print Assumptions canonical_champion_completion_exact.
Print Assumptions champion_census_board_sound.
Print Assumptions champion_census_board_pending.
Print Assumptions champion_census_inventory_exact.
Print Assumptions champion_census_coverage.
