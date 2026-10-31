(** Candidate final assembly only. This file has not been compiled.
    It may be used only after the actual448 boolean checks, all family proofs,
    and the shared source-index soundness have passed their kernel audits. *)
From Coq Require Import List.
From BBB24 Require Import Statement Spec Champion ValueSpec Census StateOnlyCloseout.
From BBB24Burn10StateCensus Require Import RootBridge.
From BBB24Burn15BlankCloseout Require Import BlankBound.
From BBB24GlobalUnits Require Import Assembly.
From BBB24OpaqueCensus448 Require Import Metadata Bounds.
Import ListNotations.
Local Opaque scoreN.

Theorem nonblank_root_bound : FamilyBound score RootBridge.nonblank_root.
Proof. exact bound_447. Qed.

Theorem blank_root_bound : FamilyBound score RootBridge.blank_root.
Proof. exact BlankBound.blank_family_score. Qed.

Theorem all_machines_state_bound : forall tm, QHBound score tm.
Proof.
  apply RootBridge.two_root_state_upper.
  intros family [<-|[<-|Hfalse]].
  - exact blank_root_bound.
  - exact nonblank_root_bound.
  - contradiction.
Qed.

Theorem BBB24_state_value : ValueSpec.BBB24_state_statement.
Proof.
  split.
  - exists champion. exact Champion.champion_attains_state.
  - exact all_machines_state_bound.
Qed.

(** Deliberately no recursive Print Assumptions over the entire final closure.
    The actual compiled objects still require fresh V3 kernel audits. *)
