(** Structural composition of conditional census units. No frontier family is
    discharged here: its bound remains an explicit hypothesis. *)
From Coq Require Import List.
From BBB24 Require Import Statement Spec Census StateOnlyCloseout.
Import ListNotations.

Lemma frontier_parts : forall B local dependencies,
  StateBoardSound B (local ++ concat dependencies) ->
  StateBoardSound B local /\ Forall (StateBoardSound B) dependencies.
Proof.
  intros B local dependencies H. split.
  - intros family Hin complete Hle. apply (H family); [apply in_or_app;auto|exact Hle].
  - apply Forall_forall. intros board Hb family Hin complete Hle.
    apply (H family); [|exact Hle]. apply in_or_app;right.
    apply in_concat. exists board;auto.
Qed.

Lemma board_app : forall B first second,
  StateBoardSound B first -> StateBoardSound B second ->
  StateBoardSound B (first ++ second).
Proof.
  intros B first second Hfirst Hsecond family Hin complete Hle.
  apply in_app_or in Hin as [Hin|Hin]; [apply (Hfirst family)|apply (Hsecond family)];assumption.
Qed.

Lemma board_cons : forall B family rest,
  (forall complete, TM_le family complete -> QHBound B complete) ->
  StateBoardSound B rest -> StateBoardSound B (family::rest).
Proof.
  intros B family rest Hfamily Hrest target [<-|Hin] complete Hle.
  - exact (Hfamily complete Hle).
  - exact (Hrest target Hin complete Hle).
Qed.

Lemma board_nil : forall B, StateBoardSound B [].
Proof. intros B family H;contradiction. Qed.

Print Assumptions frontier_parts.
Print Assumptions board_app.
