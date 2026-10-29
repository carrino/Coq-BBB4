(** State-only one-blank-step transport. The source bound gains exactly one
    prefix step, and the caller must separately fit that bound under score. *)
From Coq Require Import Arith Lia List NArith PArith FSets.FMapPositive.
From BBB24 Require Import Statement Spec Census Closeout Shadow
  StateOnlyCloseout FamilyIndex FamilyTransport OrbitCloseout.
From BBB24Burn10StateCensus Require Import StateCensus.
Import ListNotations.

Lemma swap_extends : forall family complete,
  TM_le family complete -> TM_le (swap_tm family) (swap_tm complete).
Proof.
  intros family complete Hle q s. unfold swap_tm.
  destruct (Hle (swap_state q) s) as [E|E]; rewrite E; auto.
Qed.

Lemma blank_shadow_state_bound : forall B tm direction,
  tm StA S0 = Some (mkTrans S0 direction StB) ->
  QHBound B (swap_tm tm) -> QHBound (S B) tm.
Proof.
  intros B tm direction Hfirst Hcore q [|n] Hquiet; [lia|].
  assert (Hq : QuietAfter (swap_tm tm) (swap_state q) n).
  { apply (blank_shadow_quiet tm direction Hfirst).
    now rewrite swap_state_involutive. }
  specialize (Hcore _ _ Hq). lia.
Qed.

Definition state_shadow_check index family witness :=
  match family StA S0 with
  | Some (mkTrans S0 _ StB) => state_lookup_check index (swap_tm family) witness
  | _ => false
  end.

Theorem state_shadow_sound : forall B board family witness,
  StateBoardSound B board ->
  state_shadow_check (family_index board) family witness = true ->
  forall complete, TM_le family complete -> QHBound (S B) complete.
Proof.
  intros B board family witness Hboard H complete Hle.
  unfold state_shadow_check in H.
  destruct (family StA S0) as [[written direction next]|] eqn:E; [|discriminate].
  destruct written,next; try discriminate.
  assert (Ecomplete : complete StA S0 = Some (mkTrans S0 direction StB)).
  { destruct (Hle StA S0) as [Hnone|Hsame]; congruence. }
  apply (blank_shadow_state_bound B complete direction Ecomplete).
  apply (state_lookup_sound B board (swap_tm family) witness Hboard H).
  apply swap_extends; exact Hle.
Qed.

Corollary state_shadow_with_budget : forall B limit board family witness,
  S B <= limit -> StateBoardSound B board ->
  state_shadow_check (family_index board) family witness = true ->
  forall complete, TM_le family complete -> QHBound limit complete.
Proof.
  intros B limit board family witness Hbudget Hboard H complete Hle q n Hquiet.
  pose proof (state_shadow_sound B board family witness Hboard H complete Hle q n Hquiet).
  lia.
Qed.

Print Assumptions state_shadow_with_budget.
