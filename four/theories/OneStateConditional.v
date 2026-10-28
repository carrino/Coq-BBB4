(** Partial-table state recurrence conditional on a separate nonhalting proof.
    Undefined cells are completed toward each goal independently. NonHalt
    ensures that neither artificial completion changes the actual blank run. *)
From Coq Require Import Bool Lia.
From BBB24 Require Import Statement Spec CTape Census TotalCompletion OneStateReach.

Definition orc_fill_goal (tm : TM) (goal : St) : TM := fun q s =>
  match tm q s with
  | Some tr => Some tr
  | None => Some (mkTrans S0 DR goal)
  end.
Lemma orc_fill_extends : forall tm goal, TM_le tm (orc_fill_goal tm goal).
Proof.
  intros tm goal q s. unfold orc_fill_goal.
  destruct (tm q s); [right|left]; reflexivity.
Qed.
Lemma orc_fill_total : forall tm goal, Total (orc_fill_goal tm goal).
Proof.
  intros tm goal q s. unfold orc_fill_goal. destruct (tm q s); eexists; reflexivity.
Qed.
Theorem orc_goal_recurs : forall tm goal,
  NonHalt tm -> ore_auto_goal (orc_fill_goal tm goal) goal=true ->
  forall N, exists n, N<=n /\ VisitsAt tm goal n.
Proof.
  intros tm goal Hnh Hcheck N.
  destruct (ore_reaches_recurs (orc_fill_goal tm goal) goal (orc_fill_total tm goal)
    (ore_auto_goal_sound _ _ Hcheck) N) as (n&Hn&cc&Hrun&Hgoal).
  exists n. split; [exact Hn|]. exists cc. split; [|exact Hgoal].
  rewrite (extend_run tm (orc_fill_goal tm goal) Hnh (orc_fill_extends tm goal) n) in Hrun.
  exact Hrun.
Qed.
Definition orc_state_check tm :=
  ore_auto_goal (orc_fill_goal tm StA) StA &&
  ore_auto_goal (orc_fill_goal tm StB) StB.
Theorem orc_state_check_sound : forall tm,
  NonHalt tm -> orc_state_check tm=true -> QHBound 0 tm.
Proof.
  intros tm Hnh Hcheck. apply andb_prop in Hcheck as [Ha Hb].
  intros q s [_ Hquiet].
  assert (Hrec : exists n, S s<=n /\ VisitsAt tm q n).
  { destruct q; eapply orc_goal_recurs; eauto. }
  destruct Hrec as (n&Hn&Hvisit). exfalso. apply (Hquiet n); [lia|exact Hvisit].
Qed.
Print Assumptions orc_state_check_sound.
