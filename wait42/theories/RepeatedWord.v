(** Quantitative repeated-word tails. Only finite graph ranks are accepted;
    the unbounded tape measures of the qualitative RepWL checker are absent.
    The cutoff B is a theorem parameter, never a simulation argument. *)
From Coq Require Import Arith Lia Bool List.
From BBB4 Require Import BBB4_Statement CTape PosEnc Closure.
From BBB4.Checkers Require Import RepWL.
From BBB4.Census Require Import TNF_QH.
From BBBWait42 Require Import Spec Ranked Transport.
Import ListNotations.

(** Resource cut, with the same fail-closed contract as the base checker. *)
Definition repwl_size (a : rconf) : nat :=
  let '(_, (li, lb, _, rb, ri)) := a in
  length li + length ri + length lb + length rb.
Definition repwl_succs (tm : TM) (L T M : nat) (a : rconf) :=
  if M <? repwl_size a then None else rw_succs tm L T a.

Lemma repwl_succs_sound : forall tm L T M a c,
  1 <= L -> 2 <= T -> rw_covers' a c ->
  match repwl_succs tm L T M a, step tm c with
  | Some sl, Some c' => exists a', In a' sl /\ rw_covers' a' c'
  | Some _, None => False | None, _ => True end.
Proof.
  intros tm L T M a c HL HT Hc. unfold repwl_succs.
  destruct (M <? repwl_size a); [destruct (step tm c); exact I|].
  apply rw_succs_sound'; assumption.
Qed.

(** Supplied pool and ranks are untrusted data. Seed membership, every
    successor, and every rank inequality are checked again. *)
Definition repwl_ranked_tail_ok (tm : TM) (L T M : nat) (cc : cconf)
    (pool : list rconf) (ranks : St -> rconf -> nat) (w : nat) :=
  (1 <=? L) && (2 <=? T) &&
  mem rconf rconf_enc (rw_seed L T cc) pool &&
  closed_b rconf rconf_enc (repwl_succs tm L T M) pool &&
  ranked_window_ok rw_state (repwl_succs tm L T M) pool ranks w.

Theorem repwl_ranked_tail_ok_sound : forall tm L T M cc pool ranks t B w,
  t <= B -> csteps tm t c0 = Some cc ->
  repwl_ranked_tail_ok tm L T M cc pool ranks w = true ->
  WindowBound tm B w.
Proof.
  intros tm L T M cc pool ranks t B w Ht Hanchor H.
  unfold repwl_ranked_tail_ok in H.
  apply andb_true_iff in H as [H Hrank].
  apply andb_true_iff in H as [H Hcl].
  apply andb_true_iff in H as [H Hmem].
  apply andb_true_iff in H as [HL HT].
  apply Nat.leb_le in HL. apply Nat.leb_le in HT.
  eapply (ranked_window_ok_window_bound tm rconf rconf_enc rw_state
    (repwl_succs tm L T M) rw_covers' rconf_enc_inj).
  - intros a c [Hcov _]. apply rw_covers_state. exact Hcov.
  - intros a c Hcov. apply repwl_succs_sound; assumption.
  - exact Hcl.
  - apply (mem_In rconf rconf_enc rconf_enc_inj). exact Hmem.
  - split; [apply rw_seed_covers | apply rw_seed_wf]; assumption.
  - rewrite <- lift_c0. apply csteps_lift. exact Hanchor.
  - exact Ht.
  - exact Hrank.
Qed.

Definition repwl_ranked_search (tm : TM) (L T M t fuel w : nat) :=
  match csteps tm t c0 with
  | Some cc =>
    match close rconf rconf_enc (repwl_succs tm L T M)
      fuel [] PositiveSet.empty [rw_seed L T cc] with
    | Some pool => repwl_ranked_tail_ok tm L T M cc pool
      (compute_ranks rconf rconf_enc rw_state (repwl_succs tm L T M) pool) w
    | None => false end
  | None => false end.

Theorem repwl_ranked_search_sound : forall tm L T M t fuel w B,
  t <= B -> repwl_ranked_search tm L T M t fuel w = true ->
  WindowBound tm B w.
Proof.
  intros tm L T M t fuel w B Ht H.
  unfold repwl_ranked_search in H.
  destruct (csteps tm t c0) as [cc|] eqn:Et; [|discriminate].
  destruct (close rconf rconf_enc (repwl_succs tm L T M)
    fuel [] PositiveSet.empty [rw_seed L T cc]) as [pool|]; [|discriminate].
  eapply repwl_ranked_tail_ok_sound; eauto.
Qed.

(** Closed tails also certify the partial table never reaches a hole. *)
Theorem repwl_ranked_tail_ok_nonhalt : forall tm L T M cc pool ranks t w,
  csteps tm t c0 = Some cc ->
  repwl_ranked_tail_ok tm L T M cc pool ranks w = true -> NonHalt tm.
Proof.
  intros tm L T M cc pool ranks t w Hanchor H.
  unfold repwl_ranked_tail_ok in H.
  apply andb_true_iff in H as [H _].
  apply andb_true_iff in H as [H Hcl].
  apply andb_true_iff in H as [H Hmem].
  apply andb_true_iff in H as [HL HT].
  apply Nat.leb_le in HL. apply Nat.leb_le in HT.
  assert (Hcov : rw_covers' (rw_seed L T cc) (lift cc)).
  { split; [apply rw_seed_covers | apply rw_seed_wf]; assumption. }
  apply (mem_In rconf rconf_enc rconf_enc_inj) in Hmem.
  intros n Hnone.
  destruct (closure_invariant tm rconf rconf_enc (repwl_succs tm L T M)
    rw_covers' rconf_enc_inj
    (fun a c Hc => repwl_succs_sound tm L T M a c HL HT Hc)
    pool Hcl (rw_seed L T cc) (lift cc) Hmem Hcov n)
    as (cn & an & Hsteps & _).
  assert (Hrun : stepn tm t InitES = Some (lift cc)).
  { rewrite <- lift_c0. apply csteps_lift. exact Hanchor. }
  assert (Hlong : stepn tm (t+n) InitES = Some cn).
  { rewrite stepn_add, Hrun. exact Hsteps. }
  replace (t+n) with (n+t) in Hlong by lia.
  rewrite stepn_add, Hnone in Hlong. discriminate.
Qed.

Theorem repwl_ranked_search_nonhalt : forall tm L T M t fuel w,
  repwl_ranked_search tm L T M t fuel w = true -> NonHalt tm.
Proof.
  intros tm L T M t fuel w H. unfold repwl_ranked_search in H.
  destruct (csteps tm t c0) as [cc|] eqn:Et; [|discriminate].
  destruct (close rconf rconf_enc (repwl_succs tm L T M)
    fuel [] PositiveSet.empty [rw_seed L T cc]) as [pool|]; [|discriminate].
  eapply repwl_ranked_tail_ok_nonhalt; eauto.
Qed.

Theorem repwl_ranked_search_completion : forall tm L T M t fuel w B,
  t <= B -> repwl_ranked_search tm L T M t fuel w = true ->
  forall tm', TM_le tm tm' -> WindowBound tm' B w.
Proof.
  intros tm L T M t fuel w B Ht H tm' Hle.
  apply (proj2 (window_bound_completion tm tm' B w
    (repwl_ranked_search_nonhalt tm L T M t fuel w H) Hle)).
  eapply repwl_ranked_search_sound; eauto.
Qed.

Module RepeatedWordRegression.
Definition alternating : TM := fun q _ =>
  Some (mkTrans S0 DR (match q with StA => StB | _ => StA end)).
Example alternating_accept : repwl_ranked_search alternating 1 2 16 0 64 1 = true.
Proof. vm_compute. reflexivity. Qed.
Example alternating_zero_reject : repwl_ranked_search alternating 1 2 16 0 64 0 = false.
Proof. vm_compute. reflexivity. Qed.
Theorem alternating_window : forall B, WindowBound alternating B 1.
Proof.
  intro B. apply (repwl_ranked_search_sound alternating 1 2 16 0 64 1 B);
    [lia|exact alternating_accept].
Qed.
End RepeatedWordRegression.

(** First bounded residual experiment: row index 16 of the tail census,
    machine 0RB0LC_1LA1RB_1LB1LD_1RD1RA. The other 99 rows remain
    unresolved by this bounded experiment. The window is a finite-graph
    upper bound, without a claim of sharpness. *)
Module RepeatedWordResidual.
Definition residual_16 : TM := fun q s => match q, s with
| StA, S0 => Some (mkTrans S0 DR StB)
| StA, S1 => Some (mkTrans S0 DL StC)
| StB, S0 => Some (mkTrans S1 DL StA)
| StB, S1 => Some (mkTrans S1 DR StB)
| StC, S0 => Some (mkTrans S1 DL StB)
| StC, S1 => Some (mkTrans S1 DL StD)
| StD, S0 => Some (mkTrans S1 DR StD)
| StD, S1 => Some (mkTrans S1 DR StA)
end.
Example residual_16_checked : repwl_ranked_search residual_16 3 2 64 0 918 456 = true.
Proof. vm_compute. reflexivity. Qed.
Theorem residual_16_window : forall B, 0 <= B -> WindowBound residual_16 B 456.
Proof. intros B HB. eapply repwl_ranked_search_sound; [exact HB|exact residual_16_checked]. Qed.
End RepeatedWordResidual.

Theorem repeated_word_residual_16_completion : forall tm' B,
  TM_le RepeatedWordResidual.residual_16 tm' -> WindowBound tm' B 456.
Proof.
  intros tm' B Hle.
  eapply (repwl_ranked_search_completion RepeatedWordResidual.residual_16
    3 2 64 0 918 456 B); [lia|exact RepeatedWordResidual.residual_16_checked|exact Hle].
Qed.
