(** Short-circuiting implementations of waiting certificates. The proofs
    reuse the checked suffix invariants; evaluation avoids excluded targets. *)
From Coq Require Import Arith Lia Bool List.
From SmallBB Require Import Statement StatementTr CTape ClosureTr Bounds
  CycleCensus Mirror.
From SmallBB.Checkers Require Import Cycle.
From BBBWait Require Import Spec SpecTr Checker CheckerTr Static Tail.
Import ListNotations.

Fixpoint quick_visits tm c len q :=
  match len with
  | 0 => false
  | S n => if st_eqb (fst c) q then true else
      match cstep tm c with Some d => quick_visits tm d n q | None => false end
  end.

Lemma quick_visits_eq : forall tm len c q,
  quick_visits tm c len q = cvisits tm c len q.
Proof.
  intros tm len; induction len; intros c q; [reflexivity|].
  cbn [quick_visits cvisits]; destruct (st_eqb (fst c) q); [reflexivity|].
  destruct (cstep tm c); [apply IHlen|reflexivity].
Qed.

(** Build one shared trace of instruction labels. Queries may traverse
    that trace, but stepping and tape allocation occur only once. *)
Fixpoint trace_observed tm c len : Instr -> bool :=
  match len with
  | 0 => fun _ => false
  | S n =>
    let rest := match cstep tm c with
      | Some d => trace_observed tm d n
      | None => fun _ => false end in
    let current := cinstr c in
    fun tg => if instr_eqb current tg then true else rest tg
  end.

Lemma trace_observed_eq : forall tm len c tg,
  trace_observed tm c len tg = cfires tm c len tg.
Proof.
  intros tm len; induction len; intros c tg; [reflexivity|].
  cbn [trace_observed cfires]; destruct (instr_eqb (cinstr c) tg); [reflexivity|].
  destruct (cstep tm c); [apply IHlen|reflexivity].
Qed.

(** [cfires] already stops at its first match. Filter excluded read symbols
    before invoking it, then cache the nine resulting booleans. *)
Definition quick_observed tm cb w (allowed : Sym -> bool) (tg : Instr) :=
  if allowed (snd tg) then cfires tm cb (S w) tg else false.
Definition fast_observed_instr tm cb w (allowed : Sym -> bool) :=
  let obs := trace_observed tm cb (S w) in
  instr_mask (if allowed S0 then obs (StA,S0) else false)
    (if allowed S1 then obs (StA,S1) else false)
    (if allowed S2 then obs (StA,S2) else false)
    (if allowed S0 then obs (StB,S0) else false)
    (if allowed S1 then obs (StB,S1) else false)
    (if allowed S2 then obs (StB,S2) else false)
    (if allowed S0 then obs (StC,S0) else false)
    (if allowed S1 then obs (StC,S1) else false)
    (if allowed S2 then obs (StC,S2) else false).

Lemma fast_observed_instr_sound : forall tm cb w allowed tg,
  fast_observed_instr tm cb w allowed tg = true -> cfires tm cb (S w) tg = true.
Proof.
  intros tm cb w allowed [q h]; destruct q,h;
    unfold fast_observed_instr; cbn [instr_mask];
    destruct (allowed S0), (allowed S1), (allowed S2); try discriminate;
    rewrite trace_observed_eq; auto.
Qed.

Lemma fast_forallb_ext : forall A (xs : list A) (f g : A -> bool),
  (forall x, In x xs -> f x = g x) -> forallb f xs = forallb g xs.
Proof.
  intros A xs; induction xs as [|x xs IH]; intros f g H; [reflexivity|].
  cbn; rewrite (H x (or_introl eq_refl)); f_equal.
  apply IH; intros y Hy; apply H; now right.
Qed.

Definition fast_instr_closed_mask tm (allowed : Sym -> bool) (seen : Instr -> bool) :=
  allb_tr (fun tg => if seen tg then
    match tm (fst tg) (snd tg) with
    | None => true
    | Some tr => if allowed (t_write tr) then allb_tr
      (fun h => if allowed h then seen (t_next tr,h) else true) [S0;S1;S2]
      else false
    end else true) all_Instr.

Lemma fast_instr_closed_mask_eq : forall tm allowed seen,
  fast_instr_closed_mask tm allowed seen = instr_closed_mask tm allowed seen.
Proof.
  intros tm allowed seen; unfold fast_instr_closed_mask, instr_closed_mask.
  rewrite allb_tr_eq; apply fast_forallb_ext; intros [q h] _.
  destruct (seen (q,h)); [|reflexivity].
  cbn [fst snd]; destruct (tm q h) as [tr|]; [|reflexivity].
  destruct (allowed (t_write tr)); [apply allb_tr_eq|reflexivity].
Qed.

Definition fast_static_instr_from tm cb w d allowed :=
  if tape_alphabet allowed (snd d) then
    let seen := fast_observed_instr tm cb w allowed in
    if seen (cinstr d) then fast_instr_closed_mask tm allowed seen else false
  else false.

Definition fast_static_instr_alphabet_check tm B w allowed :=
  match csteps tm B c0 with
  | None => true
  | Some cb => match csteps tm w cb with
    | None => true
    | Some d => fast_static_instr_from tm cb w d allowed
    end
  end.

Lemma fast_static_instr_from_sound : forall tm cb w d allowed,
  fast_static_instr_from tm cb w d allowed = true -> forall n ct,
  csteps tm n d = Some ct -> cfires tm cb (S w) (cinstr ct) = true.
Proof.
  intros tm cb w d allowed H n ct E.
  unfold fast_static_instr_from in H.
  destruct (tape_alphabet allowed (snd d)) eqn:Ha; [|discriminate].
  destruct (fast_observed_instr tm cb w allowed (cinstr d)) eqn:Hd; [|discriminate].
  rewrite fast_instr_closed_mask_eq in H.
  apply (fast_observed_instr_sound tm cb w allowed (cinstr ct)).
  eapply instr_closed_mask_run; eauto.
Qed.

Lemma fast_static_instr_alphabet_check_sound : forall tm B w allowed,
  fast_static_instr_alphabet_check tm B w allowed = true ->
  forall tg, FutureBeepTr tm tg B -> BeepWindowTr tm tg B w.
Proof.
  intros tm B w allowed H tg (t & Ht & Hv).
  destruct (le_lt_dec t (B+w)) as [Hle|Hlt].
  - exists t; auto.
  - destruct (fires_computable tm t tg Hv) as (ct & Et & Htg).
    destruct (csteps_prefix tm B t c0 ct Ht Et) as (cb & Eb & Ebt).
    destruct (csteps_prefix tm w (t-B) cb ct ltac:(lia) Ebt)
      as (d & Ed & Edt).
    unfold fast_static_instr_alphabet_check in H; rewrite Eb, Ed in H.
    pose proof (fast_static_instr_from_sound tm cb w d allowed H
      (t-B-w) ct Edt) as Htarget.
    rewrite Htg in Htarget.
    destruct (cfires_sound tm (S w) cb tg Htarget)
      as (i & ci & Hi & Ei & Hqi).
    exists (B+i); repeat split; try lia.
    exists (lift ci); split; [|rewrite cinstr_lift; exact Hqi].
    rewrite <- lift_c0; apply csteps_lift; rewrite csteps_add, Eb; exact Ei.
Qed.

Definition fast_static_instr_check tm B w :=
  match csteps tm B c0 with
  | None => true
  | Some cb => match csteps tm w cb with
    | None => true
    | Some d => if fast_static_instr_from tm cb w d zero_alphabet then true
      else fast_static_instr_from tm cb w d binary_alphabet
    end
  end.

Lemma fast_static_instr_check_sound : forall tm B w,
  fast_static_instr_check tm B w = true ->
  forall tg, FutureBeepTr tm tg B -> BeepWindowTr tm tg B w.
Proof.
  intros tm B w H; unfold fast_static_instr_check in H.
  destruct (csteps tm B c0) as [cb|] eqn:Eb.
  - destruct (csteps tm w cb) as [d|] eqn:Ed.
    + destruct (fast_static_instr_from tm cb w d zero_alphabet) eqn:Hz.
      * apply (fast_static_instr_alphabet_check_sound tm B w zero_alphabet).
        unfold fast_static_instr_alphabet_check; now rewrite Eb,Ed.
      * apply (fast_static_instr_alphabet_check_sound tm B w binary_alphabet).
        unfold fast_static_instr_alphabet_check; now rewrite Eb,Ed.
    + apply (fast_static_instr_alphabet_check_sound tm B w binary_alphabet).
      unfold fast_static_instr_alphabet_check; now rewrite Eb,Ed.
  - apply (fast_static_instr_alphabet_check_sound tm B w binary_alphabet).
    unfold fast_static_instr_alphabet_check; now rewrite Eb.
Qed.

(** The ternary development can opt into the full alphabet without adding
    an expensive failed fallback to binary census checks. *)
Definition full_alphabet (_ : Sym) : bool := true.
Definition fast_static_instr_check_full tm B w :=
  match csteps tm B c0 with
  | None => true
  | Some cb => match csteps tm w cb with
    | None => true
    | Some d => if fast_static_instr_from tm cb w d zero_alphabet then true
      else if fast_static_instr_from tm cb w d binary_alphabet then true
      else fast_static_instr_from tm cb w d full_alphabet
    end
  end.

Lemma fast_static_instr_check_full_sound : forall tm B w,
  fast_static_instr_check_full tm B w = true ->
  forall tg, FutureBeepTr tm tg B -> BeepWindowTr tm tg B w.
Proof.
  intros tm B w H; unfold fast_static_instr_check_full in H.
  destruct (csteps tm B c0) as [cb|] eqn:Eb.
  - destruct (csteps tm w cb) as [d|] eqn:Ed.
    + destruct (fast_static_instr_from tm cb w d zero_alphabet) eqn:Hz.
      * apply (fast_static_instr_alphabet_check_sound tm B w zero_alphabet).
        unfold fast_static_instr_alphabet_check; now rewrite Eb,Ed.
      * destruct (fast_static_instr_from tm cb w d binary_alphabet) eqn:Hb.
        -- apply (fast_static_instr_alphabet_check_sound tm B w binary_alphabet).
           unfold fast_static_instr_alphabet_check; now rewrite Eb,Ed.
        -- apply (fast_static_instr_alphabet_check_sound tm B w full_alphabet).
           unfold fast_static_instr_alphabet_check; now rewrite Eb,Ed.
    + apply (fast_static_instr_alphabet_check_sound tm B w full_alphabet).
      unfold fast_static_instr_alphabet_check; now rewrite Eb,Ed.
  - apply (fast_static_instr_alphabet_check_sound tm B w full_alphabet).
    unfold fast_static_instr_alphabet_check; now rewrite Eb.
Qed.

Definition fast_drift_check tm B :=
  match csteps tm B c0 with None => true | Some cb => drift_check tm cb end.

Lemma fast_drift_check_sound : forall tm B,
  fast_drift_check tm B = true -> forall w tg,
  FutureBeepTr tm tg B -> BeepWindowTr tm tg B w.
Proof.
  intros tm B H w tg (t & Ht & Hv).
  destruct (fires_computable tm t tg Hv) as (ct & Et & Htg).
  destruct (csteps_prefix tm B t c0 ct Ht Et) as (cb & Eb & Ebt).
  unfold fast_drift_check in H; rewrite Eb in H.
  pose proof (drift_instr_sound tm cb H (t-B) ct Ebt) as Heq.
  exists B; repeat split; try lia.
  exists (lift cb); split.
  - rewrite <- lift_c0; now apply csteps_lift.
  - rewrite cinstr_lift, <-Heq; exact Htg.
Qed.

Lemma fast_drift_check_state_sound : forall tm B,
  fast_drift_check tm B = true -> forall w q,
  FutureBeep tm q B -> BeepWindow tm q B w.
Proof.
  intros tm B H w q (t & Ht & Hv).
  apply visits_fires in Hv as (a & Hf).
  destruct (fast_drift_check_sound tm B H w (q,a)
    (ex_intro _ t (conj Ht Hf))) as (s & Hs & Hsw & Hfs).
  exists s; repeat split; try assumption; now apply fires_visits in Hfs.
Qed.

Definition fast_static_state_check tm B w :=
  match csteps tm B c0 with
  | None => true
  | Some cb =>
    let a := quick_visits tm cb (S w) StA in
    let b := quick_visits tm cb (S w) StB in
    let c := quick_visits tm cb (S w) StC in
    let seen := state_mask a b c in
    match csteps tm w cb with
    | None => true
    | Some d => seen (fst d) && state_closed_mask tm seen
    end
  end.

Lemma fast_static_state_check_eq : forall tm B w,
  fast_static_state_check tm B w = static_state_check tm B w.
Proof.
  intros tm B w; unfold fast_static_state_check,static_state_check.
  destruct (csteps tm B c0); [|reflexivity].
  repeat rewrite quick_visits_eq; reflexivity.
Qed.

Lemma fast_static_state_check_sound : forall tm B w,
  fast_static_state_check tm B w = true ->
  forall q, FutureBeep tm q B -> BeepWindow tm q B w.
Proof.
  intros tm B w H; rewrite fast_static_state_check_eq in H.
  exact (static_state_check_sound tm B w H).
Qed.

Definition fast_tail_state_gate tm B w Sl :=
  match csteps tm B c0 with
  | None => true
  | Some c => allb_tr (fun q => if tail_states Sl q then
      quick_visits tm c (S w) q else true) all_St
  end.

Lemma fast_tail_state_gate_eq : forall tm B w Sl,
  fast_tail_state_gate tm B w Sl = tail_state_gate tm B w Sl.
Proof.
  intros tm B w Sl; unfold fast_tail_state_gate,tail_state_gate.
  destruct (csteps tm B c0); [|reflexivity].
  rewrite allb_tr_eq; apply fast_forallb_ext; intros q _.
  destruct (tail_states Sl q); [apply quick_visits_eq|reflexivity].
Qed.

Definition fast_tc_wait_check_state tm B w (mirrored : bool) t p W :=
  if t <=? S (B+w) then
  let tm' := if mirrored then mirror_tm tm else tm in
  match tc_tail tm' t p W with
  | Some Sl => fast_tail_state_gate tm' B w Sl
  | None => false
  end else false.

Lemma fast_tc_wait_check_state_eq : forall tm B w mirrored t p W,
  fast_tc_wait_check_state tm B w mirrored t p W = tc_wait_check_state tm B w mirrored t p W.
Proof.
  intros tm B w mirrored t p W; unfold fast_tc_wait_check_state,tc_wait_check_state.
  destruct (t <=? S (B+w)); [|reflexivity].
  cbn [andb]. destruct (tc_tail (if mirrored then mirror_tm tm else tm) t p W);
    [apply fast_tail_state_gate_eq|reflexivity].
Qed.

Lemma fast_tc_wait_check_state_sound : forall tm B w mirrored t p W,
  fast_tc_wait_check_state tm B w mirrored t p W = true ->
  forall q, FutureBeep tm q B -> BeepWindow tm q B w.
Proof.
  intros tm B w mirrored t p W H; rewrite fast_tc_wait_check_state_eq in H.
  exact (tc_wait_check_state_sound tm B w mirrored t p W H).
Qed.

Definition fast_tail_instr_gate tm B w Sl :=
  match csteps tm B c0 with
  | None => true
  | Some c =>
    let obs := trace_observed tm c (S w) in
    allb_tr (fun tg => if tail_instrs Sl tg then obs tg else true) all_Instr
  end.

Lemma fast_tail_instr_gate_eq : forall tm B w Sl,
  fast_tail_instr_gate tm B w Sl = tail_instr_gate tm B w Sl.
Proof.
  intros tm B w Sl; unfold fast_tail_instr_gate,tail_instr_gate.
  destruct (csteps tm B c0); [|reflexivity].
  rewrite allb_tr_eq; apply fast_forallb_ext; intros tg _.
  destruct (tail_instrs Sl tg); [apply trace_observed_eq|reflexivity].
Qed.

Definition fast_tc_wait_check_tr tm B w (mirrored : bool) t p W :=
  if t <=? S (B+w) then
  let tm' := if mirrored then mirror_tm tm else tm in
  match tc_tail tm' t p W with
  | Some Sl => fast_tail_instr_gate tm' B w Sl
  | None => false
  end else false.

Lemma fast_tc_wait_check_tr_eq : forall tm B w mirrored t p W,
  fast_tc_wait_check_tr tm B w mirrored t p W = tc_wait_check_tr tm B w mirrored t p W.
Proof.
  intros tm B w mirrored t p W; unfold fast_tc_wait_check_tr,tc_wait_check_tr.
  destruct (t <=? S (B+w)); [|reflexivity].
  cbn [andb]. destruct (tc_tail (if mirrored then mirror_tm tm else tm) t p W);
    [apply fast_tail_instr_gate_eq|reflexivity].
Qed.

Lemma fast_tc_wait_check_tr_sound : forall tm B w mirrored t p W,
  fast_tc_wait_check_tr tm B w mirrored t p W = true ->
  forall tg, FutureBeepTr tm tg B -> BeepWindowTr tm tg B w.
Proof.
  intros tm B w mirrored t p W H; rewrite fast_tc_wait_check_tr_eq in H.
  exact (tc_wait_check_tr_sound tm B w mirrored t p W H).
Qed.
