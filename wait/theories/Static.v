(** Finite control-flow invariants for the suffix after a waiting window.
    Undefined transitions are allowed: coverage concerns surviving runs. *)
From Coq Require Import List Arith Lia Bool.
From SmallBB Require Import Statement StatementTr CTape ClosureTr Bounds.
From SmallBB.Checkers Require Import Cycle.
From BBBWait Require Import Spec SpecTr CheckerTr.
Import ListNotations.

Definition state_mask (a b c : bool) (q : St) :=
  match q with StA => a | StB => b | StC => c end.

Definition state_closed_mask tm (seen : St -> bool) :=
  forallb (fun q => if seen q then forallb (fun h =>
    match tm q h with None => true | Some tr => seen (t_next tr) end)
    [S0;S1;S2] else true) all_St.

Lemma state_closed_mask_next : forall tm seen,
  state_closed_mask tm seen = true -> forall q h tr,
  seen q = true -> tm q h = Some tr -> seen (t_next tr) = true.
Proof.
  intros tm seen H q h tr Hq E; unfold state_closed_mask in H.
  apply forallb_forall with (x:=q) in H; [|apply all_St_complete].
  rewrite Hq in H.
  apply forallb_forall with (x:=h) in H; [now rewrite E in H|].
  destruct h; cbn; auto.
Qed.

Definition tape_alphabet (allowed : Sym -> bool) (ct : ctape) :=
  let '(l,h,r) := ct in
  allowed S0 && forallb allowed l && allowed h && forallb allowed r.

Lemma alphabet_head : forall allowed l,
  allowed S0 = true -> forallb allowed l = true -> allowed (chd l) = true.
Proof.
  intros allowed [|h l] H0 H; [exact H0|].
  cbn in H; apply andb_prop in H; tauto.
Qed.

Lemma alphabet_tail : forall allowed l,
  forallb allowed l = true -> forallb allowed (ctl l) = true.
Proof.
  intros allowed [|h l] H; [reflexivity|].
  cbn in H; apply andb_prop in H; tauto.
Qed.

Lemma tape_alphabet_move : forall allowed dr w ct,
  allowed w = true -> tape_alphabet allowed ct = true ->
  tape_alphabet allowed (ctape_move dr w ct) = true.
Proof.
  intros allowed dr w [[l h] r] Hw H.
  unfold tape_alphabet in H; apply andb_prop in H as [H Hr].
  apply andb_prop in H as [H Hh]; apply andb_prop in H as [H0 Hl].
  destruct dr; cbn [ctape_move tape_alphabet];
    repeat rewrite andb_true_iff; repeat split; try assumption.
  - now apply alphabet_tail.
  - now apply alphabet_head.
  - cbn; rewrite Hw,Hr; reflexivity.
  - cbn; rewrite Hw,Hl; reflexivity.
  - now apply alphabet_head.
  - now apply alphabet_tail.
Qed.

Definition instr_closed_mask tm (allowed : Sym -> bool) (seen : Instr -> bool) :=
  forallb (fun tg => if seen tg then
    match tm (fst tg) (snd tg) with
    | None => true
    | Some tr => allowed (t_write tr) && forallb
      (fun h => if allowed h then seen (t_next tr,h) else true) [S0;S1;S2]
    end else true) all_Instr.

Lemma instr_closed_mask_next : forall tm allowed seen,
  instr_closed_mask tm allowed seen = true -> forall q h tr,
  seen (q,h) = true -> tm q h = Some tr ->
  allowed (t_write tr) = true /\
    forall h', allowed h' = true -> seen (t_next tr,h') = true.
Proof.
  intros tm allowed seen H q h tr Hq E; unfold instr_closed_mask in H.
  apply forallb_forall with (x:=(q,h)) in H; [|apply all_Instr_complete].
  rewrite Hq in H; cbn [fst snd] in H; rewrite E in H.
  apply andb_prop in H as [Hw Hnext]; split; [exact Hw|].
  intros h' Hh'. apply forallb_forall with (x:=h') in Hnext.
  - now rewrite Hh' in Hnext.
  - destruct h'; cbn; auto.
Qed.

Lemma instr_closed_mask_run : forall tm allowed seen,
  instr_closed_mask tm allowed seen = true -> forall n c d,
  tape_alphabet allowed (snd c) = true -> seen (cinstr c) = true ->
  csteps tm n c = Some d -> seen (cinstr d) = true.
Proof.
  intros tm allowed seen H n; induction n; intros [q [[l h] r]] d Ha Hq E.
  - injection E as <-; exact Hq.
  - cbn [csteps cstep] in E.
    destruct (tm q h) as [tr|] eqn:Et; [|discriminate].
    destruct (instr_closed_mask_next tm allowed seen H q h tr Hq Et)
      as [Hw Hnext].
    assert (Ha' : tape_alphabet allowed
      (ctape_move (t_dir tr) (t_write tr) (l,h,r)) = true).
    { apply tape_alphabet_move; [exact Hw|exact Ha]. }
    eapply IHn in E; [exact E|exact Ha'|].
    destruct (ctape_move (t_dir tr) (t_write tr) (l,h,r)) as [[l' h'] r'].
    cbn [cinstr fst snd]; apply Hnext.
    unfold tape_alphabet in Ha'; apply andb_prop in Ha' as [Ha' _].
    apply andb_prop in Ha'; tauto.
Qed.

Definition instr_mask a0 a1 a2 b0 b1 b2 c0 c1 c2 (tg : Instr) : bool :=
  match tg with
  | (StA,S0) => a0 | (StA,S1) => a1 | (StA,S2) => a2
  | (StB,S0) => b0 | (StB,S1) => b1 | (StB,S2) => b2
  | (StC,S0) => c0 | (StC,S1) => c1 | (StC,S2) => c2
  end.

Definition observed_instr tm cb w :=
  instr_mask (cfires tm cb (S w) (StA,S0)) (cfires tm cb (S w) (StA,S1))
    (cfires tm cb (S w) (StA,S2))
    (cfires tm cb (S w) (StB,S0)) (cfires tm cb (S w) (StB,S1))
    (cfires tm cb (S w) (StB,S2))
    (cfires tm cb (S w) (StC,S0)) (cfires tm cb (S w) (StC,S1))
    (cfires tm cb (S w) (StC,S2)).

Lemma observed_instr_spec : forall tm cb w tg,
  observed_instr tm cb w tg = cfires tm cb (S w) tg.
Proof. intros tm cb w [q h]; destruct q,h; reflexivity. Qed.

Definition static_instr_alphabet_check tm B w allowed :=
  match csteps tm B c0 with
  | None => true
  | Some cb =>
    let seen := observed_instr tm cb w in
    match csteps tm w cb with
    | None => true
    | Some d => tape_alphabet allowed (snd d) && seen (cinstr d) &&
                instr_closed_mask tm allowed seen
    end
  end.

Lemma static_instr_alphabet_check_sound : forall tm B w allowed,
  static_instr_alphabet_check tm B w allowed = true ->
  forall tg, FutureBeepTr tm tg B -> BeepWindowTr tm tg B w.
Proof.
  intros tm B w allowed H tg (t & Ht & Hv).
  destruct (le_lt_dec t (B+w)) as [Hle|Hlt].
  - exists t; auto.
  - destruct (fires_computable tm t tg Hv) as (ct & Et & Htg).
    destruct (csteps_prefix tm B t c0 ct Ht Et) as (cb & Eb & Ebt).
    destruct (csteps_prefix tm w (t-B) cb ct ltac:(lia) Ebt)
      as (d & Ed & Edt).
    unfold static_instr_alphabet_check in H; rewrite Eb, Ed in H.
    apply andb_prop in H as [H Hclosed]; apply andb_prop in H as [Ha Hseen].
    pose proof (instr_closed_mask_run tm allowed _ Hclosed
      (t-B-w) d ct Ha Hseen Edt) as Htarget.
    rewrite Htg, observed_instr_spec in Htarget.
    destruct (cfires_sound tm (S w) cb tg Htarget)
      as (i & ci & Hi & Ei & Hqi).
    exists (B+i); repeat split; try lia.
    exists (lift ci); split; [|rewrite cinstr_lift; exact Hqi].
    rewrite <- lift_c0; apply csteps_lift; rewrite csteps_add, Eb; exact Ei.
Qed.

Definition binary_alphabet (h : Sym) :=
  match h with S0 | S1 => true | S2 => false end.
Definition zero_alphabet (h : Sym) :=
  match h with S0 => true | _ => false end.
Definition static_instr_check tm B w :=
  if static_instr_alphabet_check tm B w binary_alphabet then true
  else static_instr_alphabet_check tm B w zero_alphabet.

Lemma static_instr_check_sound : forall tm B w,
  static_instr_check tm B w = true ->
  forall tg, FutureBeepTr tm tg B -> BeepWindowTr tm tg B w.
Proof.
  intros tm B w H; unfold static_instr_check in H.
  destruct (static_instr_alphabet_check tm B w binary_alphabet) eqn:E.
  - exact (static_instr_alphabet_check_sound tm B w binary_alphabet E).
  - exact (static_instr_alphabet_check_sound tm B w zero_alphabet H).
Qed.

Lemma state_closed_mask_run : forall tm seen,
  state_closed_mask tm seen = true -> forall n c d,
  seen (fst c) = true -> csteps tm n c = Some d -> seen (fst d) = true.
Proof.
  intros tm seen H n; induction n; intros [q [[l h] r]] d Hq E.
  - injection E as <-; exact Hq.
  - cbn [csteps cstep] in E.
    destruct (tm q h) as [tr|] eqn:Et; [|discriminate].
    eapply IHn in E; [exact E|].
    cbn; eapply state_closed_mask_next; eauto.
Qed.

Definition static_state_check tm B w :=
  match csteps tm B c0 with
  | None => true
  | Some cb =>
    let a := cvisits tm cb (S w) StA in
    let b := cvisits tm cb (S w) StB in
    let c := cvisits tm cb (S w) StC in
    let seen := state_mask a b c in
    match csteps tm w cb with
    | None => true
    | Some d => seen (fst d) && state_closed_mask tm seen
    end
  end.

Lemma static_state_check_sound : forall tm B w,
  static_state_check tm B w = true ->
  forall q, FutureBeep tm q B -> BeepWindow tm q B w.
Proof.
  intros tm B w H q (t & Ht & Hv).
  destruct (le_lt_dec t (B+w)) as [Hle|Hlt].
  - exists t; auto.
  - destruct (visits_computable tm t q Hv) as (ct & Et & Hq).
    destruct (csteps_prefix tm B t c0 ct Ht Et) as (cb & Eb & Ebt).
    destruct (csteps_prefix tm w (t-B) cb ct ltac:(lia) Ebt)
      as (d & Ed & Edt).
    unfold static_state_check in H; rewrite Eb, Ed in H.
    apply andb_prop in H as [Hseen Hclosed].
    pose proof (state_closed_mask_run tm _ Hclosed (t-B-w) d ct Hseen Edt) as Htarget.
    rewrite Hq in Htarget.
    assert (Hvisit : cvisits tm cb (S w) q = true).
    { destruct q; exact Htarget. }
    destruct (cvisits_sound tm (S w) cb q Hvisit) as (i & ci & Hi & Ei & Hqi).
    exists (B+i); repeat split; try lia.
    exists (lift ci); split; [|exact Hqi].
    rewrite <- lift_c0; apply csteps_lift; rewrite csteps_add, Eb; exact Ei.
Qed.
