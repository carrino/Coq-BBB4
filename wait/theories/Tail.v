(** Transfer an arbitrary sound tail coverage certificate to an inclusive
    waiting bound. Translated cycles are one source of these certificates. *)
From Coq Require Import Arith Lia Bool List.
From SmallBB Require Import Statement StatementTr CTape Mirror ClosureTr Bounds CycleCensus.
From SmallBB.Checkers Require Import Cycle.
From BBBWait Require Import Spec SpecTr CheckerTr.
Import ListNotations.

Definition tail_state_gate tm B w Sl :=
  match csteps tm B c0 with
  | None => true
  | Some c => forallb (fun q => implb (tail_states Sl q)
      (cvisits tm c (S w) q)) all_St
  end.

Definition tail_instr_gate tm B w Sl :=
  match csteps tm B c0 with
  | None => true
  | Some c => forallb (fun tg => implb (tail_instrs Sl tg)
      (cfires tm c (S w) tg)) all_Instr
  end.

Lemma tail_state_from_instr : forall Sl q a,
  tail_instrs Sl (q,a) = true -> tail_states Sl q = true.
Proof.
  intros Sl q a H; apply existsb_exists in H as (c & Hin & Heq).
  apply instr_eqb_spec in Heq.
  unfold tail_states; apply existsb_exists; exists c; split; [exact Hin|].
  apply st_eqb_spec. apply (f_equal fst) in Heq; exact Heq.
Qed.

Theorem tail_state_wait_sound : forall tm B w t Sl,
  t <= S (B+w) -> tail_state_gate tm B w Sl = true ->
  (forall s tg, t <= s -> FiresAt tm tg s -> tail_instrs Sl tg = true) ->
  forall q, FutureBeep tm q B -> BeepWindow tm q B w.
Proof.
  intros tm B w t Sl Ht Hgate Hcover q (s & HBs & Hv).
  destruct (le_lt_dec s (B+w)) as [Hsmall|Hlarge].
  - exists s; auto.
  - assert (Htail : tail_states Sl q = true).
    { apply visits_fires in Hv as (a & Hf).
      apply (tail_state_from_instr Sl q a); exact (Hcover s (q,a) ltac:(lia) Hf). }
    destruct (visits_computable tm s q Hv) as (cs & Es & Hqs).
    destruct (csteps_prefix tm B s c0 cs HBs Es) as (cb & Eb & _).
    unfold tail_state_gate in Hgate; rewrite Eb in Hgate.
    apply forallb_forall with (x:=q) in Hgate; [|apply all_St_complete].
    rewrite Htail in Hgate; cbn in Hgate.
    destruct (cvisits_sound tm (S w) cb q Hgate) as (i & ci & Hi & Ei & Hqi).
    exists (B+i); repeat split; try lia.
    exists (lift ci); split; [|exact Hqi].
    rewrite <- lift_c0; apply csteps_lift; rewrite csteps_add, Eb; exact Ei.
Qed.

Theorem tail_instr_wait_sound : forall tm B w t Sl,
  t <= S (B+w) -> tail_instr_gate tm B w Sl = true ->
  (forall s tg, t <= s -> FiresAt tm tg s -> tail_instrs Sl tg = true) ->
  forall tg, FutureBeepTr tm tg B -> BeepWindowTr tm tg B w.
Proof.
  intros tm B w t Sl Ht Hgate Hcover tg (s & HBs & Hv).
  destruct (le_lt_dec s (B+w)) as [Hsmall|Hlarge].
  - exists s; auto.
  - assert (Htail : tail_instrs Sl tg = true) by (exact (Hcover s tg ltac:(lia) Hv)).
    destruct (fires_computable tm s tg Hv) as (cs & Es & Hqs).
    destruct (csteps_prefix tm B s c0 cs HBs Es) as (cb & Eb & _).
    unfold tail_instr_gate in Hgate; rewrite Eb in Hgate.
    apply forallb_forall with (x:=tg) in Hgate; [|apply all_Instr_complete].
    rewrite Htail in Hgate; cbn in Hgate.
    destruct (cfires_sound tm (S w) cb tg Hgate) as (i & ci & Hi & Ei & Hqi).
    exists (B+i); repeat split; try lia.
    exists (lift ci); split; [|rewrite cinstr_lift; exact Hqi].
    rewrite <- lift_c0; apply csteps_lift; rewrite csteps_add, Eb; exact Ei.
Qed.

Theorem tail_wait_sound : forall tm bs ws bi wi t Sl,
  t <= S (bs+ws) -> t <= S (bi+wi) ->
  tail_state_gate tm bs ws Sl = true -> tail_instr_gate tm bi wi Sl = true ->
  (forall s tg, t <= s -> FiresAt tm tg s -> tail_instrs Sl tg = true) ->
  (forall q, FutureBeep tm q bs -> BeepWindow tm q bs ws) /\
  (forall tg, FutureBeepTr tm tg bi -> BeepWindowTr tm tg bi wi).
Proof.
  intros; split; [eapply tail_state_wait_sound|eapply tail_instr_wait_sound]; eauto.
Qed.

Lemma mirror_wait_state : forall tm B w,
  (forall q, FutureBeep (mirror_tm tm) q B -> BeepWindow (mirror_tm tm) q B w) ->
  forall q, FutureBeep tm q B -> BeepWindow tm q B w.
Proof.
  intros tm B w H q (s & Hs & Hv).
  assert (Hfuture : FutureBeep (mirror_tm tm) q B).
  { exists s; split; [exact Hs|apply (proj2 (mirror_visits tm q s)); exact Hv]. }
  destruct (H q Hfuture) as (k & Hk & Hkw & Hvk).
  exists k; repeat split; try assumption; apply (proj1 (mirror_visits tm q k)) in Hvk; exact Hvk.
Qed.

Lemma mirror_wait_instr : forall tm B w,
  (forall tg, FutureBeepTr (mirror_tm tm) tg B -> BeepWindowTr (mirror_tm tm) tg B w) ->
  forall tg, FutureBeepTr tm tg B -> BeepWindowTr tm tg B w.
Proof.
  intros tm B w H tg (s & Hs & Hv).
  assert (Hfuture : FutureBeepTr (mirror_tm tm) tg B).
  { exists s; split; [exact Hs|apply (proj2 (mirror_fires tm tg s)); exact Hv]. }
  destruct (H tg Hfuture) as (k & Hk & Hkw & Hvk).
  exists k; repeat split; try assumption; apply (proj1 (mirror_fires tm tg k)) in Hvk; exact Hvk.
Qed.

Definition tc_wait_check_state tm B w (mirrored : bool) t p W :=
  (t <=? S (B+w)) &&
  let tm' := if mirrored then mirror_tm tm else tm in
  match tc_tail tm' t p W with
  | Some Sl => tail_state_gate tm' B w Sl
  | None => false
  end.

Definition tc_wait_check_tr tm B w (mirrored : bool) t p W :=
  (t <=? S (B+w)) &&
  let tm' := if mirrored then mirror_tm tm else tm in
  match tc_tail tm' t p W with
  | Some Sl => tail_instr_gate tm' B w Sl
  | None => false
  end.

Theorem tc_wait_check_state_sound : forall tm B w mirrored t p W,
  tc_wait_check_state tm B w mirrored t p W = true ->
  forall q, FutureBeep tm q B -> BeepWindow tm q B w.
Proof.
  intros tm B w mirrored t p W H.
  unfold tc_wait_check_state in H; apply andb_prop in H as [Ht H].
  apply Nat.leb_le in Ht.
  set (tm' := if mirrored then mirror_tm tm else tm) in *.
  destruct (tc_tail tm' t p W) as [Sl|] eqn:E; [|discriminate].
  destruct (tc_tail_sound tm' t p W Sl E) as [_ [Hcover _]].
  pose proof (tail_state_wait_sound tm' B w t Sl Ht H Hcover) as Hwait.
  unfold tm' in Hwait; destruct mirrored; [apply mirror_wait_state|]; exact Hwait.
Qed.

Theorem tc_wait_check_tr_sound : forall tm B w mirrored t p W,
  tc_wait_check_tr tm B w mirrored t p W = true ->
  forall tg, FutureBeepTr tm tg B -> BeepWindowTr tm tg B w.
Proof.
  intros tm B w mirrored t p W H.
  unfold tc_wait_check_tr in H; apply andb_prop in H as [Ht H].
  apply Nat.leb_le in Ht.
  set (tm' := if mirrored then mirror_tm tm else tm) in *.
  destruct (tc_tail tm' t p W) as [Sl|] eqn:E; [|discriminate].
  destruct (tc_tail_sound tm' t p W Sl E) as [_ [Hcover _]].
  pose proof (tail_instr_wait_sound tm' B w t Sl Ht H Hcover) as Hwait.
  unfold tm' in Hwait; destruct mirrored; [apply mirror_wait_instr|]; exact Hwait.
Qed.
