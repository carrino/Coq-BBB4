(** History-augmented closed abstractions certify suffix instruction
    coverage. Ranking or recurrence of individual abstract labels is not
    needed for the waiting-time upper bound. *)
From Coq Require Import Arith Lia Bool List PArith.
From SmallBB Require Import Statement StatementTr CTape PosEnc ClosureTr Bounds
  AbstractCensus HistRankSearch HistCensus.
From SmallBB.Checkers Require Import NGramHist.
From BBBWait Require Import SpecTr Tail.
Import ListNotations.

Definition hn_tail tm k n t fuel rounds : option (list cconf) :=
  if 1 <=? n then
  match hcsteps tm k t hcconf0 with
  | None => None
  | Some cc =>
    let '(q,(l,h,r)) := cc in
    let a0 := hng_start n cc in
    let '(ls,rs) := hn_grow tm k n a0 fuel rounds
      (hseed_side n l) (hseed_side n r) in
    let Sl := hn_explore tm k n ls rs fuel [] PositiveSet.empty [a0] in
    if hseed_ok n ls rs cc then
    if closed_tr_b hcconf hctx_enc (hng_succs tm k n ls rs) Sl then
    if mem_tr hcconf hctx_enc a0 Sl then Some (labels hainstr Sl) else None
    else None else None
  end else None.

Theorem hn_tail_sound : forall tm k n t fuel rounds Sl,
  hn_tail tm k n t fuel rounds = Some Sl ->
  forall s tg, t <= s -> FiresAt tm tg s -> tail_instrs Sl tg = true.
Proof.
  intros tm k n t fuel rounds Sl H.
  unfold hn_tail in H.
  destruct (1 <=? n) eqn:Hn; [apply Nat.leb_le in Hn|discriminate].
  destruct (hcsteps tm k t hcconf0) as [[q [[l h] r]]|] eqn:Et; [|discriminate].
  match type of H with
  | (let '(_,_) := ?G in _) = _ => destruct G as [ls rs]
  end.
  cbv beta iota zeta in H.
  set (cc := (q,(l,h,r)) : hcconf) in *.
  set (a0 := hng_start n cc) in *.
  set (nodes := hn_explore tm k n ls rs fuel [] PositiveSet.empty [a0]) in *.
  match type of H with (if ?b then _ else _) = _ => destruct b eqn:Hseed end;
    [|discriminate].
  match type of H with (if ?b then _ else _) = _ => destruct b eqn:Hcl end;
    [|discriminate].
  match type of H with (if ?b then _ else _) = _ => destruct b eqn:Hmem end;
    [|discriminate].
  injection H as <-.
  assert (HIn : In a0 nodes) by (eapply mem_In_tr; [exact hctx_enc_inj|exact Hmem]).
  assert (Hcov : hcovers n ls rs a0 (lift (hproj cc))).
  { exists cc; split; [reflexivity|apply hng_start_covers; exact Hseed]. }
  assert (Eproj : csteps tm t c0 = Some (hproj cc)).
  { rewrite <- hproj_hcconf0; eapply hcsteps_proj; exact Et. }
  assert (Hstart : stepn tm t InitES = Some (lift (hproj cc))).
  { rewrite <- lift_c0; apply csteps_lift; exact Eproj. }
  assert (Hinv : forall j, exists c a, stepn tm j (lift (hproj cc)) = Some c /\
      In a nodes /\ hcovers n ls rs a c).
  { eapply closure_invariant_tr; [exact hctx_enc_inj| |exact Hcl|exact HIn|exact Hcov].
    intros a c Hc; apply hng_succs_sound; assumption. }
  intros s tg Hts (c & Hrun & Htg).
  destruct (Hinv (s-t)) as (c' & a & Hrun' & Ha & Hca).
  replace s with (t+(s-t)) in Hrun by lia.
  rewrite stepn_add, Hstart, Hrun' in Hrun; injection Hrun as <-.
  rewrite labels_instr; apply existsb_exists; exists a; split; [exact Ha|].
  apply instr_eqb_spec; rewrite <- Htg; eapply hcovers_instr; eauto.
Qed.

Definition hn_wait_check_tr tm B w k n t fuel rounds :=
  (t <=? S (B+w)) &&
  match hn_tail tm k n t fuel rounds with
  | None => false
  | Some Sl => tail_instr_gate tm B w Sl
  end.

Theorem hn_wait_check_tr_sound : forall tm B w k n t fuel rounds,
  hn_wait_check_tr tm B w k n t fuel rounds = true ->
  forall tg, FutureBeepTr tm tg B -> BeepWindowTr tm tg B w.
Proof.
  intros tm B w k n t fuel rounds H.
  unfold hn_wait_check_tr in H; apply andb_prop in H as [Hanchor H].
  apply Nat.leb_le in Hanchor.
  destruct (hn_tail tm k n t fuel rounds) as [Sl|] eqn:E; [|discriminate].
  eapply tail_instr_wait_sound; [exact Hanchor|exact H|].
  now apply (hn_tail_sound tm k n t fuel rounds Sl).
Qed.

Print Assumptions hn_wait_check_tr_sound.
