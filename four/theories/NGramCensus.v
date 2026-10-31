From Coq Require Import Arith Lia Bool List ZArith NArith.
From BBB24 Require Import Statement StatementTr CTape PosEnc Closure ClosureTr Bounds RankSearch.
From BBB24.Checkers Require Import Cycle NGram.
Import ListNotations.
Section Parameters.
Variable bs bi : N.

Definition ng_check (tm : TM) (n t fuel rounds : nat) : bool :=
  if 1 <=? n then
  match csteps tm t c0 with
  | None => false
  | Some cc =>
    let '(q,(l,h,r)) := cc in
    let a0 := ng_start n cc in
    let '(ls,rs) := ng_grow tm a0 fuel rounds
      (gadds (ng_seed_side n l) gempty) (gadds (ng_seed_side n r) gempty) in
    let Sl := ng_explore tm ls rs fuel [] PositiveSet.empty [a0] in
    if ng_seed_ok n ls rs cc then
    if closed_tr_b cconf cconf_enc (ng_succs tm ls rs) Sl then
    if mem_tr cconf cconf_enc a0 Sl then
    if prefix_gate bs bi tm t (tail_states Sl) (tail_instrs Sl) then
      live_lex_ok_tr cconf cconf_enc cinstr (ng_succs tm ls rs) Sl
        (fun tg => map (ng_comp_denote tm n) (rank_procedure tm ls rs Sl tg))
    else false else false else false else false
  end else false.

Lemma ng_covers_instr : forall n ls rs a c,
  ng_covers n ls rs a c -> cinstr a = instr_of c.
Proof.
  intros n ls rs [q [[l h] r]] c (Hq & Hh & _).
  unfold cinstr, instr_of; simpl. congruence.
Qed.

Lemma ng_components_exact : forall tm n ls rs comps,
  1 <= n -> Forall (comp_exact tm cconf (ng_succs tm ls rs) (ng_covers n ls rs))
    (map (ng_comp_denote tm n) comps).
Proof.
  intros tm n ls rs comps Hn. apply Forall_forall. intros comp Hin.
  apply in_map_iff in Hin as (c & <- & _).
  destruct c as [phi | m K phi gate | phi | pp rg K phi gate]; simpl.
  - exact I.
  - intros a cc a' cc' sl Hca Hca' Hstep Es HInl. eapply ngm_exact; eauto.
  - exact I.
  - destruct (pm_ok n pp rg) eqn:Epm; [|exact I].
    apply andb_prop in Epm as [He Hb].
    intros a cc a' cc' sl Hca Hca' Hstep Es HInl. eapply pm_exact; eauto.
    + apply existsb_exists in He as (x & Hx & Hx1).
      apply sym_eqb_spec in Hx1. subst x. assumption.
    + destruct rg; apply Nat.leb_le; assumption.
Qed.

Theorem ng_check_sound : forall tm n t fuel rounds,
  ng_check tm n t fuel rounds = true -> NonHalt tm /\ Bounds bs bi tm.
Proof.
  intros tm n t fuel rounds H. unfold ng_check in H.
  destruct (1 <=? n) eqn:Hn; [apply Nat.leb_le in Hn|discriminate].
  destruct (csteps tm t c0) as [[q [[l h] r]]|] eqn:Et; [|discriminate].
  match type of H with
  | (let '(_,_) := ?G in _) = true => destruct G as [ls rs]
  end.
  cbv beta iota zeta in H.
  set (cc := (q,(l,h,r)) : cconf) in *.
  set (a0 := ng_start n cc) in *.
  set (Sl := ng_explore tm ls rs fuel [] PositiveSet.empty [a0]) in *.
  match type of H with (if ?b then _ else _) = true => destruct b eqn:Hseed end; [|discriminate].
  match type of H with (if ?b then _ else _) = true => destruct b eqn:Hcl end; [|discriminate].
  match type of H with (if ?b then _ else _) = true => destruct b eqn:Hmem end; [|discriminate].
  match type of H with (if ?b then _ else _) = true => destruct b eqn:Hpre end; [|discriminate].
  assert (HIn : In a0 Sl) by (eapply mem_In_tr; [exact cconf_enc_inj|exact Hmem]).
  assert (Hcov : ng_covers n ls rs a0 (lift cc)) by (apply ng_start_covers; exact Hseed).
  assert (Hstart : stepn tm t InitES = Some (lift cc)).
  { rewrite <- lift_c0. apply csteps_lift; exact Et. }
  assert (Hinv : forall k, exists c a, stepn tm k (lift cc) = Some c /\
      In a Sl /\ ng_covers n ls rs a c).
  { eapply closure_invariant_tr; [exact cconf_enc_inj| |exact Hcl|exact HIn|exact Hcov].
    intros a c Hc. apply ng_succs_sound; assumption. }
  assert (Hrec : forall tg, tail_instrs Sl tg = true -> forall N,
      exists k, N <= k /\ FiresAt tm tg k).
  { intros tg Happ N.
    destruct (live_appears_recur_lex_tr tm cconf cconf_enc cinstr (ng_succs tm ls rs)
      (ng_covers n ls rs) cconf_enc_inj (ng_covers_instr n ls rs)
      (fun a c Hc => ng_succs_sound tm n ls rs a c Hn Hc)
      Sl (fun tg => map (ng_comp_denote tm n) (rank_procedure tm ls rs Sl tg))
      a0 cc tg Hcl (ng_components_exact tm n ls rs _ Hn) H HIn Hcov Happ N)
      as (k & c & Hk & Hrun & Htg).
    exists (t+k). split; [lia|]. exists c. split; [|exact Htg].
    rewrite stepn_add, Hstart. exact Hrun. }
  split.
  - intros k Hnone. destruct (le_lt_dec t k).
    + destruct (Hinv (k-t)) as (c & a & Hrun & _).
      replace k with (t+(k-t)) in Hnone by lia.
      rewrite stepn_add, Hstart, Hrun in Hnone. discriminate.
    + destruct (stepn_prefix tm k t InitES (lift cc) ltac:(lia) Hstart)
        as (c & Hrun & _). congruence.
  - eapply (tail_bounds bs bi); [exact Hpre| |exact Hrec].
    intros s tg Hts (c & Hrun & Htg).
    destruct (Hinv (s-t)) as (c' & a & Hrun' & Ha & Hca).
    replace s with (t+(s-t)) in Hrun by lia.
    rewrite stepn_add, Hstart, Hrun' in Hrun. injection Hrun as <-.
    apply existsb_exists. exists a. split; [exact Ha|].
    apply instr_eqb_spec. rewrite <- Htg. eapply ng_covers_instr; eauto.
Qed.

End Parameters.
