(** * Checkers/NGramTr: the n-gram CPS decider at TRANSITION level.

    NGram.v's abstraction instantiated into ClosureTr's
    instruction-target engine (SCOPING_INSTR.md sections 3.3, 5): the
    n-gram context [cconf] pins the head symbol ([ng_covers]'s second
    conjunct), so the instruction projection is [cinstr] and the
    covers bridge is one [congruence].  Everything computational —
    gram sets, successors, seeding, the untrusted [ng_grow] two-level
    fixpoint — is REUSED from NGram.v; only the engine instantiation
    and the target alphabet change.

    [ngram_check_neverqhtr] is the phase-3 in-walk never tier: same
    per-machine cost as the state tier, conclusion
    [NeverQuasiHaltsTr]. *)

From Coq Require Import Arith Lia Bool List ZArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape PosEnc
  Records ClosureTr.
From BBB4.Checkers Require Import Cycle NGram.
From BBB4.Checkers.IRules Require Import Engine AnchorVisits AnchorVisitsTr.
Import ListNotations.
Open Scope nat_scope.

(** the instruction a context is about to fire: the node's own state
    and pinned head symbol *)
Lemma ng_covers_instr : forall n lset rset a c,
  ng_covers n lset rset a c -> cinstr a = instr_of c.
Proof.
  intros n lset rset [q [[lw s] rw]] c (Hq & Hh & _).
  unfold cinstr, instr_of; simpl. congruence.
Qed.

(** ** The checker *)

Definition ngram_check_neverqhtr (tm : TM) (n t fuel rounds : nat) : bool :=
  (1 <=? n) &&
  match csteps tm t c0 with
  | Some cc =>
      let '(q, (l, h, r)) := cc in
      let lset0 := gadds (ng_seed_side n l) gempty in
      let rset0 := gadds (ng_seed_side n r) gempty in
      let a0 := ng_start n cc in
      let '(lset, rset) := ng_grow tm a0 fuel rounds lset0 rset0 in
      ng_seed_ok n lset rset cc &&
      closure_check_neverqhtr tm cconf cconf_enc cinstr
        (ng_succs tm lset rset) t fuel a0
  | None => false
  end.

Theorem ngram_check_neverqhtr_sound : forall tm n t fuel rounds,
  ngram_check_neverqhtr tm n t fuel rounds = true -> NeverQuasiHaltsTr tm.
Proof.
  intros tm n t fuel rounds H.
  unfold ngram_check_neverqhtr in H.
  apply andb_prop in H as [Hn H].
  apply Nat.leb_le in Hn.
  destruct (csteps tm t c0) as [[q [[l h] r]]|] eqn:Et; [|discriminate].
  match type of H with
  | (let '(_, _) := ?G in _) = true => destruct G as [lset rset] eqn:Eg
  end.
  cbv beta iota zeta in H.
  apply andb_prop in H as [Hseed Hcheck].
  apply (closure_check_neverqhtr_sound tm cconf cconf_enc cinstr
           (ng_succs tm lset rset) (ng_covers n lset rset)) in Hcheck;
    [assumption | | | |].
  - exact cconf_enc_inj.
  - intros a c Hc. eapply ng_covers_instr; eauto.
  - intros a c Hc. apply ng_succs_sound; assumption.
  - intros ct' Hct'. rewrite Et in Hct'. injection Hct' as <-.
    apply ng_start_covers. exact Hseed.
Qed.

(** ** The lex-gated never tier

    [ngram_check_neverqh_lex_with]'s shape: the gram sets come from
    the CALLER (the rank tier, which already grew them for its
    certificate search) -- [ng_seed_ok] + the closure check re-derive
    everything from the given sets, so soundness does not depend on
    where they came from. *)
Definition ngram_check_neverqhtr_lex_with (tm : TM) (n t fuel : nat)
    (lset rset : gset) (cert : Instr -> list ngcomp) : bool :=
  (1 <=? n) &&
  match csteps tm t c0 with
  | Some cc =>
      let a0 := ng_start n cc in
      ng_seed_ok n lset rset cc &&
      closure_check_neverqhtr_lex tm cconf cconf_enc cinstr
        (ng_succs tm lset rset) t fuel a0
        (fun tg => map (ng_comp_denote tm n) (cert tg))
  | None => false
  end.

Theorem ngram_check_neverqhtr_lex_with_sound :
  forall tm n t fuel lset rset cert,
  ngram_check_neverqhtr_lex_with tm n t fuel lset rset cert = true ->
  NeverQuasiHaltsTr tm.
Proof.
  intros tm n t fuel lset rset cert H.
  unfold ngram_check_neverqhtr_lex_with in H.
  apply andb_prop in H as [Hn H].
  apply Nat.leb_le in Hn.
  destruct (csteps tm t c0) as [cc|] eqn:Et; [|discriminate].
  apply andb_prop in H as [Hseed Hcheck].
  apply (closure_check_neverqhtr_lex_sound tm cconf cconf_enc cinstr
           (ng_succs tm lset rset) (ng_covers n lset rset)) in Hcheck;
    [assumption | | | | |].
  - exact cconf_enc_inj.
  - intros a c Hc. eapply ng_covers_instr; eauto.
  - intros a c Hc. apply ng_succs_sound; assumption.
  - intros ct' Hct'. rewrite Et in Hct'. injection Hct' as <-.
    apply ng_start_covers. exact Hseed.
  - intros tg0. apply Forall_forall. intros comp Hin.
    apply in_map_iff in Hin. destruct Hin as (c & <- & _).
    destruct c as [phi | m K phi gate | phi | pp rg K phi gate]; simpl.
    + exact I.
    + intros a cc' a' cc'' sl Hca Hca' Hstep Es HInl.
      eapply (ngm_exact tm n lset rset); eauto.
    + exact I.
    + destruct (pm_ok n pp rg) eqn:Epm; [|exact I].
      apply andb_prop in Epm as [He Hb].
      intros a cc' a' cc'' sl Hca Hca' Hstep Es HInl.
      eapply (pm_exact tm n lset rset); eauto.
      * apply existsb_exists in He as (x & Hx & Hx1).
        apply sym_eqb_spec in Hx1. subst x. assumption.
      * destruct rg; apply Nat.leb_le; assumption.
Qed.
