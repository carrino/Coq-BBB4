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
