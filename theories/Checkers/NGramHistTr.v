(** * NGramHistTr: the history-augmented n-gram never-QH tier at
    TRANSITION level.

    [NGramHist.ngramhist_check_neverqh_lex] with the target alphabet
    changed from the 4 states to the 8 instructions: the same augmented
    cells ([hsym] = bit + last-[k] (state, read) records), the same
    head-relative gram-set closure ([hng_succs]) and the same
    lexicographic liveness certificates ([hcomp]); only the liveness
    gate's target projection changes, from [ha_state] to [ha_instr]
    (state + the head cell's bit), through the instruction-target engine
    [ClosureTr.closure_check_neverqhtr_lex].

    Why this tier exists (SCOPING_INSTR.md §7.1w): on the sqrt/poly/
    non-binary-counter LIVE classes the plain n-gram rank tier
    ([DecideTr.rank_tier_tr]) discharges every instruction but one to
    three, and the failing ones are exactly those the plain gram-set
    abstraction lets the run avoid forever along a FAKE macro-cycle
    (a bounce over an all-ones far tape).  The history records on the
    far cells constrain that far tape and de-merge the fake cycle -- the
    same refinement that closed 669 state-level deferred counters. *)

From Coq Require Import Arith Lia Bool List ZArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape PosEnc PattCount
  Closure ClosureTr.
From BBB4.Checkers Require Import Cycle ExactClosure NGram NGramHist.
Import ListNotations.

(** the instruction an augmented node is about to fire *)
Definition ha_instr (a : hcconf) : Instr :=
  (fst a, let '(_, s, _) := snd a in hbit s).

Lemma hng_covers_instr : forall n lset rset a hc,
  hng_covers n lset rset a hc -> ha_instr a = (fst hc, let '(_, h, _) := snd hc in hbit h).
Proof.
  intros n lset rset [q [[lw s] rw]] [qc [[l h] r]] (Hq & Hh & _).
  unfold ha_instr; simpl in *. congruence.
Qed.

Lemma hcovers_instr : forall n lset rset a c,
  hcovers n lset rset a c -> ha_instr a = instr_of c.
Proof.
  intros n lset rset a c (hc & Hlift & Hcov).
  rewrite (hng_covers_instr n lset rset a hc Hcov).
  subst c. destruct hc as [q [[l h] r]]. reflexivity.
Qed.

Definition ngramhist_check_neverqhtr_lex (tm : TM) (k n t fuel : nat)
    (lset rset : hgset) (cert : Instr -> list hcomp) : bool :=
  (1 <=? n) &&
  match hcsteps tm k t hcconf0 with
  | Some hct =>
      hseed_ok n lset rset hct &&
      closure_check_neverqhtr_lex tm hcconf hctx_enc ha_instr
        (hng_succs tm k n lset rset) t fuel (hng_start n hct)
        (fun tg => map (hcomp_denote tm n) (cert tg))
  | None => false
  end.

Theorem ngramhist_check_neverqhtr_lex_sound :
  forall tm k n t fuel lset rset cert,
  ngramhist_check_neverqhtr_lex tm k n t fuel lset rset cert = true ->
  NeverQuasiHaltsTr tm.
Proof.
  intros tm k n t fuel lset rset cert H.
  unfold ngramhist_check_neverqhtr_lex in H.
  apply andb_prop in H as [Hn H].
  apply Nat.leb_le in Hn.
  destruct (hcsteps tm k t hcconf0) as [hct|] eqn:Eht; [|discriminate].
  apply andb_prop in H as [Hseed Hcheck].
  apply (closure_check_neverqhtr_lex_sound tm hcconf hctx_enc ha_instr
           (hng_succs tm k n lset rset) (hcovers n lset rset)) in Hcheck;
    [assumption | | | | |].
  - exact hctx_enc_inj.
  - intros a c Hc. eapply hcovers_instr; eauto.
  - intros a c Hc. apply hng_succs_sound; assumption.
  - intros ct' Hct'.
    pose proof (hcsteps_proj tm k t hcconf0 hct Eht) as Hpr.
    rewrite hproj_hcconf0 in Hpr. rewrite Hct' in Hpr. injection Hpr as Hpr.
    exists hct. split; [rewrite Hpr; reflexivity | apply hng_start_covers; exact Hseed].
  - intros tg0. apply Forall_forall. intros comp Hin.
    apply in_map_iff in Hin. destruct Hin as (c & <- & _).
    destruct c as [phi | m K phi gate | p rg K phi gate]; simpl.
    + exact I.
    + intros a cc a' cc' sl (hc & Hlift & Hcov) Hca' Hstep Es HInl.
      rewrite (hproj_eq_ngstart n lset rset a hc cc Hcov Hlift).
      apply ngm_start_exact; [exact Hn | exact Hstep].
    + destruct (pm_ok n p rg) eqn:Epm; [| exact I].
      apply andb_prop in Epm as [He Hb].
      intros a cc a' cc' sl (hc & Hlift & Hcov) Hca' Hstep Es HInl.
      rewrite (hproj_eq_ngstart n lset rset a hc cc Hcov Hlift).
      apply pm_start_exact.
      * apply existsb_exists in He as (x & Hx & Hx1).
        apply sym_eqb_spec in Hx1. subst x. exact Hx.
      * destruct rg; apply Nat.leb_le; exact Hb.
      * exact Hstep.
Qed.

Corollary ngramhist_check_neverqhtr_lex_nonhalt :
  forall tm k n t fuel lset rset cert,
  ngramhist_check_neverqhtr_lex tm k n t fuel lset rset cert = true ->
  NonHalt tm.
Proof.
  intros. apply never_qh_tr_nonhalt.
  eapply ngramhist_check_neverqhtr_lex_sound; eauto.
Qed.
