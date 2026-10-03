(** * FuelPhaseTargetTr: certify recurrence of one instruction independently.

    The generic closure proof reuses FuelSCCTr descent. A phase certificate
    can cover one difficult instruction while smaller abstractions cover the
    others through FuelMixPartialTr. All supplied graphs and ranks are checked. *)
From Coq Require Import Arith Lia Bool List ZArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape PosEnc
  Records Closure ClosureTr.
From BBB4.Checkers Require Import Cycle ExactClosure NGram NGramTr Fuel
  FuelClass FuelSCC FuelWide FuelSCCTr FuelWideTr FuelMixTr FuelPhaseTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
Import ListNotations.

Section FuelSCCTarget.
  Variable tm : TM.
  Variable A : Type.
  Variable a_enc : A -> positive.
  Variable a_instr : A -> Instr.
  Variable succs : A -> option (list A).
  Variable node_moves_right : A -> bool.
  Variable node_rfuel_ge1 : A -> bool.

  Definition closure_check_recurrent_fuelscctr (fuel : nat) (a0 : A)
      (q : Instr) (cert : list (lexcomp A) * (A -> bool)) : bool :=
    match close A a_enc succs fuel [] PositiveSet.empty [a0] with
    | Some Sl => closed_b A a_enc succs Sl && mem A a_enc a0 Sl &&
        fscc_instr_ok A a_instr succs node_moves_right node_rfuel_ge1
          Sl q (fst cert) (snd cert)
    | None => false
    end.

  Variable covers : A -> ExecState -> Prop.
  Hypothesis a_enc_inj : forall x y, a_enc x = a_enc y -> x = y.
  Hypothesis covers_instr : forall a c, covers a c -> a_instr a = instr_of c.
  Hypothesis succs_sound : forall a c, covers a c ->
    match succs a, step tm c with
    | Some l, Some c' => exists a', In a' l /\ covers a' c'
    | Some _, None => False
    | None, _ => True
    end.
  Hypothesis node_moves_right_sound : forall a c,
    node_moves_right a = true -> covers a c -> steps_right tm c.
  Hypothesis node_rfuel_ge1_sound : forall a c,
    node_rfuel_ge1 a = true -> covers a c -> has_right_nonblank (snd c).

  Theorem closure_check_recurrent_fuelscctr_sound : forall fuel a0 q cert,
    covers a0 (lift c0) ->
    Forall (comp_exact tm A succs covers) (fst cert) ->
    closure_check_recurrent_fuelscctr fuel a0 q cert = true ->
    forall N, exists j, N <= j /\ FiresAt tm q j.
  Proof.
    intros fuel a0 q cert Hcov0 Hcert H N.
    unfold closure_check_recurrent_fuelscctr in H.
    destruct (close A a_enc succs fuel [] PositiveSet.empty [a0])
      as [Sl|]; [|discriminate].
    apply andb_prop in H as [H Hlive].
    apply andb_prop in H as [Hcl Hin].
    apply (mem_In A a_enc a_enc_inj) in Hin.
    destruct (closure_invariant tm A a_enc succs covers a_enc_inj
      succs_sound Sl Hcl a0 (lift c0) Hin Hcov0 N)
      as (cN & aN & HN & HInN & HcovN).
    rewrite lift_c0 in HN.
    destruct (stepn_csteps tm N cN HN) as (ccN & HccN & HliftN).
    rewrite <- HliftN in HcovN, HN.
    destruct (extent_le_steps tm N (lift ccN) HN) as [HRN _].
    exact (fscc_find_tr tm A a_enc a_instr succs node_moves_right node_rfuel_ge1
      covers a_enc_inj covers_instr succs_sound
      node_moves_right_sound node_rfuel_ge1_sound Sl q (fst cert) (snd cert)
      Hcl Hlive Hcert (lex_tuple A (fst cert) aN ccN)
      (lexlt_wf_len (length (lex_tuple A (fst cert) aN ccN)) _ eq_refl)
      (S N) aN ccN N N (lexle_refl _) HRN
      (Nat.lt_succ_diag_r N) HInN HcovN HN).
  Qed.
End FuelSCCTarget.

Definition ngram_check_recurrent_phase2tr (tm : TM) (n fuel : nat)
    (l0 l1 r0 r1 : list (list Sym)) (q : Instr)
    (cert : list fmxcomp * list positive) : bool :=
  let ls := phase_sets l0 l1 in
  let rs := phase_sets r0 r1 in
  (1 <=? n) && phase_seed_ok n ls rs &&
  closure_check_recurrent_fuelscctr phaseconf phase_enc phase_instr
    (phase_succs tm ls rs) (phase_moves_right tm) phase_rfuel
    fuel (fw_start n c0, false) q (phase_cert_denote tm n cert).

Theorem ngram_check_recurrent_phase2tr_sound : forall tm n fuel l0 l1 r0 r1 q cert,
  ngram_check_recurrent_phase2tr tm n fuel l0 l1 r0 r1 q cert = true ->
  forall N, exists j, N <= j /\ FiresAt tm q j.
Proof.
  intros tm n fuel l0 l1 r0 r1 q cert H N.
  unfold ngram_check_recurrent_phase2tr in H.
  apply andb_prop in H as [H Hcheck]. apply andb_prop in H as [Hn Hseed].
  apply Nat.leb_le in Hn.
  eapply (closure_check_recurrent_fuelscctr_sound tm phaseconf phase_enc phase_instr
    (phase_succs tm (phase_sets l0 l1) (phase_sets r0 r1))
    (phase_moves_right tm) phase_rfuel
    (phase_covers n (phase_sets l0 l1) (phase_sets r0 r1))); [ | | | | | | | exact Hcheck].
  - exact phase_enc_inj.
  - intros a c Hc. eapply phase_covers_instr; eauto.
  - intros a c Hc. apply phase_succs_sound; assumption.
  - intros a c Hmv Hc. eapply phase_moves_right_sound; eauto.
  - intros a c Hrf Hc. eapply phase_rfuel_sound; eauto.
  - apply phase_seed_sound. exact Hseed.
  - apply Forall_forall. intros comp Hin.
    cbn [phase_cert_denote fst] in Hin.
    apply in_map_iff in Hin. destruct Hin as (c & <- & _).
    apply phase_comp_exact.
Qed.
