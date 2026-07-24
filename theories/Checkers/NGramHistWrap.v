(** * NGramHistWrap: history-augmented QHBound (R_QH) tier.

    The state-QH fork of [NGramHist]: for the residue tail that CLOSES but is
    a quasihalter (a state quiet after the transient -- correctly rejected by
    the never-QH gate), prove the census R_QH triple
    [NonHalt /\ QHBound (S t) /\ QuasiHaltsSt] via the halt-redirect machine
    ([Wrap.tm_wrap]) over the HISTORY-augmented closure.

    A fork of [Wrap.ngram_check_qhbound_lex_sound] with the plain n-gram
    instance ([ng_succs]/[ng_covers]) replaced by the augmented one
    ([hng_succs]/[hcovers]); every [Closure.v] liveness lemma is reused
    verbatim.  No new soundness beyond the augmented-alphabet abstraction. *)

From Coq Require Import Arith Lia Bool List ZArith.
From BBB4 Require Import BBB4_Statement CTape PosEnc Closure.
From BBB4.Checkers Require Import Cycle ExactClosure NGram Wrap NGramHist.
Import ListNotations.

Definition ngramhist_check_qhbound_lex (tm : TM) (q : St) (s k n t fuel : nat)
    (lset rset : hgset) (cert : St -> list hcomp) : bool :=
  (1 <=? n) && (s <? t) &&
  match csteps tm t c0, csteps tm s c0, hcsteps tm k t hcconf0 with
  | Some ct, Some cs, Some hct =>
      st_eqb (fst cs) q &&
      (match cstep tm cs with
       | Some cs1 => negb (cvisits tm cs1 (t - s) q)
       | None => false end) &&
      hseed_ok n lset rset hct &&
      match close hcconf hctx_enc (hng_succs (tm_wrap tm q) k n lset rset)
                  fuel [] PositiveSet.empty [hng_start n hct] with
      | Some Sl =>
          closed_b hcconf hctx_enc (hng_succs (tm_wrap tm q) k n lset rset) Sl &&
          mem hcconf hctx_enc (hng_start n hct) Sl &&
          live_lex_ok hcconf hctx_enc ha_state (hng_succs (tm_wrap tm q) k n lset rset) Sl
            (fun q' => map (hcomp_denote (tm_wrap tm q)) (cert q'))
      | None => false
      end
  | _, _, _ => false
  end.

Theorem ngramhist_check_qhbound_lex_sound :
  forall tm q s k n t fuel lset rset cert,
  ngramhist_check_qhbound_lex tm q s k n t fuel lset rset cert = true ->
  NonHalt tm
  /\ (forall q' s', QuietAfter tm q' s' -> S s' <= S t)
  /\ QuasiHaltsSt tm.
Proof.
  intros tm q s k n t fuel lset rset cert H.
  unfold ngramhist_check_qhbound_lex in H.
  apply andb_prop in H as [H Hrest].
  apply andb_prop in H as [Hn Hst].
  apply Nat.leb_le in Hn. apply Nat.ltb_lt in Hst.
  destruct (csteps tm t c0) as [ct|] eqn:Ect; [|discriminate].
  destruct (csteps tm s c0) as [cs|] eqn:Ecs; [|discriminate].
  destruct (hcsteps tm k t hcconf0) as [hct|] eqn:Eht; [|discriminate].
  apply andb_prop in Hrest as [H Hcl].
  apply andb_prop in H as [H Hseed].
  apply andb_prop in H as [Hqs Hnv].
  apply st_eqb_spec in Hqs.
  destruct (cstep tm cs) as [cs1|] eqn:Ecs1; [|discriminate].
  apply negb_true_iff in Hnv.
  set (tmw := tm_wrap tm q) in *.
  destruct (close hcconf hctx_enc (hng_succs tmw k n lset rset)
                  fuel [] PositiveSet.empty [hng_start n hct]) as [Sl|] eqn:Ecl;
    [|discriminate].
  apply andb_prop in Hcl as [Hcl Hlive].
  apply andb_prop in Hcl as [Hclb Hmem].
  apply mem_In in Hmem; [| exact hctx_enc_inj].
  pose proof (hcsteps_proj tm k t hcconf0 hct Eht) as Hpr.
  rewrite hproj_hcconf0 in Hpr. rewrite Ect in Hpr. injection Hpr as Hct_eq.
  assert (Hcov0 : hcovers n lset rset (hng_start n hct) (lift ct)).
  { exists hct. split; [rewrite Hct_eq; reflexivity | apply hng_start_covers; exact Hseed]. }
  set (SS := fun a c Hc => hng_succs_sound tmw k n lset rset a c Hn Hc).
  set (CST := fun a c (Hc : hcovers n lset rset a c) =>
                hcovers_state n lset rset a c Hc).
  assert (Hexd : forall q0,
    Forall (comp_exact tmw hcconf (hng_succs tmw k n lset rset)
              (hcovers n lset rset))
           (map (hcomp_denote tmw) (cert q0))).
  { intros q0. apply Forall_forall. intros comp Hin.
    apply in_map_iff in Hin. destruct Hin as (c & <- & _).
    apply hcomp_denote_comp_exact; exact Hn. }
  assert (Him : forall j, stepn tmw j (lift ct) <> None).
  { intros j HN.
    destruct (closure_invariant tmw hcconf hctx_enc (hng_succs tmw k n lset rset)
                (hcovers n lset rset) hctx_enc_inj SS
                Sl Hclb (hng_start n hct) (lift ct) Hmem Hcov0 j)
      as (c' & a' & Hst' & _ & _). congruence. }
  assert (Ecs1' : csteps tm (s + 1) c0 = Some cs1).
  { rewrite csteps_add, Ecs, csteps_1. exact Ecs1. }
  assert (Hstept : stepn tm t InitES = Some (lift ct)).
  { rewrite <- lift_c0. apply csteps_lift. exact Ect. }
  assert (Hquiet : forall m, s < m -> ~ VisitsAt tm q m).
  { intros m Hm (c & Hc & Hcq).
    destruct (stepn_csteps tm m c) as (cc & Hcc & Hlift); [exact Hc|].
    assert (Hccq : fst cc = q).
    { rewrite <- (lift_state cc), Hlift. exact Hcq. }
    destruct (le_lt_dec m t) as [Hle | Hgt].
    - replace m with ((s + 1) + (m - s - 1)) in Hcc by lia.
      rewrite csteps_add, Ecs1' in Hcc.
      rewrite (cvisits_complete tm (t - s) cs1 q (m - s - 1) cc)
        in Hnv; [discriminate | lia | exact Hcc | exact Hccq].
    - replace m with (t + (m - t)) in Hcc by lia.
      rewrite csteps_add, Ect in Hcc.
      apply csteps_lift in Hcc.
      destruct (wrap_agree tm q (lift ct) Him (m - t)) as [_ Hqfree].
      apply (Hqfree (lift cc)); [exact Hcc|].
      rewrite lift_state. exact Hccq. }
  assert (Hvis : VisitsAt tm q s).
  { exists (lift cs). split.
    - rewrite <- lift_c0. apply csteps_lift. exact Ecs.
    - rewrite lift_state. exact Hqs. }
  assert (HNonHalt : NonHalt tm).
  { intros m HN.
    destruct (le_lt_dec m t) as [Hle | Hgt].
    + destruct (csteps_prefix tm m t c0 ct Hle Ect) as (cm & Hcm & _).
      apply csteps_lift in Hcm. rewrite lift_c0 in Hcm. congruence.
    + replace m with (t + (m - t)) in HN by lia.
      rewrite stepn_add, Hstept in HN.
      destruct (wrap_agree tm q (lift ct) Him (m - t)) as [Heq _].
      rewrite <- Heq in HN.
      exact (Him (m - t) HN). }
  split; [exact HNonHalt | split].
  - intros q'' s'' [Hvis'' Hlast''].
    apply le_n_S.
    destruct (le_lt_dec s'' t) as [Hle | Hgt]; [exact Hle | exfalso].
    destruct Hvis'' as (c & Hc & Hcq).
    destruct (stepn_csteps tm s'' c) as (cc & Hcc & Hlift); [exact Hc|].
    assert (Hccq : fst cc = q'').
    { rewrite <- (lift_state cc), Hlift. exact Hcq. }
    assert (Hcw : stepn tm (s'' - t) (lift ct) = Some (lift cc)).
    { replace s'' with (t + (s'' - t)) in Hc by lia.
      rewrite stepn_add, Hstept in Hc. rewrite Hc, Hlift. reflexivity. }
    assert (Hwrun : stepn tmw (s'' - t) (lift ct) = Some (lift cc)).
    { destruct (wrap_agree tm q (lift ct) Him (s'' - t)) as [Heq _].
      transitivity (stepn tm (s'' - t) (lift ct)); [exact Heq | exact Hcw]. }
    assert (Happ : appears hcconf ha_state Sl q'' = true).
    { rewrite <- Hccq. rewrite <- (lift_state cc).
      apply (live_visited_appears tmw hcconf hctx_enc ha_state
               (hng_succs tmw k n lset rset) (hcovers n lset rset)
               hctx_enc_inj CST SS
               Sl (hng_start n hct) (lift ct) Hclb Hmem Hcov0
               (s'' - t) (lift cc) Hwrun). }
    destruct (live_appears_recur_lex tmw hcconf hctx_enc ha_state
                (hng_succs tmw k n lset rset) (hcovers n lset rset)
                hctx_enc_inj CST SS
                Sl (fun q0 => map (hcomp_denote tmw) (cert q0))
                (hng_start n hct) ct q'' Hclb (Hexd q'') Hlive Hmem Hcov0
                Happ (S s'' - t)) as (kk & c' & Hk & Hstepk & Hqk).
    assert (Hstm : stepn tm kk (lift ct) = Some c').
    { destruct (wrap_agree tm q (lift ct) Him kk) as [Heqk _].
      rewrite <- Heqk. exact Hstepk. }
    apply (Hlast'' (t + kk)); [lia|].
    exists c'. split; [| exact Hqk].
    rewrite stepn_add, Hstept. exact Hstm.
  - eapply quiet_after_qh. split; [exact Hvis | exact Hquiet].
Qed.
