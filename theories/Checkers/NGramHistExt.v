(** * NGramHistExt: the NGramHist never-QH check with one state moved outside.

    [NGramHist.ngramhist_check_neverqh_lex] verbatim, except that the
    liveness gate for a designated state [qext] is lifted and supplied as a
    premise instead ([ClosureExt]).  On the (4,2) counter residue the
    abstraction discharges three states at the cheapest rung and cannot
    discharge the fourth at any rung; [ReachSt] proves that fourth one on the
    machine itself.

    Axiom footprint: none of its own. *)

From Coq Require Import Arith Lia Bool List ZArith.
From BBB4 Require Import BBB4_Statement CTape PosEnc PattCount Closure.
From BBB4.Checkers Require Import Cycle ExactClosure NGram NGramHist ClosureExt.
Import ListNotations.

Definition ngramhist_check_neverqh_lex_ext (tm : TM) (k n t fuel : nat)
    (lset rset : hgset) (cert : St -> list hcomp) (qext : St) : bool :=
  (1 <=? n) &&
  match hcsteps tm k t hcconf0 with
  | Some hct =>
      hseed_ok n lset rset hct &&
      closure_check_neverqh_lex_ext tm hcconf hctx_enc ha_state
        (hng_succs tm k n lset rset) t fuel (hng_start n hct)
        (fun q => map (hcomp_denote tm n) (cert q)) qext
  | None => false
  end.

Theorem ngramhist_check_neverqh_lex_ext_sound :
  forall tm k n t fuel lset rset cert qext,
  (forall N, exists m, N <= m /\ VisitsAt tm qext m) ->
  ngramhist_check_neverqh_lex_ext tm k n t fuel lset rset cert qext = true ->
  NeverQuasiHaltsSt tm.
Proof.
  intros tm k n t fuel lset rset cert qext Hext H.
  unfold ngramhist_check_neverqh_lex_ext in H.
  apply andb_prop in H as [Hn H].
  apply Nat.leb_le in Hn.
  destruct (hcsteps tm k t hcconf0) as [hct|] eqn:Eht; [|discriminate].
  apply andb_prop in H as [Hseed Hcheck].
  apply (closure_check_neverqh_lex_ext_sound tm hcconf hctx_enc ha_state
           (hng_succs tm k n lset rset) (hcovers n lset rset)) in Hcheck;
    [assumption | | | | | | ].
  - exact hctx_enc_inj.
  - intros a c Hc. eapply hcovers_state; eauto.
  - intros a c Hc. apply hng_succs_sound; assumption.
  - intros ct' Hct'.
    pose proof (hcsteps_proj tm k t hcconf0 hct Eht) as Hpr.
    rewrite hproj_hcconf0 in Hpr. rewrite Hct' in Hpr. injection Hpr as Hpr.
    exists hct. split; [rewrite Hpr; reflexivity | apply hng_start_covers; exact Hseed].
  - intros q0. apply Forall_forall. intros comp Hin.
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
  - exact Hext.
Qed.
