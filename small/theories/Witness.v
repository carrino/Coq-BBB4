From Coq Require Import Arith Lia Bool List.
From SmallBB Require Import Statement StatementTr CTape Bounds CycleCensus Mirror ClosureTr.
Import ListNotations.

Definition tr_witness_check tm t p W tg s :=
  (s <? t) &&
  match tc_tail tm t p W, csteps tm s c0 with
  | Some Sl, Some cs =>
    instr_eqb (cinstr cs) tg && negb (tail_instrs Sl tg) &&
    match cstep tm cs with
    | Some cs1 => negb (cfires tm cs1 (t-s-1) tg)
    | None => false
    end
  | _,_ => false
  end.

Theorem tr_witness_sound : forall tm t p W tg s,
  tr_witness_check tm t p W tg s = true -> QuietAfterTr tm tg s.
Proof.
  intros tm t p W tg s H. unfold tr_witness_check in H.
  apply andb_prop in H as [Hst H]. apply Nat.ltb_lt in Hst.
  destruct (tc_tail tm t p W) as [Sl|] eqn:E; [|discriminate].
  destruct (csteps tm s c0) as [cs|] eqn:Es; [|discriminate].
  apply andb_prop in H as [H Hmid]. apply andb_prop in H as [Htg Htail].
  apply instr_eqb_spec in Htg. apply negb_true_iff in Htail.
  destruct (cstep tm cs) as [cs1|] eqn:Es1; [|discriminate].
  apply negb_true_iff in Hmid.
  destruct (tc_tail_sound tm t p W Sl E) as [_ [Hcover _]].
  split.
  - exists (lift cs). split.
    + rewrite <- lift_c0. apply csteps_lift; exact Es.
    + rewrite cinstr_lift. exact Htg.
  - intros n Hsn Hf. destruct (le_lt_dec t n) as [Htn|Hnt].
    + specialize (Hcover n tg Htn Hf). congruence.
    + destruct (fires_computable tm n tg Hf) as (cn & Hcn & Htgn).
      assert (Er : csteps tm (S s) c0 = Some cs1).
      { replace (S s) with (s+1) by lia. rewrite csteps_add,Es,csteps_1. exact Es1. }
      destruct (csteps_prefix tm (S s) n c0 cn ltac:(lia) Hcn) as (cb & Hb & Hbn).
      rewrite Er in Hb. injection Hb as <-.
      assert (Hyes : cfires tm cs1 (t-s-1) tg = true).
      { eapply cfires_complete; [|exact Hbn|exact Htgn]. lia. }
      congruence.
Qed.

Lemma mirror_quiet_tr : forall tm tg s,
  QuietAfterTr (mirror_tm tm) tg s -> QuietAfterTr tm tg s.
Proof.
  intros tm tg s [Hf Hquiet]. split; [apply mirror_fires; exact Hf|].
  intros n Hn Hf'. apply (Hquiet n Hn). apply mirror_fires; exact Hf'.
Qed.

Lemma halt_quiet_state : forall tm s cs,
  csteps tm s c0 = Some cs -> cstep tm cs = None -> QuietAfter tm (fst cs) s.
Proof.
  intros tm s cs Hs Hhalt.
  assert (Hr : stepn tm s InitES = Some (lift cs)).
  { rewrite <- lift_c0. apply csteps_lift; exact Hs. }
  assert (Hh : step tm (lift cs) = None).
  { destruct cs as [q [[l h] r]]. unfold cstep in Hhalt.
    cbn [step lift lift_tape fst snd t_head]. destruct (tm q h); congruence. }
  split; [exists (lift cs); split; [exact Hr|reflexivity]|].
  intros n Hn (c & Hc & _).
  replace n with (s+(1+(n-s-1))) in Hc by lia.
  rewrite stepn_add,Hr in Hc.
  change (match step tm (lift cs) with Some d => stepn tm (n-s-1) d | None => None end = Some c) in Hc.
  rewrite Hh in Hc. discriminate.
Qed.
