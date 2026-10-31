From Coq Require Import Arith Lia Bool List PArith NArith.
From BBB24 Require Import Statement StatementTr CTape PosEnc Closure ClosureTr Bounds.
From BBB24 Require Export Labels.
Import ListNotations.

Section Abstract.
Variable bs bi : N.
Variable tm : TM.
Variable A : Type.
Variable enc : A -> positive.
Variable ai : A -> Instr.
Variable succs : A -> option (list A).
Variable covers : A -> ExecState -> Prop.
Hypothesis enc_inj : forall x y, enc x = enc y -> x = y.
Hypothesis covers_instr : forall a c, covers a c -> ai a = instr_of c.
Hypothesis succs_sound : forall a c, covers a c ->
  match succs a, step tm c with
  | Some l, Some c' => exists a', In a' l /\ covers a' c'
  | Some _, None => False | None, _ => True end.

Theorem abstract_bounds : forall t cc a0 Sl cert,
  csteps tm t c0 = Some cc -> covers a0 (lift cc) ->
  closed_tr_b A enc succs Sl = true -> mem_tr A enc a0 Sl = true ->
  (forall tg, Forall (comp_exact tm A succs covers) (cert tg)) ->
  live_lex_ok_tr A enc ai succs Sl cert = true ->
  prefix_gate bs bi tm t (tail_states (labels ai Sl)) (tail_instrs (labels ai Sl)) = true ->
  NonHalt tm /\ Bounds bs bi tm.
Proof.
  intros t cc a0 Sl cert Et Hcov Hcl Hmem Hex Hlive Hpre.
  assert (HIn : In a0 Sl) by (eapply mem_In_tr; eauto).
  assert (Hstart : stepn tm t InitES = Some (lift cc)).
  { rewrite <- lift_c0. apply csteps_lift; exact Et. }
  assert (Hinv : forall k, exists c a, stepn tm k (lift cc) = Some c /\
      In a Sl /\ covers a c).
  { eapply closure_invariant_tr; eauto. }
  assert (Hrec : forall tg, tail_instrs (labels ai Sl) tg = true -> forall N,
      exists k, N <= k /\ FiresAt tm tg k).
  { intros tg Happ N. rewrite labels_instr in Happ.
    destruct (live_appears_recur_lex_tr tm A enc ai succs covers enc_inj covers_instr succs_sound
      Sl cert a0 cc tg Hcl (Hex tg) Hlive HIn Hcov Happ N)
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
    rewrite labels_instr. apply existsb_exists. exists a. split; [exact Ha|].
    apply instr_eqb_spec. rewrite <- Htg. eapply covers_instr; eauto.
Qed.
End Abstract.
